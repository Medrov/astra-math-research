'use strict';
const test=require('node:test'),assert=require('node:assert/strict');
const structure=require('../web/structure-search.js'),objects=require('../web/object-graph.js');
function source(){return{id:'a'.repeat(32),status:'ready',source_sha256:'b'.repeat(64),inspection:{status:'complete',success:true},declarations:[{name:'Example.identity',kind:'theorem',type:'∀ n : Nat, n = n',axioms:[]},{name:'Example.map',kind:'def',type:'Nat → Nat'},{name:'Example.assumed',kind:'axiom',type:'False'}]};}
test('A completed inspection must report success and a ready source before model start',()=>{
  const s=source();assert.equal(structure.ready(s),true);
  for(const failed of [{...s,status:'failed'},{...s,inspection:{status:'complete',success:false}},{...s,inspection:{status:'running',success:true}},{...s,inspection:{status:'complete'}}]){
    assert.equal(structure.ready(failed),false);assert.deepEqual(structure.theorems(failed),[]);assert.throws(()=>structure.payload(failed,'Example.identity'));
  }
});
test('Only exported theorems can be selected, not definitions, axioms or invented names',()=>{
  const s=source();assert.deepEqual(structure.theorems(s).map(d=>d.name),['Example.identity']);
  for(const name of ['Example.map','Example.assumed','Foreign.identity',''])assert.throws(()=>structure.payload(s,name));
});
test('Structure search requires an explicit model mode and pins source and target',()=>{
  const s=source(),budget={max_calls:8,timeout_seconds:600};
  assert.throws(()=>structure.payload(s,'Example.identity',{mode:'pilot',budget}));
  const actual=structure.payload(s,'Example.identity',{mode:'multi',budget,question:'  Find the same inverse construction.  '});
  assert.deepEqual(actual,{purpose:'structure',source_id:s.id,target:'Example.identity',mode:'multi',budget,question:'Find the same inverse construction.'});
  assert.equal('case_id' in actual,false);assert.equal('paper_ids' in actual,false);assert.equal('question' in structure.payload(s,'Example.identity',{budget}),false);
});
test('Ranking binds candidates to real saved transitions and never invents missing graphs',()=>{
  const run={object_graph:{transitions:[{id:'later'},{id:'first'},{id:'unranked'}]},structure_routes:[{msc_code:'14R10',candidates:[{transition_id:'later',rank:2},{transition_id:'missing',rank:0},{transition_id:'first',rank:1}]},{msc_code:'20M20',candidates:[{transition_id:'first',rank:1},{transition_id:'unranked'}]}]};
  const before=JSON.stringify(run),ranked=structure.rankedCandidates(run);
  assert.deepEqual(ranked.map(c=>c.transition_id),['first','later','unranked']);assert.equal(ranked[0].transition,run.object_graph.transitions[1]);assert.equal(JSON.stringify(run),before);assert.deepEqual(structure.rankedCandidates({...run,object_graph:null}),[]);
});
test('Ranks are local to an MSC route, even when the next route starts at rank one',()=>{
  const run={object_graph:{transitions:[{id:'a'},{id:'b'},{id:'c'},{id:'d'}]},structure_routes:[
    {id:'route_1',msc_code:'13',candidates:[{transition_id:'a',rank:3},{transition_id:'b',rank:1}]},
    {id:'route_2',msc_code:'14',candidates:[{transition_id:'c',rank:1}]},
    {id:'route_3',msc_code:'37',candidates:[{transition_id:'d',rank:1}]}]};
  const before=JSON.stringify(run),groups=structure.candidateGroups(run);
  assert.deepEqual(groups.map(group=>[group.route.msc_code,group.candidates.map(item=>item.transition_id)]),[['13',['b','a']],['14',['c']],['37',['d']]]);
  assert.deepEqual(structure.rankedCandidates(run).map(item=>item.transition_id),['b','a','c','d']);assert.equal(JSON.stringify(run),before);
});
test('A completed search reports saved candidates independently of its unknown proof outcome',()=>{
  const run={status:'complete',formal_outcome:'unknown',object_graph:{transitions:[{id:'a'},{id:'b'}]},structure_routes:[{candidates:[{transition_id:'a'},{transition_id:'missing'}]},{candidates:[{transition_id:'b'},{transition_id:'a'}]}]};
  assert.equal(structure.searchSummary(run),'Поиск завершён: 2 кандидата');
  assert.equal(structure.searchSummary({...run,object_graph:null}),'Поиск завершён: 0 кандидатов');
  assert.match(structure.searchSummary({...run,status:'running'}),/Поиск идёт/);
  assert.match(structure.searchSummary({...run,status:'cancelled'}),/Поиск не завершён/);
});
test('Candidate badges preserve the graph model certificate and semantic-review distinctions',()=>{
  const proved={status:'proved',formulation_status:'formalized',certificate:{run_id:'verified'},semantic_review:{status:'aligned'}};
  assert.equal(structure.candidateStatus(proved,objects).status,'proved');
  assert.equal(structure.candidateStatus({...proved,certificate:null},objects).status,'incomplete');
  assert.equal(structure.candidateStatus({...proved,semantic_review:{status:'uncertain'}},objects).status,'formal_only');
  assert.equal(structure.candidateStatus({...proved,status:'refuted'},objects).status,'refuted');
  assert.equal(structure.candidateStatus({...proved,formulation_status:'candidate'},objects).status,'incomplete');
  assert.equal(structure.candidateStatus(proved,null).status,'incomplete');
  let received;const newer={statusOf(value){received=value;return {status:'checking',label:'Проверяется'};},presentation(){throw Error('statusOf must have priority');}};
  assert.equal(structure.candidateStatus(proved,newer).status,'checking');assert.equal(received,proved);
  assert.equal(structure.candidateStatus(proved,{statusOf:()=> 'proved',STATUS:objects.STATUS}).label,'Доказано');
});
test('Generated Lean equations are never selected implicitly, including a generated-only source',()=>{
  const s=source(),generated={name:'Example.map.eq_1',kind:'theorem',type:'True'};
  assert.equal(structure.selectedTarget(s),'Example.identity');
  const onlyGenerated={...s,declarations:[generated]};assert.equal(structure.selectedTarget(onlyGenerated),'');
  assert.equal(structure.selectedTarget(onlyGenerated,generated.name),generated.name);
  const mixed={...s,declarations:[generated,...s.declarations]};assert.equal(structure.selectedTarget(mixed),'');assert.equal(structure.selectedTarget(mixed,'stale.name'),'');
  assert.deepEqual(structure.theorems(mixed).map(item=>item.name),['Example.identity','Example.map.eq_1']);
});
test('Math rendering uses the supplied safe renderer and preserves literal text on absence or failure',()=>{
  const content='<img src=x onerror=alert(1)> and $x^2$',node={textContent:''};
  assert.equal(structure.renderMath(node,content),node);assert.equal(node.textContent,content);
  let args;structure.renderMath(node,content,{render(...values){args=values;node.textContent='rendered';}});assert.deepEqual(args,[node,content]);assert.equal(node.textContent,'rendered');
  structure.renderMath(node,content,{render(){node.textContent='partial';throw Error('unavailable');}});assert.equal(node.textContent,content);
});
test('Short summaries leave full model text intact for disclosure',()=>{
  const original='A long mathematical description with a condition. '.repeat(12),before=original;
  const preview=structure.excerpt(original,90);assert.ok(preview.length<=91);assert.match(preview,/…$/);assert.equal(original,before);assert.equal(structure.excerpt('x = y'),'x = y');
});
test('A known source profile uses the exact source summary, while altered sources keep the model profile',()=>{
  const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto'),presentation=require('../web/math-presentation.js');
  const content=fs.readFileSync(path.join(__dirname,'../research_fixtures/Arxiv261038474.lean'),'utf8');
  const declaration={name:'Arxiv261038474.subtract_restore',kind:'theorem',type:'∀ {R : Type u_1} [inst : CommRing R] (b w : Polynomial R), Arxiv261038474.compose (Arxiv261038474.graphSubtract b w) (Arxiv261038474.graphRestore b w) = MvPolynomial.X'};
  const run={purpose:'structure',target:declaration.name,contract:{source_library:{content,source_sha256:crypto.createHash('sha256').update(content).digest('hex'),selected_declaration:declaration}}};
  const profile={objects:['Type u_1','Fin 3'],mechanism:'funext; fin_cases',conclusion_shape:'source goal'},before=JSON.stringify({run,profile});
  const preview=structure.profilePreview(run,profile,presentation);assert.equal(preview.known,true);assert.equal(preview.steps[0][1],'Полиномиальные преобразования F и G');assert.equal(preview.steps[1][1],'Подстановка и обратимость');assert.equal(preview.steps[2][1],presentation.runSummary(run).description);assert.equal(preview.formula.tex,String.raw`F\circ G=\operatorname{id}`);assert.doesNotMatch(JSON.stringify(preview),/Доказано|proved|success/);assert.equal(JSON.stringify({run,profile}),before);
  const changed=JSON.parse(JSON.stringify(run));changed.contract.source_library.source_sha256='0'.repeat(64);
  for(const input of [changed,{...run,target:'Foreign.theorem'},{purpose:'structure'}]){const fallback=structure.profilePreview(input,profile,presentation);assert.equal(fallback.known,false);assert.equal(fallback.steps[1][1],profile.mechanism);assert.equal(fallback.formula,undefined);}
  assert.equal(structure.profilePreview(run,profile,null).known,false);
});
test('Only exact known MSC codes receive Russian direction headings',()=>{
  for(const [code,title]of [['13','Коммутативная алгебра'],['14','Алгебраическая геометрия'],['37','Динамические системы']])assert.equal(structure.routeTitle({msc_code:code,title:'Model title'}),title);
  for(const code of ['14R10','13A05','37C10',' 13','13 ',13,'unknown'])assert.equal(structure.routeTitle({msc_code:code,title:'Original title'}),'Original title');
});
test('A proposed common structure cannot become a proof or an article assertion',()=>{
  const transition={id:'bridge',status:'proposed',formulation_status:'candidate',agent_task:null,obligations:[]};
  const form=objects.formulation(transition);assert.equal(form.formalized,false);assert.equal(form.status,'candidate');assert.match(form.label,/Кандидат общей структуры/);assert.doesNotMatch(form.label,/Утверждение статьи/);assert.equal(form.action,'Формализовать и проверить');
  for(const status of ['proved','refuted'])assert.equal(objects.transitionStatus({...transition,status,certificate:{run_id:'stale'}}),'incomplete');
});
test('An unformalized candidate never displays another transition’s proof nodes',()=>{
  const graph={nodes:[{id:'unrelated',status:'verified'}],edges:[]};
  assert.deepEqual(objects.proofSlice(graph,{formulation_status:'candidate',agent_task:null,obligations:[]}),{nodes:[],edges:[]});
  assert.equal(objects.formulation({formulation_status:'candidate',agent_task:{target:'target',statement:'True'},obligations:[{target:'target'}]}).formalized,false);
});

const descendants=node=>[node,...node.children.flatMap(descendants)];
function withRenderer(check){
  class Element{constructor(tag='div'){this.tagName=tag.toUpperCase();this.attributes={};this.children=[];this.dataset={};this.text='';}append(...children){this.children.push(...children);}replaceChildren(...children){this.children=[];this.text='';this.append(...children);}setAttribute(key,value){this.attributes[key]=String(value);}get textContent(){return this.text+this.children.map(child=>child.textContent).join('');}set textContent(value){this.children=[];this.text=String(value);}}
  const saved={document:global.document,location:global.location,MathPresentation:global.MathPresentation,ObjectGraphModel:global.ObjectGraphModel},nodes=new Map(),node=id=>{if(!nodes.has(id))nodes.set(id,new Element());return nodes.get(id);},rendered=[];
  global.document={createElement:tag=>new Element(tag),getElementById:node};global.location={origin:'http://localhost'};global.ObjectGraphModel=objects;global.MathPresentation={render(element,text){rendered.push(text);element.textContent=text;}};
  try{const workspace=Object.create(structure.Workspace.prototype);workspace.callbacks={};workspace.selected=null;return check(workspace,node,rendered);}finally{for(const[k,v]of Object.entries(saved))if(v===undefined)delete global[k];else global[k]=v;}
}
function articleSearch(){
  const snapshot={kind:'literature_transition',graph_ref:{id:'article',revision:1},transition:{id:'coordinate',title:'Замена координаты',claim:String.raw`При $a>1/2$ замена $t=\phi(s)$ даёт новый оператор.`,construction:'Вводится новая координата.',assumptions:['Сохранено исходное условие.'],source_ids:['profile','radial'],target_ids:['conformal']},objects:[{id:'profile',title:'Радиальный профиль'},{id:'radial',title:'Радиальный оператор'},{id:'conformal',title:'Конформный оператор'}],sources:[{id:'paper',title:'Исходная статья',url:'https://arxiv.org/html/2610.35651v2#S2',text:'Полная выдержка источника.'}],source_sha256:'b'.repeat(64)};
  const transitions=[1,2,3].map(i=>({id:'bridge_'+i,title:'Bridge '+i,formulation_status:'candidate',status:'proposed',agent_task:null,obligations:[],claim:'Original bridge claim '+i,assumptions:['Bridge condition '+i]}));
  return{id:'search',purpose:'structure',status:'complete',outcome:'unknown',contract:{source_transition:snapshot},source_graph_ref:snapshot.graph_ref,source_transition_id:'coordinate',object_graph:{id:'bridges',revision:2,transitions,sources:[{structure_transition:snapshot}]},structure_profile:{status:'model_proposed',summary:'Описание предложения модели',objects:['Оператор','Преобразование'],mechanism:'Сопряжение операторов',conclusion_shape:'Перенос условия'},structure_routes:[1,2,3].map(i=>({id:'route_'+i,msc_code:['13','14','37'][i-1],title:'Area '+i,rationale:'Причина выбора направления '+i,status:'complete',queries:['Exact query '+i],hits:[{title:'Real source '+i,url:'https://example.org/source/'+i,statement:'Full hit excerpt '+i}],candidates:[{transition_id:'bridge_'+i,title:'Bridge '+i,rank:1,evidence:[{title:'Evidence '+i,content:'Complete evidence '+i}]}]}))};
}

test('article search renders the immutable source, direct endpoints and full evidence separately from model proposals',()=>withRenderer((workspace,node,rendered)=>{
  const run=articleSearch(),before=JSON.stringify(run);workspace.render(run,true);const box=node('structure-results'),all=descendants(box);
  assert.match(box.textContent,/Поиск завершён: 3 кандидата/);assert.match(box.textContent,/Исходный переход статьи/);assert.match(box.textContent,/Сам поиск не подтверждает его в Lean/);assert.match(box.textContent,/Предложение модели · требует проверки/);assert.match(box.textContent,/Предложенный структурный паттерн/);
  const origin=all.find(element=>element.attributes.class==='structure-origin');assert.ok(origin);for(const title of ['Радиальный профиль','Радиальный оператор','Конформный оператор'])assert.ok(origin.textContent.includes(title));assert.ok(rendered.includes(run.contract.source_transition.transition.claim));assert.ok(rendered.includes('Сохранено исходное условие.'));assert.ok(origin.textContent.includes('Полная выдержка источника.'));
  assert.equal(all.filter(element=>element.attributes['data-structure-route']).length,3);assert.equal(all.filter(element=>element.attributes['data-structure-candidate']).length,3);
  for(let i=1;i<=3;i++){assert.ok(rendered.includes('Причина выбора направления '+i));assert.ok(rendered.includes('Full hit excerpt '+i));assert.ok(rendered.includes('Complete evidence '+i));}
  const badges=all.filter(element=>element.attributes.class==='structure-candidate-status');assert.ok(badges.every(element=>element.attributes['data-status']==='hypothesis'));assert.equal(JSON.stringify(run),before);
}));

test('bridge buttons preserve exact candidate payloads and open prior attempts without recolouring source candidates',()=>withRenderer((workspace,node)=>{
  const run=articleSearch(),verifications=[],selections=[],opened=[],history=[];workspace.callbacks={onVerify:(...args)=>verifications.push(args),onSelect:t=>selections.push(t),onOpenRun:id=>opened.push(id),getRuns:()=>history};workspace.render(run,true);
  const card=()=>descendants(node('structure-results')).find(element=>element.attributes['data-structure-candidate']==='bridge_1'),button=title=>descendants(card()).find(element=>element.tagName==='BUTTON'&&element.textContent===title);
  assert.equal(verifications.length,0);button('Показать на карте').onclick();assert.deepEqual(selections,[run.object_graph.transitions[0]]);assert.equal(verifications.length,0);
  button('Проверить общую структуру в Lean').onclick();assert.deepEqual(verifications,[[run.object_graph,run.object_graph.transitions[0]]]);
  history.push({id:'prior',purpose:'prove',status:'failed',source_graph_ref:{id:'bridges',revision:2},selected_transition_id:'bridge_1'});workspace.render(run,true);button('Открыть попытку').onclick();assert.deepEqual(opened,['prior']);assert.equal(verifications.length,1);assert.equal(run.object_graph.transitions[0].status,'proposed');assert.equal(run.object_graph.transitions[0].certificate,undefined);
  history[0].source_graph_ref.revision=1;workspace.render(run,true);assert.ok(button('Проверить общую структуру в Lean'));
}));

test('failed or partial article searches retain honest diagnostics, completed routes and disabled active proof buttons',()=>withRenderer((workspace,node)=>{
  const run=articleSearch();run.status='failed';run.error='Исчерпан лимит источника';run.structure_routes[2].status='failed';run.structure_routes[2].candidates=[];workspace.render(run,true);
  assert.match(node('structure-results').textContent,/Поиск не завершён · сохранено кандидатов: 2/);assert.match(node('structure-results').textContent,/Поиск остановлен: Исчерпан лимит источника/);assert.match(node('structure-results').textContent,/Full hit excerpt 1/);
  run.status='running';workspace.callbacks.onVerify=()=>{throw Error('Must not run automatically');};workspace.render(run,true);const actions=descendants(node('structure-results')).filter(element=>element.tagName==='BUTTON'&&element.textContent==='Проверить общую структуру в Lean');assert.equal(actions.length,2);assert.ok(actions.every(button=>button.disabled));
}));

test('opening an article search invalidates a pending Lean-source restore and requires no new source request',async()=>{
  const workspace=Object.create(structure.Workspace.prototype),target={value:'old-target'},requests=[];let resolve;
  Object.assign(workspace,{token:0,busy:false,source:null,sources:[],callbacks:{api:path=>{requests.push(path);return new Promise(done=>{resolve=done;});}},$:()=>target,renderSource(){},renderTarget(){},renderPicker(){},changed(){},notice(message){this.message=message;}});
  const stale=workspace.restore({source_id:'old-source',target:'Old.theorem'});assert.equal(workspace.busy,true);await workspace.restore(articleSearch());assert.equal(workspace.source,null);assert.equal(workspace.busy,false);assert.equal(target.value,'');assert.match(workspace.message,/Lean-файл для поиска аналогов не требуется/);
  resolve({source:{...source(),id:'old-source'}});await stale;assert.equal(workspace.source,null);assert.equal(target.value,'');assert.deepEqual(requests,['/api/structure/sources/old-source']);
});

test('pinned article context is rendered on the first queued response before any profile, route or graph',()=>withRenderer((workspace,node)=>{
  const run=articleSearch();run.status='queued';run.structure_profile=null;run.structure_routes=null;run.object_graph=null;workspace.callbacks.api=()=>{throw Error('Initial context must not need source restoration');};workspace.render(run,true);
  const box=node('structure-results'),origin=descendants(box).find(element=>element.attributes.class==='structure-origin');assert.ok(origin);assert.match(origin.textContent,/Замена координаты/);assert.ok(origin.textContent.includes(run.contract.source_transition.transition.claim));assert.match(box.textContent,/Astra составляет структурный профиль исходного перехода/);assert.equal(descendants(box).filter(element=>element.attributes['data-structure-route']).length,3);assert.equal(descendants(box).filter(element=>element.attributes['data-structure-candidate']).length,0);
}));
