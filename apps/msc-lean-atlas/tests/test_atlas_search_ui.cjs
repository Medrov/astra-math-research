'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),vm=require('node:vm');
const atlas=require('../web/atlas-search.js'),guided=require('../web/guided-research.js'),workspace=require('../web/research-workspace.js'),history=require('../web/research-history.js'),structure=require('../web/structure-search.js');
class Element{
  constructor(tag='div',doc){this.tagName=tag.toUpperCase();this.doc=doc;this.children=[];this.dataset={};this.attributes={};this.text='';this.classList={toggle(){},add(){},remove(){}};}
  append(...nodes){for(const node of nodes){node.parent=this;this.children.push(node);}}replaceChildren(...nodes){this.children=[];this.text='';this.append(...nodes);}setAttribute(key,value){this.attributes[key]=String(value);if(key==='id')this.doc?.nodes.set(String(value),this);}removeAttribute(key){delete this.attributes[key];}
  set textContent(value){this.text=String(value);this.children=[];}get textContent(){return this.text+this.children.map(node=>node.textContent).join('');}focus(){if(this.doc)this.doc.activeElement=this;}showModal(){this.open=true;}close(){this.open=false;this.onclose?.();}remove(){if(this.parent)this.parent.children=this.parent.children.filter(node=>node!==this);}scrollIntoView(){}
}
const all=node=>[node,...node.children.flatMap(all)],clone=value=>JSON.parse(JSON.stringify(value)),flush=async()=>{for(let i=0;i<6;i++)await Promise.resolve();};
function dom(){const doc={nodes:new Map(),createElement(tag){return new Element(tag,doc);},getElementById(id){if(!doc.nodes.has(id))doc.nodes.set(id,new Element('div',doc));return doc.nodes.get(id);},querySelectorAll(){return [];}};doc.body=doc.createElement('body');return doc;}
const digest='a'.repeat(64),run=(fields={})=>({id:'atlas-run',purpose:'structure',search_scope:'atlas',status:'complete',updated_at:'same',budget:{max_calls:8,timeout_seconds:600},atlas_summary:{snapshot_sha256:digest,progress_sha256:'p1',total_codes:6603,considered_codes:6603,queried_codes:6000,query_count:6001,corpus_gaps:3000,deep_completed:2,deep_pending:1,candidates_found:2,proof_verified:0,screening_complete:true,deep_complete:false},...fields});
function overview(id='atlas-run'){
  const base={screen_status:'considered',query_status:'executed',corpus_status:'unknown',deep_status:'not_scheduled',source_count:0,candidate_count:0,route_ids:[]};
  const roots=Array.from({length:63},(_,i)=>({...base,code:String(i).padStart(2,'0'),title:'Root '+i,parent_code:null,level:0}));
  const leaves=Array.from({length:6540},(_,i)=>({...base,code:'L'+i,title:'Leaf '+i,parent_code:roots[i%63].code,level:2}));
  return {schema_version:1,run_id:id,snapshot_sha256:digest,progress_sha256:'p1',summary:run().atlas_summary,nodes:[...roots,...leaves],queue:[{id:'q1',code:'00',status:'complete',reason:'Mechanism match'}],source_links:[{code:'00',source_id:'paper',provenance_kind:'source_reported',evidence:'MSC 00'}],global_channel:{status:'queried',source_count:3},limitations:['A bounded corpus, not all mathematical literature.']};
}
test('coverage keeps independent counts and never inherits a root search status into a leaf',()=>{
  const data=overview(),index=atlas.indexOf(data);assert.equal(index.nodes.length,6603);assert.equal(atlas.pageOf(index).items.length,63);
  const leaf=index.byCode.get('L0');leaf.query_status='not_started';assert.equal(atlas.pageOf(index,{parent:'00'}).items[0].query_status,'not_started');
  assert.equal(atlas.pageOf(index,{query:'Leaf',limit:10000}).items.length,80);assert.equal(atlas.metrics({})[0].value,null);assert.equal(atlas.metrics(data.summary).find(m=>m.key==='query_count').value,6001);
  assert.deepEqual(atlas.ancestors(index,'L0').map(n=>n.code),['00','L0']);assert.equal(atlas.enabled({purpose:'structure'}),false);
});
test('6603-record explorer renders roots or 80 search results, safely, with Escape and drill navigation',async()=>{
  const doc=dom(),box=doc.createElement('section'),data=overview(),requests=[];data.nodes[0].title='<img src=x onerror=attack()>';
  const view=new atlas.Workspace({document:doc,container:box,api:async path=>{requests.push(path);return data;}});view.render(run());await flush();
  const cards=()=>all(box).filter(n=>n.attributes.class==='atlas-code-card');assert.equal(cards().length,63);assert.equal(all(box).filter(n=>n.tagName==='IMG').length,0);assert.match(box.textContent,/Учтённый код MSC не означает/);assert.match(box.textContent,/Доказательств в этом поиске0/);assert.match(box.textContent,/неклассифицированные/);
  cards()[0].children[0].onclick();assert.equal(cards().length,80);assert.match(box.textContent,/MSC указан источником/);assert.match(box.textContent,/родительской области не переносится/);
  const input=doc.getElementById('atlas-code-search');input.value='Leaf';input.oninput();assert.equal(cards().length,80);let prevented=false;input.onkeydown({key:'Escape',preventDefault(){prevented=true;}});assert.equal(input.value,'');assert.ok(prevented);
  all(box).find(n=>n.tagName==='BUTTON'&&n.textContent==='Все корневые области').onclick();assert.equal(cards().length,63);assert.deepEqual(requests,['/api/research/runs/atlas-run/atlas']);
});
test('stale coverage response cannot overwrite a new run and failed load is explicit rather than zero coverage',async()=>{
  const doc=dom(),box=doc.createElement('section');let resolveOld;const old=new Promise(resolve=>{resolveOld=resolve;});
  const view=new atlas.Workspace({document:doc,container:box,api:path=>path.includes('atlas-run')?old:Promise.resolve(overview('new'))});view.render(run());view.render(run({id:'new'}));await flush();resolveOld(overview());await flush();assert.equal(view.data.run_id,'new');
  const errorView=new atlas.Workspace({document:doc,container:doc.createElement('section'),api:async()=>{throw Error('network failed');}});errorView.render(run({atlas_snapshot_sha256:digest,atlas_summary:{}}));await flush();assert.match(errorView.container.textContent,/Не удалось загрузить покрытие/);assert.match(errorView.container.textContent,/Кодов учтено при обзоре—/);
});

test('atlas waits for a saved pin and terminal absence stays honest without an early GET or retry control',async()=>{
  for(const status of ['running','complete','failed','cancelled','budget_exhausted']){const doc=dom(),box=doc.createElement('section'),requests=[],view=new atlas.Workspace({document:doc,container:box,api:async path=>{requests.push(path);return overview();},onContinue(){assert.fail('No snapshot to continue');}}),early=run({status,phase:'structure_routes',atlas_summary:null});
    view.render(early);await flush();assert.equal(requests.length,0);assert.match(box.textContent,status==='running'?/Подготавливаем первичный обзор атласа/:/Первичный обзор атласа не успел сохраниться/);assert.doesNotMatch(box.textContent,/Не удалось загрузить|snapshot\.json|FileNotFound|Продолжить поиск/);
    view.render({...early,atlas_snapshot_sha256:digest});await flush();assert.equal(requests.length,1);assert.equal(view.data.run_id,early.id);assert.match(box.textContent,/Кодов учтено при обзоре/);
  }
});
test('global queue and active depth use current backend statuses without a null MSC label',async()=>{
  const doc=dom(),box=doc.createElement('section'),data=overview();data.nodes[0].deep_status='active';data.queue=[{id:'global',code:null,status:'active',reason:'Global corpus'}];
  const view=new atlas.Workspace({document:doc,container:box,api:async()=>data});view.render(run());await flush();
  assert.match(box.textContent,/Без привязки к MSC · Выполняется/);assert.doesNotMatch(box.textContent,/null ·/);
  assert.match(box.textContent,/Поиск по корпусу без привязки к MSC: выполнен/);
  all(box).find(n=>n.attributes.class==='atlas-code-card').children[0].onclick();assert.match(box.textContent,/Углублённый поиск выполняется/);
  data.global_channel.status='partial';view.draw();assert.match(box.textContent,/Поиск по корпусу без привязки к MSC: частичный/);
});

test('continuation overview labels inherited totals and opens its actual parent without merging candidate maps',async()=>{
  const doc=dom(),box=doc.createElement('section'),data=overview(),opened=[],requests=[],parent='36a2b4e8023d46f19340bcab568603ed',view=new atlas.Workspace({document:doc,container:box,api:async path=>{requests.push(path);return data;},onOpenRun:id=>opened.push(id)});
  view.render(run({status:'cancelled',contract:{atlas_seed:{parent_run_id:parent}},structure_routes:[{status:'pending',candidates:[]}]}));await flush();assert.match(box.textContent,/Счётчики покрытия включают предыдущие попытки/);assert.match(box.textContent,/Карта этой попытки не объединяет их автоматически/);const button=all(box).find(n=>n.tagName==='BUTTON'&&n.textContent==='Кандидаты предыдущей попытки');assert.ok(button);button.onclick();assert.deepEqual(opened,[parent]);assert.equal(requests.length,1);
  view.render(run({id:'ordinary'}));await flush();assert.doesNotMatch(box.textContent,/Счётчики покрытия включают предыдущие попытки/);
});
function dialogView(){const doc=dom(),previous=global.document;global.document=doc;const view=Object.create(guided.Workspace.prototype);view.prose=(text,tag='p')=>view.el(tag,{},text);view.backends=[{id:'native',title:'Native',available:true}];const calls=[],opened=[];view.cb={api:async(path,body)=>{calls.push({path,body});return {run:{id:'new-draft',status:'draft'}};}};view.openRun=async id=>opened.push(id);return {doc,view,calls,opened,restore:()=>{global.document=previous;}};}

test('compact source links are explicitly examples and never imply all corpus matches were displayed',async()=>{
  const doc=dom(),box=doc.createElement('section'),data=overview();data.source_links_scope='One retained example per code; all shortlisted links are in the immutable snapshot.';data.source_links_total=400;data.nodes[0].source_count=20;
  const view=new atlas.Workspace({document:doc,container:box,api:async()=>data});view.render(run());await flush();all(box).find(n=>n.attributes.class==='atlas-code-card').children[0].onclick();
  assert.match(box.textContent,/Пример связи источника с областью/);assert.match(box.textContent,/один сохранённый пример на код MSC/);assert.match(box.textContent,/Полный список.*неизменном снимке/);assert.match(box.textContent,/Совпадений в корпусе: 20/);assert.doesNotMatch(box.textContent,/Связь источников с этой областью · 1/);
});

test('corpus matches, retained shortlist and hierarchy counts stay separate, with honest absent metadata',async()=>{
  const doc=dom(),box=doc.createElement('section'),data=overview();data.summary.level_counts={roots:63,groups:534,leaves:6006};data.global_channel.source_count=1200;data.global_channel.retained_count=12;data.nodes[0].source_count=80;
  const view=new atlas.Workspace({document:doc,container:box,api:async()=>data});view.render(run());await flush();all(box).find(n=>n.attributes.class==='atlas-code-card').children[0].onclick();
  assert.match(box.textContent,/Корневых областей: 63 · групп: 534 · листовых кодов: 6006/);assert.match(box.textContent,/Совпадений в корпусе: 1200 · Отобрано для углубления: 12/);assert.match(box.textContent,/Совпадений в корпусе: 80/);assert.doesNotMatch(box.textContent,/источников сохранено|Сохранённых источников/);
  delete data.global_channel.retained_count;delete data.summary.level_counts;view.draw();assert.doesNotMatch(box.textContent,/Отобрано для углубления|Корневых областей:/);
  data.global_channel.retained_count=0;data.summary.level_counts={roots:63};view.draw();assert.match(box.textContent,/Отобрано для углубления: 0/);assert.match(box.textContent,/Корневых областей: 63 · групп: — · листовых кодов: —/);
});

test('MSC details expose the actual pool cutoff without deriving missing counts or substituting zero',async()=>{
  const doc=dom(),box=doc.createElement('section'),data=overview();Object.assign(data.nodes[0],{source_count:42,retained_count:6,pool_truncated:36});
  const view=new atlas.Workspace({document:doc,container:box,api:async()=>data});view.render(run());await flush();all(box).find(n=>n.attributes.class==='atlas-code-card').children[0].onclick();const detail=()=>all(box).find(n=>n.attributes.class==='atlas-code-detail').textContent;
  assert.match(detail(),/Совпадений в корпусе: 42/);assert.match(detail(),/Отобрано для углубления: 6 · За пределами пула: 36/);
  delete data.nodes[0].pool_truncated;view.draw();assert.match(detail(),/Отобрано для углубления: 6 · За пределами пула: —/);assert.doesNotMatch(detail(),/За пределами пула: 36/);
  delete data.nodes[0].retained_count;view.draw();assert.doesNotMatch(detail(),/Отобрано для углубления|За пределами пула/);
  Object.assign(data.nodes[0],{retained_count:0,pool_truncated:42});view.draw();assert.match(detail(),/Отобрано для углубления: 0 · За пределами пула: 42/);
});

function sourceGraph(){return {id:'739f04950bbd47b7b98353a031236383',revision:1,sources:[{url:'https://arxiv.org/html/2409.02933v1#S2'}],objects:[{id:'a'},{id:'b'}],transitions:[{id:'quartic_step',title:'Исключение смешанного произведения',source_ids:['a'],target_ids:['b'],formulation_status:'literature_only',agent_task:null,obligations:[]}]};}
test('primary atlas search confirms an explicit budget, pins the chosen transition and blocks duplicate submits',async()=>{
  const h=dialogView();try{const graph=sourceGraph(),starts=[];let release;h.view.backend='goedel-adapted';h.view.setBusy=function(value){this.busy=value;};h.view.cb.start=payload=>{starts.push(payload);return new Promise(resolve=>{release=resolve;});};h.view.cb.error=message=>assert.fail(message);
    await h.view.searchAnalogies(graph,graph.transitions[0]);assert.equal(starts.length,0);assert.equal(h.calls.length,0);const dialog=h.view.searchDialog,form=all(dialog).find(n=>n.tagName==='FORM');assert.equal(h.doc.getElementById('atlas-search-calls').value,'8');assert.equal(h.doc.getElementById('atlas-search-minutes').value,'10');
    await h.view.searchAnalogies(graph,graph.transitions[0]);assert.equal(h.view.searchDialog,dialog);h.doc.getElementById('atlas-search-calls').value='20';h.doc.getElementById('atlas-search-minutes').value='30';const pending=form.onsubmit({preventDefault(){}});await form.onsubmit({preventDefault(){}});assert.equal(starts.length,1);assert.equal(h.view.busy,true);let prevented=false;dialog.oncancel({preventDefault(){prevented=true;}});assert.equal(prevented,true);
    assert.deepEqual(starts[0],{purpose:'structure',search_scope:'atlas',mode:'multi',graph_id:graph.id,graph_revision:1,transition_id:'quartic_step',budget:{max_calls:20,timeout_seconds:1800,max_parallel:2},proof_backend:'goedel-adapted'});release();await pending;assert.equal(h.view.searchDialog,null);assert.equal(h.view.busy,false);
  }finally{h.restore();}
});
test('primary atlas dialog preserves provided limits, validates inputs and cancels without a request',async()=>{
  const h=dialogView();try{const graph=sourceGraph(),starts=[];h.view.setBusy=function(value){this.busy=value;};h.view.cb.start=async payload=>starts.push(payload);h.view.cb.error=message=>assert.fail(message);
    await h.view.searchAnalogies(graph,graph.transitions[0],{max_calls:12,timeout_seconds:900});assert.equal(h.doc.getElementById('atlas-search-calls').value,'12');assert.equal(h.doc.getElementById('atlas-search-minutes').value,'15');const form=all(h.view.searchDialog).find(n=>n.tagName==='FORM');h.doc.getElementById('atlas-search-calls').value='25';await form.onsubmit({preventDefault(){}});assert.equal(starts.length,0);assert.match(h.view.searchDialog.textContent,/от 1 до 24/);all(h.view.searchDialog).find(n=>n.tagName==='BUTTON'&&n.textContent==='Отмена').onclick();assert.equal(h.view.searchDialog,null);assert.equal(starts.length,0);assert.equal(h.calls.length,0);
  }finally{h.restore();}
});
test('atlas continuation saves a bounded idempotent draft and never starts research',async()=>{
  const h=dialogView();try{h.view.openAtlasContinuation(run(),overview());const form=all(h.view.continueDialog).find(n=>n.tagName==='FORM');await form.onsubmit({preventDefault(){}});
    assert.equal(h.calls.length,1);assert.equal(h.calls[0].path,'/api/research/runs/atlas-run/atlas-continue');assert.deepEqual(h.calls[0].body.budget,{max_calls:8,timeout_seconds:600});assert.equal(h.calls[0].body.expected_snapshot_sha256,digest);assert.ok(h.calls[0].body.idempotency_key);assert.deepEqual(h.opened,['new-draft']);assert.ok(workspace.stages(run({status:'draft'})).every(s=>s.state==='pending'));
  }finally{h.restore();}
});
test('continuation validates budget and reuses request identity after a transport error',async()=>{
  const h=dialogView();try{h.view.cb.api=async(path,body)=>{h.calls.push({path,body});throw Error('Conflict; reload coverage');};h.view.openAtlasContinuation(run(),overview());const form=all(h.view.continueDialog).find(n=>n.tagName==='FORM');h.doc.getElementById('atlas-continue-calls').value='100';await form.onsubmit({preventDefault(){}});assert.equal(h.calls.length,0);h.doc.getElementById('atlas-continue-calls').value='8';await form.onsubmit({preventDefault(){}});h.doc.getElementById('atlas-continue-calls').value='12';await form.onsubmit({preventDefault(){}});assert.equal(h.calls[0].body.idempotency_key,h.calls[1].body.idempotency_key);assert.equal(h.calls[1].body.budget.max_calls,8);assert.equal(h.opened.length,0);assert.match(h.view.continueDialog.textContent,/Conflict/);h.view.continueDialog.close();h.view.openAtlasContinuation(run(),overview());assert.equal(h.doc.getElementById('atlas-continue-calls').value,'8');await all(h.view.continueDialog).find(n=>n.tagName==='FORM').onsubmit({preventDefault(){}});assert.deepEqual(h.calls[2].body,h.calls[0].body);
  }finally{h.restore();}
});
test('failed directions require an explicit retry selection, while an exhausted successful queue offers no continuation',async()=>{
  const h=dialogView();try{const data=overview();data.summary={...data.summary,local_queries_complete:true,deep_pending:0,deep_failed:1};h.view.openAtlasContinuation(run(),data);const nodes=all(h.view.continueDialog),form=nodes.find(n=>n.tagName==='FORM'),check=nodes.find(n=>n.attributes.type==='checkbox'),submit=nodes.find(n=>n.attributes.type==='submit');assert.equal(check.checked,false);assert.equal(submit.disabled,true);await form.onsubmit({preventDefault(){}});assert.equal(h.calls.length,0);check.checked=true;check.onchange();assert.equal(submit.disabled,false);await form.onsubmit({preventDefault(){}});assert.equal(h.calls[0].body.retry_failed,true);
    const box=h.doc.createElement('section');data.summary.deep_failed=0;const view=new atlas.Workspace({document:h.doc,container:box,api:async()=>data,onContinue(){throw Error('No pending work');}});view.render(run({atlas_summary:data.summary}));await flush();assert.match(box.textContent,/незавершённых направлений.*нет/);assert.equal(all(box).some(n=>n.textContent==='Продолжить поиск в новой попытке'),false);
  }finally{h.restore();}
});
test('coverage polling preserves a focused query and explicit duplicate candidates are counted once',async()=>{
  const doc=dom(),box=doc.createElement('section'),data=overview(),view=new atlas.Workspace({document:doc,container:box,api:async()=>data});view.render(run());await flush();const input=doc.getElementById('atlas-code-search');input.focus();input.value='Leaf 123';input.oninput();view.render(run({atlas_summary:{...run().atlas_summary,progress_sha256:'p2'}}));await flush();assert.equal(doc.activeElement,doc.getElementById('atlas-code-search'));assert.equal(doc.activeElement.value,'Leaf 123');
  const original={object_graph:{transitions:[{id:'canonical'}]},structure_routes:[{candidates:[{transition_id:'copy',duplicate_of:'canonical',canonical_transition_id:'canonical'}]},{candidates:[{transition_id:'canonical',rank:1}]}]};assert.deepEqual(structure.rankedCandidates(original).map(c=>c.transition_id),['canonical']);
});
test('accepted revision preserves its server-confirmed formalization unless the user changes math or opts out',async()=>{
  for(const change of ['none','title','claim','optout']){const h=dialogView();try{const source={...run(),purpose:'prove',source_card:{editable:true,title:'Bridge',conclusion:'A = B',assumptions:['Ring R']},revision_options:{can_preserve_formalization:true,default_preserve_formalization:true,reason:'Saved typed draft'}};h.view.openRevision(source);const nodes=all(h.view.revisionDialog),form=nodes.find(n=>n.tagName==='FORM'),texts=nodes.filter(n=>n.tagName==='TEXTAREA'),check=nodes.find(n=>n.attributes.type==='checkbox');assert.equal(check.checked,true);texts[0].value='Continue proof';if(change==='claim'){texts[1].value='A = C';texts[1].oninput();assert.equal(check.disabled,true);}if(change==='title')nodes.find(n=>n.tagName==='INPUT'&&n.attributes.type==='text').value='New title';if(change==='optout'){check.checked=false;check.onchange();}await form.onsubmit({preventDefault(){}});assert.equal(h.calls[0].body.preserve_formalization,['none','title'].includes(change));assert.deepEqual(h.opened,['new-draft']);}finally{h.restore();}}
});
test('terminal proof attempts and partial obligations remain visible without certifying the full contract',()=>{
  const value={id:'proof',purpose:'prove',status:'failed',phase:'failed',active_stage:'investigate',termination:{code:'invalid_contract',stage:'verify',message:'adapter failure'},formal_contract:{target:'goal'},contract_verification:{kind:'lean_contract_preflight',target:'goal',well_typed:true,proof_checked:false,status:'complete',audit:{status:'passed'}},contract_review:{status:'aligned'},attempts:[{role:'prove',status:'completed'}],nodes:[{id:'lemma',status:'pending'}],proof_progress:{started:true,obligations_total:3,proved:1,failed:1,pending:1},outcome_summary:{category:'infrastructure',title:'Сбой проверки доказательства',stage:'verify',technical_failure:true,reason:'Adapter audit stopped'}};
  assert.equal(guided.verdict(value).title,'Сбой проверки доказательства');assert.equal(guided.formalEvidence(value),false);assert.deepEqual(workspace.stages(value).map(s=>s.state),['complete','complete','complete','partial','pending','pending']);
  const legacy={...value,proof_progress:undefined,outcome_summary:undefined};assert.equal(guided.proofProgress(legacy).started,true);assert.doesNotMatch(guided.verdict(legacy).title,/постановка отклонена/i);assert.equal(workspace.stages(legacy)[3].state,'stopped');
  for(const category of ['no_source','no_supported_candidate','unsupported_conditions','proof_budget_exhausted','invalid_formalization','infrastructure'])assert.equal(guided.terminationInfo({...value,outcome_summary:{category,title:category,reason:'exact reason'}}).code,category);
  assert.equal(guided.terminationInfo({purpose:'prove',status:'complete',outcome_summary:{category:'proved',title:'Verified'}}),null);
  assert.equal(history.statusOf({...run(),outcome_summary:{category:'candidates_found',title:'Найдены кандидаты: 2'}}).kind,'search');
  assert.equal(history.statusOf({status:'complete',purpose:'prove',outcome:'proved',outcome_summary:{category:'proved',title:'Verified'}}).kind,'result');
});
test('real browser export and guided parent mount coverage without starting research',async()=>{
  const doc=dom(),context={document:doc,URL,location:{href:'http://localhost/?step=connections'}};context.window=context;vm.createContext(context);
  for(const file of ['research-workspace.js','atlas-search.js','guided-research.js'])vm.runInContext(fs.readFileSync(require.resolve('../web/'+file),'utf8'),context,{filename:file});const calls=[];
  const view=new context.GuidedResearch.Workspace({api:async path=>{calls.push(path);if(path==='/api/research/backends')return {default:'native',backends:[]};return overview();},action(){throw Error('Unexpected action');},start(){throw Error('Unexpected research');}});await flush();view.render({run:run(),runs:[]});await flush();assert.equal(doc.getElementById('guided-atlas').hidden,false);assert.equal(all(doc.getElementById('guided-atlas')).filter(n=>n.attributes.class==='atlas-code-card').length,63);assert.deepEqual(calls,['/api/research/backends','/api/research/runs/atlas-run/atlas']);
});

test('actual guided parent updates atlas preparation to search counters without proof text or updated_at changes',async()=>{
  const doc=dom(),context={document:doc,URL,location:{href:'http://localhost/?step=connections'}};context.window=context;vm.createContext(context);
  for(const file of ['research-workspace.js','atlas-search.js','guided-research.js'])vm.runInContext(fs.readFileSync(require.resolve('../web/'+file),'utf8'),context,{filename:file});const calls=[];
  const view=new context.GuidedResearch.Workspace({api:async path=>{calls.push(path);if(path==='/api/research/backends')return {default:'native',backends:[]};return overview();},action(){throw Error('Unexpected action');},start(){throw Error('Unexpected research');}});await flush();
  const early=run({status:'running',phase:'structure_routes',active_stage:'structure_profile',atlas_summary:null,proof_progress:{started:false,obligations_total:0,proved:0},events:[{phase:'structure_routes',message:'Astra выполняет задачу: structure_routes.'}],attempts:[{role:'structure_routes',status:'completed'}]});view.render({run:early,runs:[]});await flush();
  const display=()=>doc.getElementById('guided-progress').textContent;assert.match(display(),/Подготавливаем первичный обзор атласа/);assert.doesNotMatch(display(),/Проверено обязательств|полной сборки|structure_routes|Astra выполняет задачу/);assert.match(display(),/Проверка выбранного кандидата в Lean запускается отдельно/);assert.deepEqual(calls,['/api/research/backends']);
  view.render({run:{...early,atlas_snapshot_sha256:digest,atlas_summary:{snapshot_sha256:digest,progress_sha256:'p1',considered_codes:6603,query_count:7,deep_completed:1,candidates_found:2}},runs:[]});await flush();assert.equal(calls.length,2);assert.match(display(),/Кодов учтено при обзоре: 6603/);assert.match(display(),/Поисковых запросов выполнено: 7/);assert.match(display(),/Кандидатов найдено: 2/);assert.doesNotMatch(display(),/Проверено обязательств|Подготавливаем первичный обзор|structure_routes/);
});
