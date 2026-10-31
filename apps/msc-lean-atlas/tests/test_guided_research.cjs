const {test}=require('node:test');
const assert=require('node:assert/strict');
const m=require('../web/guided-research.js');
const ready={id:'s',status:'ready',inspection:{status:'complete',success:true},declarations:[{kind:'theorem',name:'Input.main'},{kind:'theorem',name:'Input.main.eq_1'},{kind:'def',name:'Input.def'}]};
const verified={purpose:'prove',status:'complete',outcome:'proved',result:{verification:{success:true,target_preserved:true,obligations_passed:true,audit:{status:'passed'}},semantic_review:{status:'aligned'}}};
test('successful search never inherits a proof status',()=>{
  const r={...verified,purpose:'structure',object_graph:{transitions:[{id:'a'},{id:'b'}]}};
  assert.deepEqual(m.verdict(r),{kind:'search',title:'Поиск завершён',count:2});
});
test('missing full audit or obligations prevents green result',()=>{
  for(const change of [{obligations_passed:false},{target_preserved:false},{audit:{status:'failed'}},{success:false}]){
    const r=structuredClone(verified);Object.assign(r.result.verification,change);assert.notEqual(m.verdict(r).kind,'proved');
  }
});
test('semantic mismatch stays formal only despite successful Lean',()=>{
  const r=structuredClone(verified);r.result.semantic_review.status='mismatch';assert.equal(m.verdict(r).kind,'formal_only');
  assert.equal(m.verdict(verified).kind,'proved');
});
test('old success cannot hide active recheck',()=>assert.equal(m.verdict({...verified,status:'running'}).kind,'running'));
test('old success cannot hide a failed run',()=>assert.equal(m.verdict({...verified,status:'failed'}).kind,'incomplete'));

test('a successful report of another target never certifies the selected contract',()=>{
  const run=structuredClone(verified);run.formal_contract={target:'Selected.theorem'};
  run.result.verification.target='Other.theorem';
  assert.equal(m.verdict(run).kind,'incomplete');
  run.result.verification.target='Selected.theorem';assert.equal(m.verdict(run).kind,'proved');
});
test('a checked counterexample is distinct from a semantic mismatch',()=>{
  const r=structuredClone(verified);r.outcome='refuted';assert.equal(m.verdict(r).title,'Lean подтвердил контрпример');
});
test('article example matches version, not merely base identifier',()=>{
  const examples=[{arxiv_id:'2610.38474',versioned_id:'2610.38474v1'}];
  assert.equal(m.matchExample({arxiv_id:'2610.38474',versioned_id:'2610.38474v2'},examples),null);
  assert.equal(m.matchExample(examples[0],examples),examples[0]);
});
test('only authored input theorems may start a search',()=>{
  assert.equal(m.theoremChoices(ready).length,1);
  assert.throws(()=>m.structurePayload(ready,'Input.main.eq_1',{}));
  assert.throws(()=>m.structurePayload({...ready,inspection:{success:false}},'Input.main',{}));
});
test('the source and target are pinned; MSC choice is left to existing pipeline',()=>{
  const p=m.structurePayload(ready,'Input.main',m.budget(16,30),' search ');
  assert.equal(p.mode,'multi');assert.equal(p.source_id,'s');assert.equal(p.target,'Input.main');assert.ok(!('msc_codes' in p));assert.equal(p.budget.timeout_seconds,1800);
});
test('article path preserves version and selected section, never fabricates Lean',()=>{
  const p={versioned_id:'2610.38474v1',title:'Article',sections:[{id:'S9'}],msc_codes:['14R10']};
  const payload=m.discoveryPayload(p,'S9',m.budget(8,10));assert.equal(payload.purpose,'discover');assert.deepEqual(payload.paper_ids,['2610.38474v1']);assert.deepEqual(payload.section_ids,['S9']);assert.equal(payload.source_id,undefined);
  assert.throws(()=>m.discoveryPayload(p,'invented',{}));
});
test('bad budgets rejected before POST',()=>{for(const args of [[0,10],[25,10],[2,31],['oops',10],[1.5,4]])assert.throws(()=>m.budget(...args));});
test('transition title takes precedence over truncated generated claim',()=>{
  assert.equal(m.titleOf({selected_transition_id:'s',title:'Candidate truncated',object_graph:{transitions:[{id:'s',title:'Спектр: граф → ось'}]}}),'Спектр: граф → ось');
});
test('budget exhaustion is not mathematical refutation',()=>{
  const r=m.verdict({purpose:'prove',status:'budget_exhausted',outcome:'unknown'});assert.equal(r.kind,'incomplete');
});

// Only the DOM operations used by the workspace are supplied; production methods
// and registered input handlers run unchanged. No browser, API or model is used.
function withWorkspace(check){
  class Element {
    constructor(tag='div'){this.tagName=tag.toUpperCase();this.children=[];this.attributes={};this.dataset={};this.value='';this.hidden=false;this.disabled=false;this.text='';}
    append(...items){for(const item of items){item.parent=this;this.children.push(item);}}
    replaceChildren(...items){this.children=[...items];this.text='';}
    scrollIntoView(){this.scrolled=true;}
    setAttribute(name,value){this.attributes[name]=String(value);}
    get textContent(){return this.text+this.children.map(child=>child.textContent||'').join('');}
    set textContent(value){this.children=[];this.text=String(value);}
    showModal(){this.open=true;}
    close(){this.open=false;}
    remove(){if(this.parent)this.parent.children=this.parent.children.filter(child=>child!==this);}
    focus(){this.focused=true;}
    removeAttribute(name){delete this.attributes[name];}
  }
  const elements=new Map(),node=id=>{if(!elements.has(id))elements.set(id,new Element());return elements.get(id);};
  const tabs=['arxiv','lean','example'].map(kind=>{const tab=new Element();tab.dataset.guidedSource=kind;return tab;});
  const previousDocument=global.document,previousWindow=global.window;
  global.document={getElementById:node,createElement:tag=>new Element(tag),querySelectorAll:()=>tabs};
  global.window={ObjectGraphModel:require('../web/object-graph.js')};
  try{
    const workspace=new m.Workspace({api(){throw Error('Unexpected API call in unit test');},action(){throw Error('Unexpected run action in unit test');}});
    return check(workspace,node,tabs);
  }finally{if(previousDocument===undefined)delete global.document;else global.document=previousDocument;if(previousWindow===undefined)delete global.window;else global.window=previousWindow;}
}

test('changing a file, prepared source or article invalidates the previous inspected target',()=>{
  for(const [id,event]of [['guided-file','onchange'],['guided-example','onchange'],['guided-arxiv','oninput']])withWorkspace((workspace,node)=>{
    workspace.source=ready;workspace.paper={versioned_id:'oldv1'};workspace.token=7;
    node('guided-theorem').value='Input.main';node('guided-selection').hidden=false;
    node('guided-source-preview').append({textContent:'Old source'});node('guided-theorem-preview').append({textContent:'Old target'});
    workspace.updateStart();assert.equal(node('guided-start').disabled,false);
    assert.equal(typeof node(id)[event],'function');node(id)[event]();
    assert.equal(workspace.source,null,id);assert.equal(workspace.paper,null,id);assert.equal(workspace.token,8,id);
    assert.equal(node('guided-selection').hidden,true,id);assert.equal(node('guided-start').disabled,true,id);
    assert.equal(node('guided-source-preview').textContent,'',id);assert.equal(node('guided-theorem-preview').textContent,'',id);
    assert.throws(()=>m.structurePayload(workspace.source,'Input.main',m.budget(8,10)));
    assert.throws(()=>m.discoveryPayload(workspace.paper,'',m.budget(8,10)));
  });
});

test('switching source kind immediately disables an earlier ready launch',()=>withWorkspace((workspace,node,tabs)=>{
  workspace.source=ready;workspace.paper={versioned_id:'oldv1'};node('guided-theorem').value='Input.main';
  workspace.ensureCatalog=async()=>({examples:[]});workspace.updateStart();assert.equal(node('guided-start').disabled,false);
  tabs.find(tab=>tab.dataset.guidedSource==='lean').onclick();
  assert.equal(workspace.kind,'lean');assert.equal(workspace.source,null);assert.equal(workspace.paper,null);
  assert.equal(node('guided-start').disabled,true);assert.equal(node('guided-selection').hidden,true);
  assert.equal(node('guided-lean-fields').hidden,false);assert.equal(node('guided-arxiv-fields').hidden,true);
}));

test('opening a map or selecting a candidate never starts research or opens technical tools',()=>withWorkspace((workspace,node)=>{
  const seen=[];
  workspace.cb.details=()=>{throw Error('Technical tools should remain closed');};
  workspace.cb.verify=()=>{throw Error('Viewing must not verify');};
  workspace.map={setView:value=>seen.push(['view',value]),select:value=>seen.push(['selection',value])};
  workspace.showMap('objects','transition:candidate');
  assert.deepEqual(seen,[['view','objects'],['selection','transition:candidate']]);
  assert.equal(node('guided-map').scrolled,true);
  workspace.showMap('proof');
  assert.deepEqual(seen.at(-1),['view','proof']);
}));

test('progress counts exact obligations once and excludes definitions, generated equations and helper lemmas',()=>withWorkspace((workspace,node)=>{
  const run={status:'running',phase:'composition',formal_contract:{required_obligations:[{target:'Input.a'},{target:'Input.b'},{target:'Input.c'},{target:'Input.d'}]},nodes:[
    {id:'Input.a',status:'proved'},{id:'alias-of-a',target:'Input.a',status:'verified'},
    {id:'node-b',target:'Input.b',status:'verified'},{id:'Input.c',status:'failed'},
    {id:'Input.d',status:'pending'},{id:'Input.definition',status:'defined'},
    {id:'Input.definition.eq_1',status:'proved'},{id:'Input.helper',status:'proved'}]};
  workspace.renderProgress(run);assert.match(node('guided-progress').textContent,/Проверено обязательств: 2 из 4\./);
  assert.doesNotMatch(node('guided-progress').textContent,/из 8\./);assert.match(node('guided-progress').textContent,/после полной сборки и смысловой проверки/);
  workspace.renderProgress({...run,formal_contract:null});assert.doesNotMatch(node('guided-progress').textContent,/Проверено обязательств/);
}));

test('saved graph cards use certificate and semantic review instead of a fixed candidate label',()=>withWorkspace((workspace,node)=>{
  workspace.renderCandidates(null,{transitions:[
    {id:'proved',title:'Verified relation',status:'proved',certificate:{run_id:'proof'},semantic_review:{status:'aligned'}},
    {id:'uncertain',title:'Uncertain relation',status:'proved',certificate:{run_id:'proof'},semantic_review:{status:'uncertain'}},
    {id:'candidate',title:'Model relation',status:'proposed',formulation_status:'candidate'}]});
  const cards=node('guided-candidates').children.slice(1),badges=cards.map(card=>card.children[0]);
  assert.equal(badges[0].textContent,'Доказано');assert.match(badges[0].attributes.class,/\bgood\b/);
  assert.equal(badges[1].textContent,'Lean-цель проверена · смысл не подтверждён');assert.doesNotMatch(badges[1].attributes.class,/\bgood\b/);
  assert.equal(badges[2].textContent,'Кандидат структуры');assert.doesNotMatch(badges[2].attributes.class,/\bgood\b/);
}));

const originalClaim='Кандидат общей структуры, без заявления о проверке Lean.';
function resultFixture(){const run=structuredClone(verified);run.selected_transition_id='bridge';run.object_graph={transitions:[{id:'bridge',claim:originalClaim}]};run.result.semantic_review.reason='Постановка сохраняет объекты и предпосылки выбранной связи.';return run;}
function originalDisclosure(box){return box.children.find(child=>child.tagName==='DETAILS'&&child.children[0]?.textContent==='Исходная формулировка кандидата');}

test('a verified generic result separates original candidate wording from actual verification',()=>withWorkspace((workspace,node)=>{
  const run=resultFixture(),before=JSON.stringify(run);workspace.renderResult(run);const box=node('guided-result');
  assert.equal(box.dataset.verdict,'proved');
  assert.ok(box.children.some(child=>child.tagName==='P'&&child.textContent==='Lean проверил точную формальную цель и все обязательства. Аудит аксиом пройден.'));
  assert.ok(!box.children.some(child=>child.tagName==='P'&&child.textContent.includes(originalClaim)));
  const original=originalDisclosure(box);assert.ok(original);assert.equal(original.children[1].textContent,originalClaim);assert.equal(original.attributes.open,undefined);
  const semantic=box.children.find(child=>child.tagName==='DETAILS'&&child.children[0]?.textContent==='Итоговая смысловая рецензия и границы результата');assert.ok(semantic);assert.equal(semantic.children[1].textContent,run.result.semantic_review.reason);
  assert.equal(JSON.stringify(run),before);
}));

test('negative, incomplete or semantically uncertain results never receive the positive generic copy',()=>withWorkspace((workspace,node)=>{
  const variants=[];
  for(const status of ['failed','cancelled','budget_exhausted'])variants.push({...resultFixture(),status});
  const negative=resultFixture();negative.outcome='refuted';variants.push(negative);
  const uncertain=resultFixture();uncertain.result.semantic_review.status='uncertain';variants.push(uncertain);
  const incomplete=resultFixture();incomplete.result.verification.obligations_passed=false;variants.push(incomplete);
  for(const run of variants){workspace.renderResult(run);const box=node('guided-result');assert.notEqual(box.dataset.verdict,'proved');assert.doesNotMatch(box.textContent,/Lean проверил точную формальную цель и все обязательства/);assert.equal(originalDisclosure(box)?.children[1].textContent,originalClaim);}
}));

test('an exact known mathematical summary remains the result presentation',()=>withWorkspace((workspace,node)=>{
  const summary={title:'Точное известное утверждение',description:'Сохранённое математическое описание.'};
  global.window.MathPresentation={runSummary:()=>summary,render(element,text){element.textContent=text;}};
  workspace.renderResult(resultFixture());const box=node('guided-result');
  assert.ok(box.children.some(child=>child.tagName==='H3'&&child.textContent===summary.title));assert.ok(box.children.some(child=>child.tagName==='P'&&child.textContent===summary.description));
  assert.equal(originalDisclosure(box),undefined);assert.doesNotMatch(box.textContent,/Lean проверил точную формальную цель и все обязательства/);
}));

test('opening a saved attempt only loads it; opening the current result does not rerun',async()=>{
  let workspace,node;
  withWorkspace((w,n)=>{workspace=w;node=n;workspace.$=node;});
  const loaded=[];workspace.cb.load=async id=>{loaded.push(id);return true;};
  workspace.state={run:{id:'current'}};
  await workspace.openRun('saved');
  assert.deepEqual(loaded,['saved']);assert.equal(node('guided-current').scrolled,true);
  await workspace.openRun('current');
  assert.deepEqual(loaded,['saved']);assert.equal(node('guided-result').scrolled,true);
  node('guided-result').hidden=true;node('guided-current').scrolled=false;
  await workspace.openRun('current');assert.equal(node('guided-current').scrolled,true);
  workspace.cb.load=async()=>false;
  await assert.rejects(workspace.openRun('missing'),/Не удалось открыть/);
});

test('a rendered map replaces duplicate candidate controls',()=>withWorkspace((workspace,node)=>{
  workspace.map={};
  workspace.renderCandidates({purpose:'discover',object_graph:{transitions:[{id:'a',title:'Candidate'}]}});
  assert.equal(node('guided-candidates').hidden,true);
  assert.equal(node('guided-candidates').children.length,0);
}));

function articleGraph(){return{id:'original-graph',revision:3,sources:[{url:'https://arxiv.org/html/2610.35651v2#S2'}],objects:[{id:'profile',title:'Profile'},{id:'target',title:'New coordinate'}],transitions:[{id:'coordinate_change',title:'Замена координаты',source_ids:['profile'],target_ids:['target'],formulation_status:'literature_only',agent_task:null,obligations:[]}]};}
function articleSnapshot(){const graph=articleGraph();return{kind:'literature_transition',graph_ref:{id:graph.id,revision:graph.revision},transition:graph.transitions[0],objects:graph.objects,sources:graph.sources,source_sha256:'a'.repeat(64)};}
test('an article analogy request pins one saved transition without requiring or leaking a Lean source',()=>{
  const graph=articleGraph(),before=JSON.stringify(graph),limits=m.budget(16,30),payload=m.transitionSearchPayload(graph,graph.transitions[0],limits,'  Compare the coordinate change.  ');
  assert.deepEqual(payload,{purpose:'structure',mode:'multi',graph_id:'original-graph',graph_revision:3,transition_id:'coordinate_change',budget:{max_calls:16,timeout_seconds:1800,max_parallel:2},question:'Compare the coordinate change.'});
  for(const key of ['source_id','target','paper_ids','section_ids','msc_codes'])assert.equal(key in payload,false);
  for(const change of [g=>delete g.id,g=>g.revision=0,g=>g.revision='3',g=>g.transitions[0].id='other',g=>g.transitions[0].formulation_status='candidate',g=>g.sources.push({structure_transition:articleSnapshot()})]){const invalid=structuredClone(graph);change(invalid);assert.throws(()=>m.transitionSearchPayload(invalid,graph.transitions[0],limits));}
  assert.equal(JSON.stringify(graph),before);
});

test('source navigation keeps the original article separate from the selected bridge lineage',()=>{
  const origin=articleSnapshot(),search={purpose:'structure',contract:{source_transition:origin},source_graph_ref:origin.graph_ref,source_transition_id:origin.transition.id};
  assert.deepEqual(m.sourceNavigation(search),[{kind:'article',label:'← Исходный переход статьи',ref:origin.graph_ref,transitionId:'coordinate_change'}]);
  const proof={...search,purpose:'prove',source_graph_ref:{id:'candidate-map',revision:2},source_transition_id:'route_3_bridge',selected_transition_id:'route_3_bridge'};
  assert.deepEqual(m.sourceNavigation(proof).map(item=>[item.kind,item.ref,item.transitionId]),[['article',origin.graph_ref,'coordinate_change'],['parent',{id:'candidate-map',revision:2},'route_3_bridge']]);
  assert.deepEqual(m.sourceNavigation({purpose:'prove',source_graph_ref:{id:'old-lean-map',revision:1},selected_transition_id:'old-bridge'}).map(item=>[item.kind,item.transitionId]),[['parent','old-bridge']]);
  assert.equal(m.titleOf(search),'Аналоги: Замена координаты');assert.equal(m.verdict({...search,status:'complete',outcome:'unknown',object_graph:{transitions:[{}]}}).kind,'search');
});

test('explicit analogy launch uses the existing budget and blocks double clicks and active runs',async()=>{
  let workspace,node;withWorkspace((w,n)=>{workspace=w;node=n;workspace.$=node;});
  workspace.setBusy=function(value){this.busy=value;};workspace.source=null;workspace.paper=null;node('guided-calls').value='16';node('guided-minutes').value='30';node('guided-question').value='Извлеки все переходы из другой статьи — старый скрытый вопрос';
  const starts=[],errors=[];let release;workspace.cb.start=payload=>{starts.push(payload);return new Promise(resolve=>{release=resolve;});};workspace.cb.error=message=>errors.push(message);
  const graph=articleGraph(),pending=workspace.searchAnalogies(graph,graph.transitions[0]);assert.equal(starts.length,1);assert.equal(workspace.busy,true);await workspace.searchAnalogies(graph,graph.transitions[0]);assert.equal(starts.length,1);
  release();await pending;assert.equal(workspace.busy,false);assert.equal(node('guided-current').scrolled,true);assert.deepEqual(starts[0],m.transitionSearchPayload(graph,graph.transitions[0],m.budget(16,30)));
  workspace.state={run:{status:'running'}};await workspace.searchAnalogies(graph,graph.transitions[0]);assert.equal(starts.length,1);assert.match(errors[0],/Дождитесь завершения/);
});

test('the run heading keeps the work journal without destructive ancestor shortcuts',()=>withWorkspace((workspace,node)=>{
  const opened=[],origin=articleSnapshot(),run={purpose:'prove',status:'failed',source_graph_ref:{id:'bridge-map',revision:1},source_transition_id:'bridge',contract:{source_transition:origin}};
  workspace.cb.openSource=(...args)=>opened.push(args);workspace.cb.details=()=>{};workspace.cb.start=()=>{throw Error('Back navigation must not start work');};workspace.renderCurrent(run,null);
  const actions=node('guided-current').children.find(child=>child.attributes.class==='guided-inline-actions');assert.ok(actions);
  assert.deepEqual(actions.children.map(child=>child.textContent),['Журнал работы']);
  assert.deepEqual(opened,[]);
}));

test('a derived formal graph distinguishes candidate revision two from its own contract revision one',()=>withWorkspace((workspace,node)=>{
  const run={purpose:'prove',status:'running',source_graph_ref:{id:'candidate',revision:2},graph_ref:{id:'derived-formal',revision:1}};workspace.renderCurrent(run,null);
  const meta=node('guided-current').children.find(child=>child.attributes.class==='guided-run-meta');assert.ok(meta);assert.match(meta.textContent,/Версия кандидата 2 · Формальный контракт 1/);assert.doesNotMatch(meta.textContent,/Версия постановки 1/);
  assert.equal(m.versionCaption({...run,graph_ref:{id:'candidate',revision:2}}),'Версия кандидата 2');assert.equal(m.versionCaption({purpose:'prove',graph_ref:{id:'plain',revision:4}}),'Версия постановки 4');assert.equal(m.versionCaption({...run,purpose:'structure'}),'Версия постановки 1');
}));

test('bridge result scope never certifies the original article, including failed and successful outcomes',()=>withWorkspace((workspace,node)=>{
  for(const status of ['complete','failed']){const run={...resultFixture(),status,contract:{source_transition:articleSnapshot()}};workspace.renderResult(run);const box=node('guided-result');assert.match(box.textContent,/применимость к исходному переходу статьи отдельно не подтверждена/);assert.equal(box.dataset.verdict,status==='complete'?'proved':'incomplete');}
}));

test('formalization review explains the concrete missing definitions before Lean',()=>withWorkspace((workspace,node)=>{
  const reason='Нужно сначала определить слабые производные и действие композиции на H¹.';
  const run={...refineRun(),requires_review:true,termination:{code:'needs_review',stage:'formalize_transition',message:reason},formalization_review:{status:'needs_review',reason,limitations:['Принять сохранение формы за гипотезу означало бы предположить вывод.']}};
  const before=JSON.stringify(run);workspace.renderResult(run);
  const result=node('guided-result');assert.match(result.textContent,/Почему остановилась проверка/);assert.match(result.textContent,/Нужно сначала определить слабые производные/);assert.match(result.textContent,/До проверки Lean не дошли/);assert.match(result.textContent,/Что нужно уточнить для продолжения/);assert.equal(result.dataset.verdict,'incomplete');assert.equal(JSON.stringify(run),before);
}));

test('a fresh structure search reveals its source immediately and hides the empty map until candidates arrive',()=>withWorkspace((workspace,node)=>{
  const maps=[],run={id:'fresh-search',purpose:'structure',status:'running',phase:'structure_routes',contract:{source_transition:articleSnapshot()},object_graph:null};
  node('research-panel').classList={toggle(){}};for(const method of ['renderCurrent','renderProgress','renderCandidates','renderResult','renderHistory','updateStart'])workspace[method]=()=>{};workspace.map={render:(...args)=>maps.push(args)};
  workspace.render({run,runs:[]});assert.equal(node('guided-structure-slot').hidden,false);assert.equal(node('guided-structure-slot').open,true);assert.equal(node('structure-results').hidden,false);assert.equal(node('guided-map').hidden,true);assert.equal(maps.length,0);
  node('guided-structure-slot').open=false;workspace.render({run:{...run,updated_at:'next'},runs:[]});assert.equal(node('guided-structure-slot').open,false,'Polling preserves the explicit disclosure choice');assert.equal(maps.length,0);
  const ready={...run,updated_at:'next',object_graph:{id:'candidates',revision:1,objects:[],transitions:[{id:'bridge'}]}};workspace.render({run:ready,runs:[]});assert.equal(node('guided-map').hidden,false);assert.equal(maps.length,1);assert.equal(maps[0][0],ready);assert.equal(node('guided-structure-slot').open,false);
  workspace.render({run:{...run,id:'second-search'},runs:[]});assert.equal(node('guided-structure-slot').open,true);assert.equal(node('guided-map').hidden,true);
  workspace.render({run:{id:'proof',purpose:'prove',status:'running',nodes:[{id:'lemma'}]},runs:[]});assert.equal(node('guided-map').hidden,false);assert.equal(node('guided-structure-slot').hidden,true);assert.equal(maps.length,2);
}));

test('candidate checks belong to bridge maps and refresh when another run changes',()=>withWorkspace((workspace,node)=>{
  node('research-panel').classList={toggle(){}};
  for(const method of ['renderCurrent','renderProgress','renderCandidates','renderResult','renderHistory','updateStart','renderSavedSource','renderLeanStage'])workspace[method]=()=>{};
  const renders=[],suspensions=[];workspace.candidateChecks={render:(...args)=>renders.push(args),suspend:()=>suspensions.push(true)};
  workspace.map={render(){}};
  const article={id:'article-run',purpose:'discover',status:'complete',object_graph:{id:'article-map',revision:1,objects:[],sources:[{id:'paper',versioned_id:'2610.35651v2'}],transitions:[{id:'article-step',formulation_status:'literature_only'}]}};
  workspace.render({run:article,runs:[]});workspace.goStep('connections',{scroll:false,remember:false});
  assert.equal(node('guided-checks').hidden,true);assert.equal(node('guided-directions').hidden,false);assert.equal(renders.length,0);
  const run={...article,id:'bridge-search',purpose:'structure',object_graph:{...article.object_graph,id:'bridge-map',transitions:[{id:'bridge',formulation_status:'candidate'}]}};
  workspace.render({run,runs:[]});assert.equal(node('guided-checks').hidden,false);assert.equal(node('guided-directions').hidden,true);assert.equal(renders.length,1);
  workspace.render({run,runs:[{id:'new-proof',status:'running',updated_at:'one'}]});assert.equal(renders.length,2);
  workspace.goStep('source',{scroll:false,remember:false});assert.equal(node('guided-checks').hidden,true);assert.ok(suspensions.length);
}));

function refineRun(){
  const object=id=>({id,title:id,definition:'Definition '+id,parameters:['p'],assumptions:['Condition '+id],msc_codes:['13']});
  const graph={id:'candidate-map',revision:1,title:'Original map',question:'Original question',objects:['shared','local','output','other'].map(object),sources:[{id:'origin',structure_transition:articleSnapshot()}],transitions:[{id:'chosen',title:'Candidate',claim:'Original broad claim',construction:'Original construction',assumptions:['Original condition'],source_ids:['shared','local'],target_ids:['output'],formulation_status:'candidate',agent_task:null,obligations:[],status:'proposed',last_result:{run_id:'previous'}},{id:'neighbor',title:'Other route',source_ids:['shared'],target_ids:['other'],formulation_status:'formalized',agent_task:{target:'Other'},status:'proved',certificate:{run_id:'other-proof'}}]};
  return{id:'needs-review',purpose:'prove',status:'complete',outcome:'unknown',selected_transition_id:'chosen',graph_ref:{id:graph.id,revision:1},object_graph:graph,result:{reason:'The current scope requires separate analytic obligations.'}};
}
const refinementValues=run=>{const context=m.refinementContext(run.object_graph,run.selected_transition_id);return{title:context.transition.title,claim:context.transition.claim,construction:context.transition.construction,assumptions:context.transition.assumptions,objects:context.objects.filter(item=>item.editable).map(({value})=>({id:value.id,title:value.title,definition:value.definition,parameters:value.parameters,assumptions:value.assumptions}))};};

test('refinement changes only the selected unformalized scope and unique endpoint objects, preserving the source and other routes',()=>{
  const run=refineRun(),before=JSON.stringify(run),fields=refinementValues(run),context=m.refinementTarget(run);assert.deepEqual(context.objects.map(item=>[item.value.id,item.editable]),[['shared',false],['local',true],['output',true]]);
  fields.claim='A revised explicit scope';fields.assumptions='First assumption\nSecond assumption';fields.objects[0].title='Revised object';fields.objects[0].definition='Revised definition';fields.objects[0].parameters='q\nr';fields.objects[0].assumptions='New object condition';
  const draft=m.refinementDraft(run.object_graph,'chosen',fields);assert.equal(draft.transitions[0].claim,fields.claim);assert.deepEqual(draft.transitions[0].assumptions,['First assumption','Second assumption']);assert.equal(draft.transitions[0].last_result,undefined);assert.equal(draft.transitions[0].certificate,undefined);assert.equal(draft.transitions[0].agent_task,null);assert.deepEqual(draft.transitions[0].obligations,[]);
  assert.equal(draft.objects[1].title,'Revised object');assert.deepEqual(draft.objects[1].parameters,['q','r']);assert.deepEqual(draft.transitions[1],run.object_graph.transitions[1]);assert.deepEqual(draft.objects[0],run.object_graph.objects[0]);assert.deepEqual(draft.objects[3],run.object_graph.objects[3]);assert.deepEqual(draft.sources,run.object_graph.sources);assert.equal(draft.question,run.object_graph.question);assert.equal(draft.revision,1);assert.equal(JSON.stringify(run),before);
});

test('refinement rejects empty or unchanged scope, shared-object changes, active runs and foreign graph bindings',()=>{
  const run=refineRun(),fields=refinementValues(run);assert.throws(()=>m.refinementDraft(run.object_graph,'chosen',fields),/не изменилась/);assert.throws(()=>m.refinementDraft(run.object_graph,'chosen',{...fields,claim:''}),/Заполните поле/);assert.throws(()=>m.refinementDraft(run.object_graph,'chosen',{...fields,claim:'New',objects:[{id:'shared',title:'Do not change'}]}),/Общий объект/);
  for(const change of [r=>r.status='running',r=>r.graph_ref.revision=2,r=>r.selected_transition_id='missing',r=>r.object_graph.transitions[0].agent_task={target:'Existing.formalGoal'}]){const invalid=structuredClone(run);change(invalid);assert.equal(m.refinementTarget(invalid),null);}
});

test('the review result exposes exact feedback and an accessible selected-scope editor without automatic work',()=>withWorkspace((workspace,node)=>{
  const run=refineRun(),before=JSON.stringify(run);workspace.renderResult(run);const box=node('guided-result');assert.ok(box.textContent.includes(run.result.reason));const button=box.children.find(child=>child.tagName==='BUTTON'&&child.textContent==='Уточнить постановку');assert.ok(button);button.onclick();
  const edit=workspace.refinement;assert.equal(edit.dialog.tagName,'DIALOG');assert.equal(edit.dialog.open,true);assert.equal(edit.dialog.attributes['aria-labelledby'],'guided-refinement-title');assert.equal(edit.fields.claim.value,run.object_graph.transitions[0].claim);assert.equal(edit.fields.title.focused,true);assert.deepEqual(edit.fields.objects.map(item=>item.id),['local','output']);assert.match(edit.dialog.textContent,/доступен только для чтения/);assert.match(edit.dialog.textContent,/Сертификат не переносится/);assert.equal(JSON.stringify(run),before);
  workspace.closeRefinement();assert.equal(workspace.refinement,null);assert.equal(edit.dialog.open,false);assert.equal(node('guided-research').children.includes(edit.dialog),false);
}));

test('saving a refinement posts one new revision and navigates to it without proving or resuming',async()=>{
  let workspace,edit;const requests=[],opened=[];let resolve;
  withWorkspace(w=>{workspace=w;w.openRefinement(refineRun());edit=w.refinement;});
  workspace.cb.api=(url,payload)=>{requests.push([url,payload]);return new Promise(done=>{resolve=done;});};workspace.cb.onRevision=(...args)=>opened.push(args);workspace.cb.start=()=>{throw Error('Saving must not start a model');};workspace.cb.action=()=>{throw Error('Saving must not resume the old attempt');};edit.fields.claim.value='A revised explicit scope';edit.fields.objects[0].definition.value='Revised object definition';
  const pending=workspace.saveRefinement();assert.equal(requests.length,1);assert.equal(edit.saving,true);assert.equal(edit.save.disabled,true);workspace.closeRefinement();assert.equal(workspace.refinement,edit);await workspace.saveRefinement();assert.equal(requests.length,1);
  const [url,payload]=requests[0];assert.equal(url,'/api/objects/graphs/candidate-map/revisions');assert.equal(payload.expected_revision,1);assert.equal(payload.graph.transitions[0].claim,edit.fields.claim.value);assert.deepEqual(payload.graph.sources,refineRun().object_graph.sources);
  const saved={...payload.graph,revision:2};resolve(saved);await pending;assert.equal(workspace.refinement,null);assert.deepEqual(opened,[[saved,'chosen']]);assert.equal(edit.dialog.open,false);
});

test('a revision conflict leaves the edited text available without navigating or starting proof',async()=>{
  let workspace,edit;withWorkspace(w=>{workspace=w;w.openRefinement(refineRun());edit=w.refinement;});edit.fields.claim.value='Kept user scope';workspace.cb.api=async()=>{throw Error('Graph changed; reload its current revision');};workspace.cb.onRevision=()=>{throw Error('Conflict must not navigate');};await workspace.saveRefinement();assert.equal(workspace.refinement,edit);assert.equal(edit.dialog.open,true);assert.equal(edit.fields.claim.value,'Kept user scope');assert.match(edit.message.textContent,/Graph changed/);assert.equal(edit.save.disabled,false);assert.equal(edit.saving,false);
});

test('the saved needs-review attempt offers only its exact bridge and direct editable endpoints',t=>{
  const fs=require('node:fs'),path=require('node:path'),file=path.join(__dirname,'../research_data/4df45c44aed947809cb63e0d517bdbea/run.json');if(!fs.existsSync(file)){t.skip('Local historical research fixture is not included in a clean clone');return;}
  const run=JSON.parse(fs.readFileSync(file,'utf8')),before=JSON.stringify(run),context=m.refinementTarget(run);assert.equal(context.transition.id,'route_3_finite_dimensional_congruence');assert.equal(run.object_graph.id,'ac905d27c5b94540820562bc6d7736a2');assert.equal(run.object_graph.revision,1);assert.deepEqual(context.objects.filter(item=>item.editable).map(item=>item.value.id),['route_3_input','route_3_library_isometry','route_3_trial_spaces','route_3_matrix_pairs']);assert.deepEqual(context.objects.filter(item=>!item.editable).map(item=>item.value.id),['input_object']);assert.equal(JSON.stringify(run),before);
});

test('termination metadata distinguishes validation, missing proof, Lean failure and service limits without refutation',()=>{
  const expected={invalid_plan:'План отклонён до проверки Lean',invalid_contract:'Формальная постановка отклонена',proof_not_produced:'Текст доказательства не получен',model_response_invalid:'Ответ исполнителя не принят',lean_unproved:'Lean не подтвердил доказательство',needs_review:'Нужно уточнить постановку',cancelled:'Исследование остановлено',budget_exhausted:'Достигнут лимит работы',infrastructure:'Сбой сервиса или окружения',internal_error:'Сбой выполнения'};
  for(const[code,title]of Object.entries(expected)){const run={purpose:'prove',status:'failed',outcome:'unknown',termination:{code,stage:'plan',message:'Exact diagnostic'},semantic_review:{status:'pending'}},before=JSON.stringify(run);assert.equal(m.verdict(run).title,title);assert.equal(m.verdict(run).kind,'incomplete');assert.equal(m.terminationInfo(run).message,'Exact diagnostic');assert.equal(m.finalReview(run).status,'not_performed');assert.match(m.finalReview(run).title,/Итоговая рецензия не проводилась:/);assert.equal(JSON.stringify(run),before);}
  const unsupported={purpose:'prove',status:'complete',outcome:'refuted'};assert.equal(m.verdict(unsupported).kind,'incomplete');assert.match(m.verdict(unsupported).title,/не подтверждено/);
});

test('invalid replanning preserves prior failed Lean evidence instead of claiming no Lean check ever ran',()=>{
  const run={purpose:'prove',status:'failed',termination:{code:'invalid_plan',stage:'plan',message:'Rejected revised plan'},nodes:[{id:'Lemma',status:'failed',verification:{success:false,compilation_success:false,diagnostics:[{file:'Candidate.lean',exit_code:1,stderr:'Earlier type mismatch'}]}}]},before=JSON.stringify(run);
  assert.equal(m.hasLeanEvidence(run),true);assert.equal(m.verdict(run).title,'Новый план доказательства отклонён');assert.match(m.terminationInfo(run).explanation,/Текущий вариант плана/);assert.match(m.terminationInfo(run).explanation,/Ранее выполненные проверки сохранены/);assert.equal(m.verdict(run).kind,'incomplete');assert.equal(JSON.stringify(run),before);
  const noChecks={...run,nodes:[],artifacts:[{path:'plan/Candidate.lean'}]};assert.equal(m.hasLeanEvidence(noChecks),false);assert.equal(m.verdict(noChecks).title,'План отклонён до проверки Lean');
  const logsOnly={...noChecks,artifacts:[{path:'nodes/Lemma/lean-123/Candidate.lean.stderr.log'}]};assert.equal(m.hasLeanEvidence(logsOnly),true);assert.equal(m.verdict(logsOnly).title,'Новый план доказательства отклонён');
  const explicitRevision={...noChecks,termination:{...run.termination,stage:'replan'}};assert.equal(m.verdict(explicitRevision).title,'Новый план доказательства отклонён');assert.doesNotMatch(m.terminationInfo(explicitRevision).explanation,/Ранее выполненные проверки/);
});

function preflightRun(){const run=retryRun();run.termination={code:'proof_not_produced',stage:'prove',message:'Empty proof response'};run.result=null;run.contract_verification={kind:'lean_contract_preflight',status:'complete',well_typed:true,proof_checked:false,outcome:'unknown',target:'Frozen.goal',checked_obligations:[{id:'goal',target:'Frozen.goal',declaration:'AtlasContractGoal'}],declarations:[{name:'context',kind:'def',module:'ContractTypes',type:'Nat'},{name:'AtlasContractGoal',kind:'def',module:'ContractTypes',type:'Prop'}],audit:{status:'passed'},diagnostics:[{file:'ContractTypes.lean',exit_code:0,stdout:'',stderr:''}]};return run;}
test('an accepted contract preflight, even for False, is never a proof or certificate',()=>{
  const run=preflightRun();run.object_graph.transitions[0].agent_task.statement='False';const before=JSON.stringify(run),preflight=m.contractPreflight(run);assert.equal(preflight.accepted,true);assert.equal(preflight.statement,'False');assert.deepEqual(preflight.definitions,['context']);assert.equal(m.formalEvidence(run),false);assert.equal(m.verdict(run).kind,'incomplete');assert.equal(m.verdict(run).title,'Доказательство не получено');assert.match(m.terminationInfo(run).explanation,/Lean принял определения и тип цели\. Доказательство не получено/);assert.equal(run.result,null);assert.equal(JSON.stringify(run),before);
  for(const change of [r=>r.contract_verification.target='Other.goal',r=>r.contract_verification.proof_checked=true,r=>r.contract_verification.audit.status='failed',r=>r.contract_verification.well_typed=false]){const invalid=structuredClone(run);change(invalid);assert.equal(m.contractPreflight(invalid).accepted,false);assert.notEqual(m.verdict(invalid).kind,'proved');assert.notEqual(m.verdict(invalid).kind,'formal_only');}
});
test('contract preflight has a separate compact panel with exact goal, definitions and expandable diagnostics',()=>withWorkspace((workspace,node)=>{
  const run=preflightRun();workspace.renderResult(run);const box=node('guided-result'),panel=box.children.find(child=>child.attributes['aria-label']==='Постановка в Lean');assert.ok(panel);assert.equal(panel.attributes['data-contract-preflight'],'accepted');assert.match(panel.textContent,/не доказывает утверждение и не выдаёт сертификат/);assert.match(panel.textContent,/Цель: Frozen.goal/);assert.match(panel.textContent,/Определения: context/);assert.ok(panel.children.some(child=>child.tagName==='DETAILS'&&child.children[0].textContent==='Точный тип цели'));assert.ok(panel.children.some(child=>child.tagName==='DETAILS'&&child.children[0].textContent==='Определения постановки'));assert.ok(panel.children.some(child=>child.tagName==='DETAILS'&&child.children[0].textContent==='Диагностика Lean и полный отчёт проверки постановки'));assert.equal(box.dataset.verdict,'incomplete');
  workspace.renderProgress({...run,status:'running',phase:'prove'});assert.ok(node('guided-progress').children.some(child=>child.attributes['aria-label']==='Постановка в Lean'));assert.equal(m.progressText({status:'running',phase:'lean_contract_preflight'}),'Lean проверяет определения и тип цели');
}));
test('compiler rejection of a contract is distinct from unproved theorem, timeout and source-validation rejection',()=>withWorkspace((workspace,node)=>{
  const run=preflightRun();run.termination={code:'invalid_contract',stage:'lean_contract_preflight',message:'Compiler failed'};Object.assign(run.contract_verification,{status:'failed',well_typed:false,error:'Command failed',diagnostics:[{file:'ContractTypes.lean',exit_code:1,stdout:'ContractTypes.lean:12:3: error: unknown constant Frozen.symbol\nFull preserved explanation',stderr:''}],termination:run.termination});workspace.renderResult(run);assert.equal(m.verdict(run).title,'Lean отклонил постановку');const panel=node('guided-result').children.find(child=>child.attributes['aria-label']==='Постановка в Lean');assert.equal(panel.attributes['data-contract-preflight'],'not_accepted');assert.match(panel.textContent,/unknown constant Frozen.symbol/);assert.match(panel.textContent,/Full preserved explanation/);assert.match(panel.textContent,/до доказательства/);assert.notEqual(node('guided-result').dataset.verdict,'refuted');
  run.contract_verification.status='timeout';run.contract_verification.termination={code:'lean_timeout',stage:'lean_contract_preflight'};assert.match(m.contractPreflight(run).title,/по времени/);
  run.contract_verification.status='rejected';run.contract_verification.diagnostics=[];run.contract_verification.termination={code:'invalid_contract',stage:'lean_contract_preflight'};assert.equal(m.contractPreflight(run).title,'Постановка не прошла предварительную проверку');
}));
test('contract preflight logs do not masquerade as previous proof checks when the first proof plan is rejected',()=>{
  const run=preflightRun();run.termination={code:'invalid_plan',stage:'plan',message:'Invalid plan'};run.artifacts=[{path:'contract-preflight/key/contract-id/ContractTypes.lean.stdout.log'}];assert.equal(m.hasLeanEvidence(run),false);assert.equal(m.verdict(run).title,'План доказательства отклонён');assert.match(m.terminationInfo(run).explanation,/Lean принял определения и тип цели/);assert.doesNotMatch(m.terminationInfo(run).explanation,/Ранее выполненные проверки/);
  delete run.contract_verification;assert.equal(m.contractPreflight(run),null);assert.equal(m.verdict(run).title,'План отклонён до проверки Lean');
});

test('accepted preflight never masks a later rejection of the actual proof contract',()=>withWorkspace((workspace,node)=>{
  for(const stage of ['compose','lean_contract']){const run=preflightRun();run.termination={code:'invalid_contract',stage,message:'Contract.lean rejected a different proof type'};run.result={verification:{success:false,target:'Frozen.goal',target_preserved:false,diagnostics:[{file:'Contract.lean',exit_code:1,stdout:'error: type mismatch in final proof',stderr:''}]}};const before=JSON.stringify(run);assert.equal(m.contractPreflight(run).accepted,true);assert.equal(m.verdict(run).title,'Доказательство не прошло проверку на точную цель');assert.equal(m.verdict(run).kind,'incomplete');assert.doesNotMatch(m.terminationInfo(run).explanation,/а не её доказательство/);workspace.renderResult(run);const box=node('guided-result');assert.match(box.textContent,/Доказательство не прошло проверку на точную цель/);assert.match(box.textContent,/Contract.lean rejected/);assert.ok(box.children.some(child=>child.attributes['data-contract-preflight']==='accepted'));assert.equal(JSON.stringify(run),before);}
}));

test('initial contract review is never presented as a final review after an early stop',()=>withWorkspace((workspace,node)=>{
  const run={purpose:'prove',status:'failed',outcome:'unknown',error:'Тип леммы не должен содержать команды Lean.',contract_review:{status:'aligned',reason:'Initial scope aligned'},semantic_review:{status:'aligned'},final_semantic_review:{status:'not_performed',reason:'План отклонён до Lean'}};workspace.renderResult(run);const box=node('guided-result');assert.match(box.textContent,/План отклонён до проверки Lean/);assert.match(box.textContent,/Итоговая рецензия не проводилась: План отклонён до Lean/);assert.ok(box.children.some(child=>child.tagName==='DETAILS'&&child.children[0].textContent==='Рецензия постановки до доказательства'));assert.ok(box.children.some(child=>child.tagName==='DETAILS'&&child.children[0].textContent==='Диагностика завершения'));assert.ok(!box.children.some(child=>child.tagName==='DETAILS'&&child.children[0].textContent==='Итоговая смысловая рецензия и границы результата'));assert.notEqual(box.dataset.verdict,'proved');
  assert.equal(m.finalReview({purpose:'structure',status:'complete',semantic_review:{status:'pending'}}).status,'not_applicable');
  const checked=structuredClone(verified);checked.final_semantic_review={status:'not_performed',reason:'Review service failed'};assert.equal(m.verdict(checked).kind,'formal_only');assert.match(m.verdict(checked).title,/итоговая рецензия не выполнена/);checked.final_semantic_review={status:'mismatch',reason:'A semantic mismatch'};assert.equal(m.verdict(checked).kind,'formal_only');
}));

test('a later stop preserves an exact compiled Lean result without claiming final semantic success',()=>withWorkspace((workspace,node)=>{
  for(const status of ['budget_exhausted','interrupted','cancelled','failed']){
    const run={...structuredClone(verified),status,formal_contract:{target:'Exact.goal'},termination:{code:status==='failed'?'infrastructure':status==='interrupted'?'infrastructure':status,stage:'semantic_review',message:'Review did not finish'},final_semantic_review:{status:'not_performed',reason:'Остановка после Lean'},result:{verification:{...verified.result.verification,target:'Exact.goal',compilation_success:true},semantic_review:{status:'pending'}}};
    assert.equal(m.formalEvidence(run),true);assert.equal(m.verdict(run).kind,'formal_only');workspace.renderResult(run);const box=node('guided-result');assert.equal(box.dataset.verdict,'formal_only');assert.match(box.textContent,/Lean подтвердил формальную цель/);assert.match(box.textContent,/Итоговая рецензия не проводилась: Остановка после Lean/);assert.ok(box.textContent.includes(m.terminationInfo(run).title));assert.doesNotMatch(box.textContent,/Связь проверена в Lean/);
    const wrong=structuredClone(run);wrong.result.verification.target='Other.goal';assert.equal(m.formalEvidence(wrong),false);assert.equal(m.verdict(wrong).kind,'incomplete');
  }
  const timeout={purpose:'prove',status:'failed',termination:{code:'lean_timeout',stage:'verify',message:'Timeout'}};assert.equal(m.terminationInfo(timeout).code,'lean_timeout');assert.match(m.verdict(timeout).title,/по времени/);
}));

function retryRun(){const run=refineRun();run.status='failed';run.mode='multi';run.budget={max_calls:16,timeout_seconds:1800,max_parallel:2};Object.assign(run.object_graph.transitions[0],{formulation_status:'formalized',agent_task:{target:'Frozen.goal',statement:'True',prelude:'def context := 1',imports:['Mathlib']},obligations:[{id:'goal',target:'Frozen.goal',statement:'True',expected_outcome:'proved'}]});return run;}
test('retry creates the exact saved formal graph payload with the original mode and budget',()=>{
  const run=retryRun(),before=JSON.stringify(run),payload=m.retryPayload(run);assert.deepEqual(payload,{purpose:'prove',mode:'multi',graph_id:'candidate-map',graph_revision:1,transition_id:'chosen',budget:{max_calls:16,timeout_seconds:1800,max_parallel:2},msc_codes:[]});for(const key of ['question','source_id','target','paper_ids','source_graph_ref'])assert.equal(key in payload,false);assert.equal(JSON.stringify(run),before);
  for(const change of [r=>r.status='running',r=>r.status='complete',r=>r.graph_ref.revision=2,r=>r.object_graph.transitions[0].agent_task=null,r=>r.budget=null,r=>r.budget.max_calls=0]){const invalid=structuredClone(run);change(invalid);assert.equal(m.canRetry(invalid),false);assert.throws(()=>m.retryPayload(invalid));}
});
test('retry is explicit, creates a new run once and never resumes or rewrites the old attempt',async()=>{
  let workspace,node;withWorkspace((w,n)=>{workspace=w;node=n;workspace.$=node;workspace.renderResult(retryRun());});workspace.setBusy=function(value){this.busy=value;};const run=retryRun(),before=JSON.stringify(run),starts=[],errors=[];let release;workspace.cb.start=payload=>{starts.push(payload);return new Promise(resolve=>{release=resolve;});};workspace.cb.action=()=>{throw Error('Retry must not resume');};workspace.cb.error=message=>errors.push(message);assert.equal(starts.length,0);const actions=node('guided-result').children.find(child=>child.attributes.class==='guided-inline-actions');assert.ok(actions.children.some(child=>child.textContent==='Повторить проверку'));assert.ok(!actions.children.some(child=>child.textContent==='Продолжить запуск'));assert.match(node('guided-result').textContent,/16 вызовов \/ 30 мин/);
  const pending=workspace.retry(run);await workspace.retry(run);assert.equal(starts.length,1);release();await pending;assert.deepEqual(starts,[m.retryPayload(run)]);assert.equal(JSON.stringify(run),before);assert.equal(errors.length,0);assert.equal(workspace.busy,false);
});

for(const[id,code,retry]of [['1021913905104fea9267d81d3e3dbff6','invalid_plan',true],['624de3c0099e4e978f50bbc781154a8e','proof_not_produced',true],['4df45c44aed947809cb63e0d517bdbea','needs_review',false]]){
  const fs=require('node:fs'),path=require('node:path'),file=path.join(__dirname,'../research_data',id,'run.json');
  test('legacy attempt '+id+' has the saved failure meaning without modifying its record',{skip:!fs.existsSync(file)&&'Local research fixture is not distributed'},()=>{
    const run=JSON.parse(fs.readFileSync(file,'utf8')),before=JSON.stringify(run);assert.equal(m.terminationInfo(run).code,code);assert.equal(m.verdict(run).kind,'incomplete');assert.equal(m.finalReview(run).status,'not_performed');assert.equal(m.canRetry(run),retry);if(retry){const payload=m.retryPayload(run);assert.equal(payload.graph_id,run.graph_ref.id);assert.equal(payload.graph_revision,run.graph_ref.revision);assert.deepEqual(payload.budget,run.budget);}assert.equal(JSON.stringify(run),before);
  });
}


test('step navigation distinguishes available views from execution progress',()=>{
  const enabled=(run,draft)=>m.stepNavigation(run,draft).filter(s=>s.available).map(s=>s.id);
  assert.deepEqual(enabled(null,null),['source']);
  assert.deepEqual(enabled(null,{id:'map'}),['source','connections']);
  assert.deepEqual(enabled({purpose:'structure',status:'running'}),['source','connections']);
  assert.deepEqual(enabled({purpose:'structure',status:'complete'}),['source','connections','result']);
  assert.deepEqual(enabled({purpose:'prove',status:'running'}),['source','connections','lean']);
  assert.deepEqual(enabled({purpose:'prove',status:'failed'}),['source','connections','lean','result']);
  assert.equal(m.selectedStep({purpose:'prove',status:'failed'},null,'source'),'source');
  assert.equal(m.selectedStep({purpose:'structure',status:'running'},null,'lean'),'connections');
  assert.equal(m.selectedStep(null,null,'result'),'source');
});

test('backward and forward step browsing preserves the exact run and cannot start research',()=>withWorkspace((workspace,node)=>{
  node('research-panel').classList={toggle(){}};
  const run={...preflightRun(),id:'kept-run',paper_manifest:[{title:'Pinned article',versioned_id:'2610.35651v2',source_urls:{abstract:'https://arxiv.org/abs/2610.35651v2'}}]},before=JSON.stringify(run),maps=[];
  workspace.map={render:(r,options)=>maps.push([r,options])};
  workspace.cb.start=workspace.cb.load=workspace.cb.action=()=>{throw Error('Viewing a step cannot start or replace the run');};
  workspace.render({run,runs:[]});assert.equal(workspace.step,'result');assert.equal(node('guided-result').hidden,false);assert.equal(node('guided-map').hidden,true);
  workspace.stepButtons.source.onclick();assert.equal(workspace.step,'source');assert.equal(node('guided-saved-source').hidden,false);assert.equal(node('guided-result').hidden,true);assert.match(node('guided-saved-source').textContent,/Pinned article/);assert.equal(workspace.stepButtons.source.attributes['aria-current'],'step');
  workspace.stepButtons.connections.onclick();assert.equal(node('guided-map').hidden,false);assert.equal(maps.at(-1)[0],run);assert.equal(maps.at(-1)[1].view,'objects');
  workspace.stepButtons.lean.onclick();assert.equal(node('guided-lean').hidden,false);assert.match(node('guided-lean').textContent,/Граф лемм пока не построен/);assert.equal(node('guided-map').hidden,true);
  workspace.stepButtons.result.onclick();assert.equal(node('guided-result').hidden,false);assert.equal(workspace.state.run,run);assert.equal(JSON.stringify(run),before);
}));

test('polling and completion preserve the viewed source and expanded source details',()=>withWorkspace((workspace,node)=>{
  node('research-panel').classList={toggle(){}};
  const run={...preflightRun(),id:'active',status:'running',updated_at:'first'};
  workspace.render({run,runs:[]});assert.equal(workspace.step,'lean');
  workspace.goStep('source',{scroll:false,remember:false});const content=node('guided-saved-source').children;content[0].open=true;
  workspace.render({run:{...run,updated_at:'next',phase:'prove'},runs:[]});assert.equal(workspace.step,'source');assert.equal(node('guided-saved-source').children,content);assert.equal(content[0].open,true);
  workspace.render({run:{...run,status:'failed',updated_at:'last'},runs:[]});assert.equal(workspace.step,'source');assert.equal(workspace.stepButtons.result.disabled,false);
  workspace.render({run:{...run,id:'another'},runs:[]});assert.equal(workspace.step,'lean');assert.notEqual(node('guided-saved-source').children,content);
}));

test('URL stage restore validates availability and uses the preserved run without API calls',()=>withWorkspace((workspace,node)=>{
  node('research-panel').classList={toggle(){}};
  const run={...preflightRun(),id:'saved'};workspace.urlStep=()=> 'source';workspace.render({run,runs:[]});assert.equal(workspace.step,'source');
  workspace.urlStep=()=> 'connections';workspace.restoreStep();assert.equal(workspace.step,'connections');assert.equal(workspace.state.run,run);
  workspace.urlStep=()=> 'result';workspace.restoreStep();assert.equal(workspace.step,'result');
  workspace.urlStep=()=> 'not-a-step';workspace.restoreStep();assert.equal(workspace.step,'result');
}));


test('browser Back to a viewed stage invalidates a slower pending run load',async()=>{
  const fs=require('node:fs'),vm=require('node:vm'),code=fs.readFileSync(require.resolve('../web/research.js'),'utf8');
  const loadLine=code.split('\n').find(line=>line.trim().startsWith('async function loadRun('));
  const backLine=code.split('\n').find(line=>line.includes("window.addEventListener('popstate'"));
  for(const draft of [false,true]){
    let release,onBack,restored=0;
    const run={id:'A'},state={initialized:true,request:0,run:draft?null:run,draftGraph:draft?{id:'G',revision:2}:null};
    const context={state,objectWorkspace:{loadToken:'old'},api:()=>new Promise(resolve=>{release=resolve;}),error(){},URL,
      location:{hash:'#research',href:draft?'http://localhost/?object_graph=G&graph_revision=2&step=source#research':'http://localhost/?research=A&step=source#research'},
      $:()=>({close(){}}),guidedWorkspace:{history:{hide(){}},restoreStep(){restored++;}},window:{addEventListener(type,handler){onBack=handler;}}};
    vm.createContext(context);vm.runInContext(loadLine+'\n'+backLine,context);
    const pending=vm.runInContext("loadRun('B')",context);assert.equal(state.request,1);onBack();assert.equal(restored,1);assert.equal(state.request,2);assert.equal(context.objectWorkspace.loadToken,null);
    release({run:{id:'B'}});assert.equal(await pending,false);assert.equal(state.run,draft?null:run);if(draft)assert.equal(state.draftGraph.id,'G');
  }
});


test('a saved graph draft displays its pinned article transition instead of the candidate question',()=>withWorkspace((workspace,node)=>{
  const graph=refineRun().object_graph,before=JSON.stringify(graph);workspace.paper={title:'Unrelated old form'};workspace.renderSavedSource(null,graph);
  assert.match(node('guided-saved-source').textContent,/Замена координаты/);assert.doesNotMatch(node('guided-saved-source').textContent,/Unrelated old form/);assert.equal(JSON.stringify(graph),before);
}));


test('contract errors offer readable causes and another candidate without rerunning proof',()=>withWorkspace((workspace,node)=>{
  const run=preflightRun();run.termination={code:'invalid_contract',stage:'lean_contract_preflight'};Object.assign(run.contract_verification,{status:'rejected',well_typed:false,termination:run.termination,diagnostics:[{file:'ContractTypes.lean',exit_code:1,stdout:'ContractTypes.lean:7:2: error: invalid field notation\nfailed to synthesize\n MeasurableSpace X\ntype mismatch',stderr:''}]});
  const before=JSON.stringify(run),p=m.contractPreflight(run);assert.equal(p.issues.length,3);assert.match(p.issues[1],/измеримую структуру/);assert.equal(p.diagnostic.startsWith('ContractTypes.lean: ContractTypes.lean:'),false);
  workspace.renderResult(run);const result=node('guided-result');assert.match(result.textContent,/Повтор с теми же определениями не исправляет/);assert.match(result.textContent,/invalid field notation/);
  const action=result.children.find(child=>child.attributes.class==='guided-inline-actions').children.find(child=>child.textContent==='Выбрать другую связь');assert.ok(action);let chosen;workspace.goStep=id=>chosen=id;workspace.cb.start=()=>{throw Error('View must not run');};action.onclick();assert.equal(chosen,'connections');assert.equal(JSON.stringify(run),before);
}));
