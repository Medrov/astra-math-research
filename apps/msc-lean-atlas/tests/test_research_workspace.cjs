'use strict';
const test=require('node:test'),assert=require('node:assert/strict');
const workspace=require('../web/research-workspace.js'),guided=require('../web/guided-research.js'),map=require('../web/research-map.js'),history=require('../web/research-history.js');
function run(fields={}){return {id:'attempt',purpose:'prove',status:'failed',source_title:'Полиномиальные преобразования',formal_contract:{target:'Bridge.goal'},
  budget:{max_calls:16,timeout_seconds:1800},usage:{calls:1,total_tokens:32883,elapsed_seconds:37.485},
  termination:{code:'invalid_contract',stage:'lean_contract_preflight',message:'Unknown identifier'},
  contract_verification:{kind:'lean_contract_preflight',target:'Bridge.goal',well_typed:false,proof_checked:false,status:'rejected',audit:{status:'pending'},
    termination:{code:'invalid_contract',stage:'lean_contract_preflight'},diagnostics:[{file:'ContractTypes.lean',exit_code:1,stdout:"error: unknown identifier 'Function.iterate'"}]},...fields};}

test('contract failure is localized to elaboration and never marks later stages as attempted or proved',()=>{
  const value=run(),before=JSON.stringify(value),stages=workspace.stages(value);
  assert.deepEqual(stages.map(stage=>stage.state),['complete','stopped','pending','pending','pending','pending']);
  const result=workspace.resultSummary(value);assert.equal(result.kind,'incomplete');assert.match(result.stopped,/до доказательства/);assert.match(result.next,/новую версию/);assert.doesNotMatch(result.achieved,/проверены Lean/);assert.equal(JSON.stringify(value),before);
});
test('a saved draft rejected by preflight completes preparation without inventing type or proof success',()=>{
  // Reduced shape of failed run 9964f19c4ea340168b1a719cf1dcf9b4; no formal_contract was frozen.
  const value={id:'draft-failed',purpose:'prove',status:'failed',phase:'failed',active_stage:'formalize_transition',
    termination:{code:'invalid_contract',stage:'lean_contract_preflight'},
    draft_repair:{status:'stopped',version:0,repairs:0,max_repairs:2,intent_sha256:'94a0006b82628fcc07fcb57653d0ecf1794532fed851175cc6ace9ec77094efb'},
    contract_verification:{kind:'lean_contract_preflight',target:'top_exterior_bridge',status:'rejected',well_typed:false,proof_checked:false,
      checked_obligations:[{id:'primary',target:'top_exterior_bridge',declaration:'Probe.expectedType0'}],audit:{status:'pending'}}};
  const before=JSON.stringify(value);assert.deepEqual(workspace.stages(value).map(stage=>stage.state),['complete','stopped','pending','pending','pending','pending']);
  assert.match(workspace.resultSummary(value).achieved,/Черновик/);assert.equal(guided.formalEvidence(value),false);assert.equal(JSON.stringify(value),before);
  const legacy={...value};delete legacy.draft_repair;assert.equal(workspace.stages(legacy)[0].state,'complete');
  delete legacy.contract_verification;assert.notEqual(workspace.stages(legacy)[0].state,'complete');assert.doesNotMatch(workspace.resultSummary(legacy).achieved,/Черновик/);
  legacy.draft_repair={status:'unknown',version:0};assert.notEqual(workspace.stages(legacy)[0].state,'complete');
});
test('a typed draft marker does not replace the actual accepted preflight report',()=>{
  const value={purpose:'prove',status:'running',phase:'lean_contract_preflight',draft_repair:{status:'typed',version:1}};
  assert.deepEqual(workspace.stages(value).map(stage=>stage.state),['complete','active','pending','pending','pending','pending']);
  value.contract_verification={kind:'lean_contract_preflight',target:'Draft.goal',status:'complete',well_typed:true,proof_checked:false,audit:{status:'passed'}};
  assert.equal(workspace.stages(value)[1].state,'complete');assert.ok(workspace.stages(value).slice(2).every(stage=>stage.state==='pending'));
});
test('well-typed proposition is distinct from proving it or completing a semantic review',()=>{
  const value=run({termination:{code:'proof_not_produced',stage:'prove'}});Object.assign(value.contract_verification,{well_typed:true,status:'complete',audit:{status:'passed'}});
  assert.equal(workspace.stages(value)[1].state,'complete');assert.equal(workspace.stages(value)[4].state,'pending');assert.equal(workspace.stages(value)[5].state,'pending');assert.match(workspace.resultSummary(value).achieved,/тип цели приняты/);
});
test('successful Lean without final semantic review remains a separate incomplete stage',()=>{
  const value=run({status:'budget_exhausted',termination:{code:'budget_exhausted',stage:'final_semantic_review'},contract_review:{status:'aligned'},
    result:{verification:{target:'Bridge.goal',success:true,compilation_success:true,target_preserved:true,obligations_passed:true,audit:{status:'passed'}}}});
  const stages=workspace.stages(value);assert.equal(stages[4].state,'complete');assert.equal(stages[5].state,'stopped');assert.equal(guided.verdict(value).kind,'formal_only');
});
test('final all-obligation evidence completes the proof stage when the compiler graph also contains definitions',()=>{
  // Shape observed in run 0aa54bc83b1c4d358155d20a4610ecf4; no saved run is required or changed.
  const targets=['polynomial_bridge','iteration_transport','periodic_points','least_positive_period'];
  const value=run({status:'complete',phase:'complete',outcome:'proved',termination:null,formal_contract:{target:'DynamicsBridge.iteration_transport'},contract_review:{status:'aligned'},
    contract_verification:{kind:'lean_contract_preflight',target:'DynamicsBridge.iteration_transport',well_typed:true,proof_checked:false,status:'complete',audit:{status:'passed'}},
    nodes:[...targets,'evaluate.eq_1'].map(name=>({id:'DynamicsBridge.'+name,target:'DynamicsBridge.'+name,kind:'theorem',status:'proved',extraction:'lean_environment'})).concat(['evaluate','conjugate','Per','LeastPositivePeriod'].map(name=>({id:'DynamicsBridge.'+name,target:'DynamicsBridge.'+name,kind:'def',status:'defined',extraction:'lean_environment'}))),
    result:{outcome:'proved',semantic_review:{status:'aligned'},verification:{target:'DynamicsBridge.iteration_transport',success:true,compilation_success:true,target_preserved:true,obligations_passed:true,audit:{status:'passed'},obligations:targets.map(id=>({id,target:'DynamicsBridge.'+id,ok:true}))}}});
  const before=JSON.stringify(value);assert.deepEqual(workspace.stages(value).map(stage=>stage.state),Array(6).fill('complete'));assert.equal(JSON.stringify(value),before);
  assert.equal(workspace.stages({...value,nodes:[]})[3].state,'complete');
  const unfinished=structuredClone(value);unfinished.result=null;unfinished.nodes.find(node=>node.kind==='theorem').status='failed';assert.equal(workspace.stages(unfinished)[3].state,'stopped');
  unfinished.nodes=unfinished.nodes.filter(node=>node.kind==='def');assert.equal(workspace.stages(unfinished)[3].state,'stopped');
});
test('draft revisions have no false failure or progress and need explicit start',()=>{
  const value=run({status:'draft',ready_to_start:true,termination:null,source_lineage:{parent_run_id:'old',root_run_id:'root',kind:'correction',reason:'Correct a library name'}});
  assert.ok(workspace.stages(value).every(stage=>stage.state==='pending'));assert.equal(guided.verdict(value).kind,'draft');assert.equal(guided.defaultStep(value),'source');assert.equal(workspace.resultSummary(value).kind,'draft');assert.equal(workspace.lineage(value).parent,'old');assert.equal(workspace.lineage(value).root,'root');
});
test('bounded repair appears at the type stage rather than as proof progress',()=>{
  const stages=workspace.stages(run({status:'running',termination:null,phase:'repair_contract',draft_repair:{status:'checking',version:2,max_repairs:2}}));
  assert.equal(stages[1].state,'active');assert.ok(stages.slice(2).every(stage=>stage.state==='pending'));
});
test('search stages do not convert saved candidate count into proof evidence',()=>{
  const value=run({purpose:'structure',status:'complete',outcome:'proved',object_graph:{transitions:[{},{}]}});
  assert.equal(workspace.stages(value).length,3);assert.ok(workspace.stages(value).every(stage=>stage.state==='complete'));assert.match(workspace.resultSummary(value).achieved,/2 кандидатов/);assert.equal(workspace.resultSummary(value).kind,'search');
});
test('resource metrics preserve observed usage and identify the selected backend',()=>{
  const metrics=workspace.resourceUsage(run({proof_backend:'goedel-adapted'}));assert.equal(metrics.calls,1);assert.equal(metrics.seconds,37.485);assert.equal(metrics.tokens,32883);assert.match(metrics.backend,/Goedel/);
  const empty=workspace.resourceUsage({usage:{calls:-1,total_tokens:'not measured'}});assert.equal(empty.calls,0);assert.equal(empty.tokens,0);
  assert.match(workspace.resourceUsage(run({mode:'multi'})).backend,/SHAIM \/ native/);assert.doesNotMatch(workspace.resourceUsage(run({mode:'multi'})).backend,/Локальная проверка/);
});
test('source fields preserve object definitions and all assumptions without fabricating grounding',()=>{
  const card={input_objects:[{id:'a',title:'A',definition:'An object',assumptions:['x > 0']}],output_objects:[{title:'B'}],assumptions:['R is a ring'],operations:['Map A to B'],conclusion:'A ≃ B',scope:'Conditional bridge'};
  const before=JSON.stringify(card),fields=workspace.sourceCardFields(card);assert.equal(fields.find(field=>field.label==='Входные объекты').values[0].definition,'An object');assert.deepEqual(fields.find(field=>field.label==='Предпосылки').values,['R is a ring']);assert.equal(JSON.stringify(card),before);
});
test('version diff preserves both sides and reports changed assumptions even with equal titles',()=>{
  const before={title:'Bridge',assumptions:['CommRing R'],conclusion:'A = B',formal_statement:'Function.iterate f n = g'},after={...before,assumptions:['Field R'],formal_statement:'Nat.iterate f n = g'};
  const changes=workspace.compareCards(before,after);assert.deepEqual(changes.map(change=>change.key),['assumptions','formal_statement']);assert.deepEqual(changes[0].before,['CommRing R']);assert.deepEqual(changes[0].after,['Field R']);assert.deepEqual(workspace.compareCards(before,structuredClone(before)),[]);
});
test('explorer filters keep the selected node visible without changing the graph or numbering',()=>{
  const nodes=[{id:'a',kind:'object',number:1,title:'Кольцо',statusLabel:'Объект'},{id:'b',kind:'transition',number:2,title:'Связь спектров',statusLabel:'Кандидат',mscContext:{items:[{code:'14',title:'Алгебраическая геометрия'}]}}],before=JSON.stringify(nodes);
  assert.deepEqual(map.visibleNodes(nodes,{query:'ГЕОМЕТРИЯ',kind:'transition'}).map(node=>node.id),['b']);assert.deepEqual(map.visibleNodes(nodes,{query:'missing',selected:'a'}).map(node=>node.id),['a']);assert.equal(JSON.stringify(nodes),before);
});
test('history groups saved lineage and treats a ready draft as unstarted',()=>{
  const runs=[{id:'new',source_lineage:{root_run_id:'r',parent_run_id:'r'}},{id:'other',source_title:'Other'},{id:'r',source_lineage:{root_run_id:'r'}}];
  assert.deepEqual(history.groupRuns(runs).map(run=>run.id),['new','r','other']);assert.equal(history.statusOf({status:'draft'}).kind,'draft');
});
test('same invalid contract is not offered as a useful exact retry',()=>{
  assert.equal(guided.canRetry(run()),false);assert.throws(()=>guided.retryPayload(run()));
});

class Element{
  constructor(tag,doc){this.tagName=tag.toUpperCase();this.ownerDocument=doc;this.children=[];this.attributes={};this.dataset={};this._text='';this.hidden=false;}
  append(...nodes){this.children.push(...nodes);}replaceChildren(...nodes){this.children=[];this.append(...nodes);}setAttribute(key,value){this.attributes[key]=String(value);}getAttribute(key){return this.attributes[key]??null;}
  set textContent(value){this._text=String(value);this.children=[];}get textContent(){return this._text+this.children.map(node=>node.textContent).join('');}
}
const all=node=>[node,...node.children.flatMap(all)];
function dom(){const nodes=new Map(),doc={createElement(tag){return new Element(tag,this);},getElementById(id){if(!nodes.has(id))nodes.set(id,new Element('section',this));return nodes.get(id);}};return {doc,nodes};}
test('viewing draft workspace never starts it; the explicit action does and parent navigation preserves history',()=>{
  const {doc,nodes}=dom(),actions=[],view=new workspace.Workspace({document:doc,onStart:()=>actions.push('start'),onOpenRun:id=>actions.push(id)});
  view.render(run({status:'draft',ready_to_start:true,source_lineage:{parent_run_id:'old'}}));assert.deepEqual(actions,[]);
  all(nodes.get('workspace-timeline')).find(node=>node.tagName==='BUTTON'&&node.textContent==='Запустить проверку этой версии').onclick();assert.deepEqual(actions,['start']);
  all(nodes.get('workspace-context')).find(node=>node.tagName==='BUTTON'&&node.textContent==='← Предыдущая попытка').onclick();assert.deepEqual(actions,['start','old']);
});
test('grounding identifies proposals, preserves quotes literally and refuses executable links',()=>{
  const {doc}=dom(),view=new workspace.Workspace({document:doc});
  const card=view.sourceCard({conclusion:'A = B',sources:[{id:'bad',url:'javascript:alert(1)',title:'unsafe'}],grounding:[{component:'Conclusion',origin:'proposed_abstraction',source_ref:'bad',quote:'<img src=x onerror=attack()>'}]});
  assert.match(card.textContent,/Предложенная абстракция/);const quote=all(card).find(node=>node.tagName==='BLOCKQUOTE');assert.equal(quote.textContent,'<img src=x onerror=attack()>');assert.equal(quote.children.length,0);assert.equal(all(card).filter(node=>node.tagName==='A').length,0);
  assert.match(view.sourceCard({conclusion:'A = B'}).textContent,/ещё не размечены/);
});
test('a revised draft saves the chosen available backend without starting any research',async()=>{
  const {doc}=dom(),requests=[],opened=[],originalDocument=global.document;doc.body=new Element('body',doc);
  const create=doc.createElement.bind(doc);doc.createElement=tag=>{const node=create(tag);node.focus=()=>{};node.showModal=()=>{node.open=true;};node.close=()=>{node.open=false;node.onclose?.();};node.remove=()=>{};return node;};global.document=doc;
  try{const view=Object.create(guided.Workspace.prototype);view.backends=[{id:'native',title:'SHAIM',description:'Native controller',available:true},{id:'goedel-adapted',title:'Goedel',description:'Adapted controller',available:true},{id:'offline',title:'Unavailable',available:false}];
    view.prose=(value,tag='p')=>view.el(tag,{},value);view.cb={api:async(path,payload)=>{requests.push({path,payload});return {run:{id:'revision',status:'draft',ready_to_start:true}};}};view.openRun=async id=>opened.push(id);
    view.openRevision(run({source_card:{editable:true,title:'Bridge',conclusion:'A = B',assumptions:['Ring R']}}));
    const nodes=all(view.revisionDialog),form=nodes.find(node=>node.tagName==='FORM'),select=nodes.find(node=>node.tagName==='SELECT'),reason=nodes.find(node=>node.tagName==='TEXTAREA');
    assert.equal(select.value,'native');assert.equal(select.children.find(node=>node.attributes.value==='offline').disabled,true);assert.deepEqual(requests,[]);
    assert.equal(nodes.find(node=>node.tagName==='LABEL'&&node.textContent==='Процесс доказательства').attributes.for,select.attributes.id);
    select.value='goedel-adapted';select.onchange();reason.value='Use the adapted proof controller';await form.onsubmit({preventDefault(){}});
    assert.deepEqual(requests,[{path:'/api/research/runs/attempt/revise',payload:{reason:'Use the adapted proof controller',proof_backend:'goedel-adapted',preserve_formalization:false}}]);assert.deepEqual(opened,['revision']);
  }finally{global.document=originalDocument;}
});
test('mechanism details render the stored API contract, every obligation and provenance safely without running research',async()=>{
  const {doc,nodes}=dom(),requests=[],opened=[],originalDocument=global.document;global.document=doc;
  const statement='∀ n : Nat, n = n',proof='import Init\nnamespace Fixture\ntheorem identity (n : Nat) : n = n := by rfl\nend Fixture\n';
  const record={id:'a'.repeat(64),schema_version:1,title:'Identity fixture',status:'verified_stored_contract',
    formal_contract:{imports:['Init'],prelude:'namespace Fixture',target:'Fixture.identity',statement,required_obligations:[
      {id:'identity',target:'Fixture.identity',statement,expected_outcome:'proved'},
      {id:'extra',target:'Fixture.extra',statement:'∀ n : Nat, n + 0 = n',expected_outcome:'proved'}]},
    provenance:{run_id:'b'.repeat(32),title:'Original fixture',source_sha256:'c'.repeat(64),source_kind:'literature',assumptions:['n is a natural number'],proof_backend:'goedel-adapted',claim:'An explicit fixture only',
      sources:[{id:'source',title:'<img src=x onerror=attack()>',url:'https://example.org/source',locator:'Section 2'},{id:'bad',title:'Unsafe URL',url:'javascript:attack()'}]},
    semantic_review:{status:'aligned',reason:'Matches the fixture',limitations:['No generalization beyond this statement']},proof_source:proof,
    source_library:{content:'-- fixed source fixture',source_sha256:'c'.repeat(64)},
    verification:{success:true,compilation_success:true,target_preserved:true,obligations_passed:true,target:'Fixture.identity',obligations:[{id:'identity',target:'Fixture.identity',ok:true},{id:'extra',target:'Fixture.extra',ok:true}],audit:{status:'passed'},print_axioms:{exit_code:0,stdout:'Fixture.identity depends on no axioms'}},
    source_application_status:'not_verified',verification_scope:'stored_contract_only',requires_new_proof:true,environment_fingerprint:'env-fixture',proof_sha256:'d'.repeat(64),contract_sha256:'e'.repeat(64),verification_sha256:'f'.repeat(64)};
  try{const view=Object.create(guided.Workspace.prototype);view.prose=(value,tag='p')=>view.el(tag,{},value);view.$=id=>doc.getElementById(id);view.openRun=async id=>opened.push(id);
    view.cb={api:async path=>{requests.push(path);return {mechanism:record};}};const box=view.$('workspace-mechanism-detail');box.focus=()=>{};box.scrollIntoView=()=>{};
    await view.openMechanism(record.id);const rendered=all(box),pres=rendered.filter(node=>node.tagName==='PRE');
    assert.deepEqual(requests,['/api/research/mechanisms/'+record.id]);assert.deepEqual(opened,[]);
    assert.ok(pres.some(node=>node.textContent===statement));assert.ok(pres.some(node=>node.textContent==='∀ n : Nat, n + 0 = n'));assert.ok(pres.some(node=>node.textContent===proof));assert.ok(pres.some(node=>node.textContent==='-- fixed source fixture'));
    for(const text of ['Все обязательства · 2','n is a natural number','Goedel','Section 2','Matches the fixture','No generalization beyond this statement','stored_contract_only','к исходной статье не подтверждена','нового доказательства','env-fixture'])assert.ok(box.textContent.includes(text),text);
    assert.equal(rendered.filter(node=>node.tagName==='A').length,1);assert.equal(rendered.find(node=>node.tagName==='A').attributes.href,'https://example.org/source');assert.equal(rendered.filter(node=>['IMG','SCRIPT'].includes(node.tagName)).length,0);assert.ok(box.textContent.includes('<img src=x onerror=attack()>'));assert.doesNotMatch(box.textContent,/undefined/);
    rendered.find(node=>node.tagName==='BUTTON'&&node.textContent==='Открыть исходное исследование').onclick();assert.deepEqual(opened,[record.provenance.run_id]);
    record.status='needs_recheck';await view.openMechanism(record.id);assert.match(box.textContent,/Окружение изменилось/);assert.doesNotMatch(box.textContent,/Сохранённый контракт проверен;/);
  }finally{global.document=originalDocument;}
});
