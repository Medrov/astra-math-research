'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),vm=require('node:vm');
const checks=require('../web/candidate-checks.js'),objects=require('../web/object-graph.js');
const digest='a'.repeat(64),clone=value=>JSON.parse(JSON.stringify(value));
const snapshot=()=>({id:'partial-run',purpose:'structure',status:'budget_exhausted',phase:'budget_exhausted',updated_at:'unchanged',title:'Partial search',budget:{max_calls:16,timeout_seconds:1800},usage:{calls:8,elapsed_seconds:1800},
  termination:{code:'budget_exhausted',stage:'structure_candidates',message:'Исчерпан бюджет времени'},structure_profile:{summary:'Saved profile',objects:['X'],mechanism:'M',conclusion_shape:'C'},
  structure_routes:[{id:'route_1',msc_code:'16',status:'complete',candidates:[{transition_id:'bridge_1',title:'First',rank:1}],hits:[]},{id:'route_2',msc_code:'15',status:'complete',candidates:[{transition_id:'bridge_2',title:'Second',rank:1}],hits:[]},{id:'route_3',msc_code:'12',status:'searched',candidates:[],hits:[]}],
  partial_search:{status:'available',snapshot_sha256:digest,candidate_count:2,completed_route_ids:['route_1','route_2'],pending_route_ids:['route_3'],issues:[]}});
const graph=()=>({id:'partial-map',revision:1,title:'Partial map',msc_codes:['16','15'],objects:[{id:'input',title:'Input',definition:'X'},{id:'out_1',title:'First output',definition:'Y'},{id:'out_2',title:'Second output',definition:'Z'}],sources:[],transitions:[1,2].map(i=>({id:'bridge_'+i,title:'Bridge '+i,source_ids:['input'],target_ids:['out_'+i],claim:'X = X',construction:'Identity',assumptions:[],formulation_status:'candidate',status:'hypothesis'}))});
const materialized=run=>({...run,object_graph:graph(),partial_graph_ref:{id:'partial-map',revision:1},partial_search:{...run.partial_search,status:'materialized',graph_ref:{id:'partial-map',revision:1}}});
class Element{
  constructor(tag='div'){this.tagName=tag.toUpperCase();this.children=[];this.attributes={};this.dataset={};this.text='';this.classList={toggle(){},add(){},remove(){}};}
  append(...nodes){this.children.push(...nodes);}replaceChildren(...nodes){this.text='';this.children=[];this.append(...nodes);}setAttribute(key,value){this.attributes[key]=String(value);}removeAttribute(key){delete this.attributes[key];}
  set textContent(value){this.text=String(value);this.children=[];}get textContent(){return this.text+this.children.map(node=>node.textContent).join('');}
}
const all=node=>[node,...node.children.flatMap(all)];
function setup(options={}){
  const nodes=new Map(),node=id=>{if(!nodes.has(id))nodes.set(id,new Element());return nodes.get(id);},document={createElement:tag=>new Element(tag),getElementById:node,querySelectorAll:()=>[]};
  const context={document,URL,location:{href:'http://localhost/#research'}};context.window=context;vm.createContext(context);
  for(const file of ['object-graph.js','structure-search.js','research-workspace.js','guided-research.js'])vm.runInContext(fs.readFileSync(require.resolve('../web/'+file),'utf8'),context,{filename:file});
  const requests=[],loads=[],verifications=[],state={run:snapshot(),runs:[]};let view;
  const api=async(route,payload)=>{if(route==='/api/research/backends')return {default:'native',backends:[]};requests.push({route,payload});return options.api?options.api(route,payload):{run:materialized(state.run)};};
  view=new context.GuidedResearch.Workspace({api,load:async id=>{loads.push(id);state.run=materialized(state.run);view.render(state);return true;},action(){throw Error('Viewing partial candidates must not resume/cancel/prove');}});
  const structure=new context.StructureSearch.Workspace({onVerify:(g,t)=>verifications.push(objects.verificationPayload(g,t,{mode:'multi',budget:state.run.budget})),getRuns:()=>[]});
  return {context,node,requests,loads,verifications,state,view,structure};
}
test('terminal partial snapshot displays validated counts before opening and preserves stopped search after materialization',async()=>{
  const h=setup(),before=JSON.stringify(h.state.run);h.view.render(h.state);h.structure.render(h.state.run,true);
  assert.match(h.node('guided-current').textContent,/Сохранено 2 кандидатов из 2 завершённых направлений/);assert.match(h.node('guided-current').textContent,/2 \/ 3/);
  assert.match(h.node('structure-results').textContent,/сохранено кандидатов: 2/);assert.doesNotMatch(h.node('structure-results').textContent,/Кандидатов: 0|Кандидатов с сохранённой постановкой нет|Кандидат не предложен/);
  assert.match(h.node('structure-results').textContent,/Частичные кандидаты сохранены/);assert.match(h.node('structure-results').textContent,/Источники найдены; кандидаты не подготовлены/);
  const button=all(h.node('guided-current')).find(n=>n.tagName==='BUTTON'&&n.textContent==='Открыть найденные связи');assert.ok(button);assert.equal(h.requests.length,0);
  await button.onclick();assert.equal(JSON.stringify(snapshot()),before);assert.equal(h.state.run.status,'budget_exhausted');assert.equal(h.state.run.graph_ref,undefined);
  assert.equal(h.requests.length,1);assert.equal(h.requests[0].route,'/api/research/runs/partial-run/partial-candidates');assert.deepEqual(clone(h.requests[0].payload),{snapshot_sha256:digest});assert.deepEqual(h.loads,['partial-run']);
  assert.match(h.node('guided-current').textContent,/Частичная карта доступна/);assert.match(h.node('workspace-timeline').textContent,/Частично/);assert.match(h.node('workspace-timeline').textContent,/Остановлено/);
  assert.deepEqual(clone(h.context.ResearchWorkspaceView.stages(h.state.run).map(s=>s.state)),['complete','stopped','partial']);assert.notEqual(h.context.GuidedResearch.verdict(h.state.run).kind,'proved');
  h.structure.render(h.state.run,true);const cards=all(h.node('structure-results')).filter(n=>n.attributes['data-structure-candidate']);assert.equal(cards.length,2);
  const verify=all(cards[0]).find(n=>n.tagName==='BUTTON'&&n.textContent==='Проверить общую структуру в Lean');assert.equal(verify.disabled,false);verify.onclick();
  assert.equal(h.verifications.length,1);assert.equal(h.verifications[0].graph_id,'partial-map');assert.equal(h.verifications[0].graph_revision,1);assert.equal(h.verifications[0].transition_id,'bridge_1');
  const preview={graph_ref:{id:'partial-map',revision:1},candidates:[{transition_id:'bridge_1',eligible:true,status:'proposed'}]};const rows=checks.candidateRows(h.state.run,null,[],preview);assert.equal(rows.length,2);assert.equal(rows[0].eligible,true);assert.equal(rows[0].certificate,false);
});

test('partial opening prevents duplicate posts and ignores responses after run or digest changes',async()=>{
  for(const change of ['run','digest']){
    let resolve;const h=setup({api:()=>new Promise(done=>{resolve=done;})});h.view.render(h.state);const initial=h.state.run,pending=h.view.openPartial(initial);await h.view.openPartial(initial);assert.equal(h.requests.length,1);
    h.state.run={...snapshot(),...(change==='run'?{id:'new-run'}:{partial_search:{...initial.partial_search,snapshot_sha256:'b'.repeat(64)}})};h.view.render(h.state);const current=h.state.run;
    resolve({run:materialized(initial)});await pending;assert.deepEqual(h.loads,[]);assert.equal(h.state.run,current);assert.equal(h.state.run.object_graph,undefined);
  }
});

test('stale snapshot rejection retains terminal run and cannot fabricate or auto-open a graph',async()=>{
  const h=setup({api:async()=>{throw Error('Снимок изменился: обновите данные');}});h.view.render(h.state);const before=JSON.stringify(h.state.run);await h.view.openPartial(h.state.run);
  assert.deepEqual(h.loads,[]);assert.equal(JSON.stringify(h.state.run),before);assert.match(h.node('guided-current').textContent,/Снимок изменился/);assert.equal(h.state.run.object_graph,undefined);
  const retry=all(h.node('guided-current')).find(n=>n.textContent==='Открыть найденные связи');assert.equal(retry.disabled,false);
});

test('unavailable, active and empty snapshots cannot materialize; unmatched route artifacts never become verifiable candidates',async()=>{
  for(const fields of [{status:'running'},{partial_search:{...snapshot().partial_search,status:'unavailable',issues:['Повреждён route_2']}},{partial_search:{...snapshot().partial_search,candidate_count:0}},{partial_search:{...snapshot().partial_search,snapshot_sha256:'bad'}}]){
    const h=setup();h.state.run={...h.state.run,...fields};h.view.render(h.state);await h.view.openPartial(h.state.run);assert.equal(h.requests.length,0);assert.equal(h.context.StructureSearch.rankedCandidates(h.state.run).length,0);
  }
  const h=setup();h.state.run.partial_search.candidate_count=1;h.state.run.partial_search.issues=['route_2 исключён проверкой'];h.view.render(h.state);h.structure.render(h.state.run,true);
  assert.match(h.node('structure-results').textContent,/сохранено кандидатов: 1/);assert.doesNotMatch(h.node('structure-results').textContent,/Кандидатов: [12]/);assert.match(h.node('guided-current').textContent,/route_2 исключён проверкой/);
});

const busyPartial=()=>({status:'unavailable',candidate_count:0,completed_route_ids:[],pending_route_ids:[],issues:[{code:'active_run',message:'Частичные кандидаты доступны после остановки процесса поиска.'}]});
test('continuation partial counts remain local even when its inherited atlas overview has a candidate',()=>{
  const h=setup();h.state.run={...snapshot(),status:'cancelled',contract:{atlas_seed:{parent_run_id:'parent'}},atlas_summary:{candidates_found:1,deep_completed:1},partial_search:{...snapshot().partial_search,candidate_count:0,completed_route_ids:[],pending_route_ids:['next']}};h.view.render(h.state);h.structure.render(h.state.run,true);
  assert.match(h.node('guided-current').textContent,/В этой попытке сохранено 0 кандидатов из 0/);assert.match(h.node('structure-results').textContent,/В этой попытке сохранено кандидатов: 0/);assert.doesNotMatch(h.node('guided-current').textContent,/Сохранено 1|сохранено 1/);assert.equal(h.requests.length,0);
});
test('an unstarted continuation draft never claims a partial stop or zero results and needs explicit search start',async()=>{
  const h=setup(),actions=[];h.state.run={...snapshot(),id:'9cf336f3ea73641cad44fee96b02d88a',status:'draft',phase:'draft',ready_to_start:true,usage:{calls:0,total_tokens:0,elapsed_seconds:0},termination:null,partial_search:busyPartial()};
  h.view.cb.action=action=>actions.push(action);h.view.render(h.state);h.structure.render(h.state.run,true);
  for(const id of ['guided-current','structure-results','guided-result'])assert.doesNotMatch(h.node(id).textContent,/Поиск остановлен|сохранено кандидатов: 0|Сохранено 0|после остановки|На карте сохранено переходов: 0/i);
  assert.equal(h.context.GuidedResearch.partialSearchInfo(h.state.run),null);assert.equal(h.context.GuidedResearch.partialSearchFinalizing(h.state.run),false);assert.match(h.node('structure-results').textContent,/ещё не запускался/);assert.deepEqual(actions,[]);assert.equal(h.requests.length,0);await h.view.openPartial(h.state.run);assert.equal(h.requests.length,0);
  const start=all(h.node('workspace-timeline')).find(n=>n.tagName==='BUTTON'&&n.textContent==='Продолжить поиск');assert.ok(start);start.onclick();assert.deepEqual(actions,['resume']);
});

function pollingController(h,replies){
  const timers=new Map();let next=0;const requests=[],errors=[],state=h.state;state.visible=true;state.polling=false;
  const source=fs.readFileSync(require.resolve('../web/research.js'),'utf8'),functions=source.split('\n').filter(line=>/^\s*(?:async )?function (schedulePoll|pollRun)\(/.test(line)).join('\n');
  const context={state,window:{GuidedResearch:h.context.GuidedResearch},activeStates:new Set(['queued','running','cancelling']),setTimeout(fn,ms){assert.equal(ms,1800);timers.set(++next,fn);return next;},clearTimeout(id){timers.delete(id);},api:async path=>{requests.push(path);return {run:replies()};},syncHistory(){},render(){h.view.render(state);h.structure.render(state.run,true);},objectWorkspace:{refreshLibrary(){}},error:message=>errors.push(message)};
  vm.createContext(context);vm.runInContext(functions,context);return {state,timers,requests,errors,schedule:()=>vm.runInContext('schedulePoll()',context),refresh:()=>vm.runInContext('state.partialPoll=null;pollRun()',context),async tick(){const entry=timers.entries().next().value;assert.ok(entry,'Expected a scheduled GET');timers.delete(entry[0]);await entry[1]();}};
}
test('actual polling follows running to terminal cleanup to available candidates without displaying the placeholder zero',async()=>{
  const h=setup(),busy={...snapshot(),status:'cancelled',partial_search:busyPartial()},ready={...snapshot(),status:'cancelled',partial_search:{...snapshot().partial_search,candidate_count:1,completed_route_ids:['atlas_global_unclassified'],pending_route_ids:['next']}};h.state.run={...snapshot(),status:'running'};const replies=[busy,ready],poll=pollingController(h,()=>replies.shift());poll.schedule();await poll.tick();
  assert.equal(poll.state.run.status,'cancelled');assert.equal(poll.timers.size,1);assert.match(h.node('guided-current').textContent,/Сохраняем результаты поиска/);for(const id of ['guided-current','guided-result','structure-results'])assert.doesNotMatch(h.node(id).textContent,/Сохранено 0|сохранено кандидатов: 0|сохранено переходов: 0/i);assert.equal(h.context.GuidedResearch.partialSearchInfo(busy),null);
  await poll.tick();assert.equal(poll.timers.size,0);assert.equal(poll.requests.length,2);assert.match(h.node('guided-current').textContent,/Сохранено 1 кандидатов из 1/);assert.match(h.node('structure-results').textContent,/сохранено кандидатов: 1/);const open=all(h.node('guided-current')).find(n=>n.tagName==='BUTTON'&&n.textContent==='Открыть найденные связи');assert.ok(open);assert.notEqual(open.disabled,true);assert.deepEqual(poll.errors,[]);
});
test('terminal cleanup polling is bounded, manually refreshable and never runs for a fresh draft',async()=>{
  const h=setup();h.state.run={...snapshot(),status:'cancelled',partial_search:busyPartial()};const poll=pollingController(h,()=>h.state.run);h.view.cb.refresh=poll.refresh;h.view.render(h.state);poll.schedule();for(let i=0;i<10;i++)await poll.tick();assert.equal(poll.requests.length,10);assert.equal(poll.timers.size,0);
  const refresh=all(h.node('guided-current')).find(n=>n.tagName==='BUTTON'&&n.textContent==='Обновить результаты поиска');assert.ok(refresh);await refresh.onclick();assert.equal(poll.requests.length,11);assert.equal(poll.timers.size,1);
  h.state.run={...h.state.run,id:'fresh-draft',status:'draft',phase:'draft',ready_to_start:true};poll.schedule();assert.equal(poll.timers.size,0);assert.equal(h.context.GuidedResearch.partialSearchFinalizing(h.state.run),false);
});
