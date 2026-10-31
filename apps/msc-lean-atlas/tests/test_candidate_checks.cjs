const {test}=require('node:test');
const assert=require('node:assert/strict');
const m=require('../web/candidate-checks.js');

class Element{
  constructor(tag,doc){this.tagName=tag.toUpperCase();this.ownerDocument=doc;this.children=[];this.dataset={};this.attributes={};this._text='';this.hidden=false;}
  setAttribute(k,v){this.attributes[k]=String(v);}
  append(...nodes){for(const n of nodes){n.remove();n.parentNode=this;this.children.push(n);}}
  replaceChildren(...nodes){for(const n of this.children)n.parentNode=null;this.children=[];this._text='';this.append(...nodes);}
  remove(){if(this.parentNode){this.parentNode.children=this.parentNode.children.filter(n=>n!==this);this.parentNode=null;}}
  set textContent(v){this.replaceChildren();this._text=String(v);}
  get textContent(){return this._text+this.children.map(n=>n.textContent).join('');}
  focus(){this.ownerDocument.activeElement=this;}
}
const descendants=n=>[n,...n.children.flatMap(descendants)],tick=()=>new Promise(resolve=>setImmediate(resolve));
function graph(){return {id:'G',revision:2,objects:[{id:'x',title:'X',msc_codes:['13']},{id:'y',title:'Y'}],transitions:['a','b','c'].map(id=>({id,title:'Связь '+id,claim:'Исходное утверждение '+id,semantic_hash:'hash-'+id,status:'proposed',formulation_status:'candidate',agent_task:null,obligations:[],source_ids:['x'],target_ids:['y']}))};}
function preview(g,budget=m.perItemBudget(),overrides={}){const candidates=g.transitions.map(t=>({transition_id:t.id,title:t.title,eligible:true,status:'proposed',...overrides[t.id]})),n=candidates.filter(t=>t.eligible).length;return {graph_ref:{id:g.id,revision:g.revision},graph_sha256:'snapshot',candidates,aggregate:{selected:3,eligible:n,skipped:3-n,max_calls:n*budget.max_calls,timeout_seconds:n*budget.timeout_seconds,max_parallel_runs:1}};}
function certified(g){const t=g.transitions[0];Object.assign(t,{status:'proved',formulation_status:'formalized',agent_task:{target:'Goal.a'},semantic_review:{status:'aligned'}});t.certificate={graph_id:g.id,revision:g.revision,transition_id:t.id,semantic_hash:t.semantic_hash,run_id:'cert',result:{verification:{target:'Goal.a',success:true,compilation_success:true,target_preserved:true,obligations_passed:true,audit:{status:'passed'}}}};return t;}
function fixture(handler){const doc={createElement(tag){return new Element(tag,this);}},container=doc.createElement('div'),calls=[],actions=[],errors=[],g=graph();const api=async(path,body)=>{calls.push({path,body});if(handler){const result=handler(path,body,g);if(result!==undefined)return result;}if(path==='/api/research/batches/preview')return preview(g,body.budget);if(path.startsWith('/api/research/batches?'))return {batches:[]};if(path==='/api/research/batches')return {id:'B',status:'complete',graph_ref:{id:g.id,revision:g.revision},items:[],aggregate:{max_calls:48,timeout_seconds:5400}};throw Error('Unexpected '+path);};const workspace=new m.Workspace({container,api,onSelect:(...args)=>actions.push(['select',...args]),onVerify:(...args)=>actions.push(['verify',...args]),onOpenRun:id=>actions.push(['open',id]),onError:e=>errors.push(e)});return {workspace,doc,container,calls,actions,errors,g};}

test('current certificate requires exact graph, revision, transition, hash, target and verifier',()=>{
  const g=graph();certified(g);assert.equal(m.candidateRows(null,g)[0].status,'proved');
  for(const change of [t=>t.certificate.revision=1,t=>t.certificate.graph_id='foreign',t=>t.certificate.transition_id='b',t=>t.certificate.semantic_hash='old',t=>t.certificate.result.verification.target='Other',t=>t.certificate.result.verification.audit.status='failed']){const copy=structuredClone(g);change(copy.transitions[0]);assert.notEqual(m.candidateRows(null,copy)[0].status,'proved');}
  const copy=structuredClone(g);copy.transitions[0].semantic_review.status='uncertain';assert.equal(m.candidateRows(null,copy)[0].status,'formal_only');
});
test('history parent lineage and same id at foreign revision never certify a candidate',()=>{
  const g=graph(),before=JSON.stringify(g),runs=[{id:'old',purpose:'prove',status:'complete',outcome:'proved',selected_transition_id:'a',graph_ref:{id:'G',revision:1}},{id:'derived',purpose:'prove',status:'complete',outcome:'proved',selected_transition_id:'b',graph_ref:{id:'Child',revision:1},source_graph_ref:{id:'G',revision:2}}];
  const rows=m.candidateRows(null,g,runs);assert.equal(rows[0].attempt,undefined);assert.equal(rows[1].attempt.derived,true);assert.notEqual(rows[1].status,'proved');assert.match(rows[1].label,/производной/);assert.equal(JSON.stringify(g),before);
});
test('authoritative invalid contract requires correction; historical exact evidence is neutral',()=>{
  const g=graph(),p=preview(g,m.perItemBudget(),{a:{eligible:false,status:'invalid_contract',run_id:'bad',reason:'Compiler rejected type'},b:{eligible:false,status:'historical_exact_evidence',run_id:'exact-other',reason:'Exact evidence in another graph'}}),rows=m.candidateRows(null,g,[],p);
  assert.equal(rows[0].needsContract,true);assert.equal(rows[0].eligible,false);assert.equal(rows[0].runId,'bad');assert.match(rows[0].label,/исправленная постановка/);assert.equal(rows[1].certificate,false);assert.notEqual(rows[1].status,'proved');assert.equal(rows[2].eligible,true);
});
test('scope review before Lean is distinct from a rejected formal contract',()=>{
  const g=graph(),p=preview(g,m.perItemBudget(),{a:{eligible:false,status:'invalid_contract',termination:{code:'invalid_contract',stage:'lean_contract_preflight'}},b:{eligible:false,status:'needs_review',termination:{code:'needs_review',stage:'formalize_transition'}},c:{eligible:false,status:'needs_review',termination:{code:'needs_review',stage:'semantic_review'}}}),rows=m.candidateRows(null,g,[],p);
  assert.equal(rows[0].label,'Нужна исправленная постановка');assert.equal(rows[1].label,'Нужно уточнить объём задачи');assert.match(rows[1].correctionExplanation,/Lean ещё не проверил этот кандидат/);assert.equal(rows[1].eligible,false);assert.doesNotMatch(rows[2].correctionExplanation,/Lean ещё не проверил/);
});
test('a failed derived formulation does not reject the source candidate when preview allows retry',()=>{
  const g=graph(),run={id:'derived',purpose:'prove',status:'failed',selected_transition_id:'a',graph_ref:{id:'Child',revision:1},source_graph_ref:{id:'G',revision:2},termination:{code:'invalid_contract'},requires_review:true};
  const p=preview(g,m.perItemBudget(),{a:{eligible:true,status:'not_proved',run_id:run.id,termination:run.termination}}),row=m.candidateRows(null,g,[run],p)[0];
  assert.equal(row.attempt.derived,true);assert.equal(row.needsContract,false);assert.equal(row.eligible,true);assert.equal(row.hasFailure,true);assert.equal(row.runId,'derived');
  assert.equal(m.candidateRows(null,g,[run])[0].needsContract,false);
  const direct={...run,graph_ref:{id:'G',revision:2},source_graph_ref:null};g.transitions[0].agent_task={target:'Goal.a'};
  assert.equal(m.candidateRows(null,g,[direct])[0].needsContract,true);
  assert.equal(m.candidateRows(null,g,[direct],preview(g,m.perItemBudget(),{a:{eligible:false,status:'invalid_contract'}}))[0].eligible,false);
});
test('certificate environment conflicts fail closed and successful history opens the proof',()=>{
  const g=graph(),t=certified(g);g.environment_fingerprint='current';t.certificate.environment_fingerprint='current';t.certificate.result.verification.environment_fingerprint='old';assert.equal(m.certificateValid(g,t),false);t.certificate.result.verification.environment_fingerprint='current';assert.equal(m.certificateValid(g,t),true);
  g.active_environment_fingerprint='new';assert.equal(m.certificateValid(g,t),false);t.certificate.environment_fingerprint='new';t.certificate.result.verification.environment_fingerprint='new';assert.equal(m.certificateValid(g,t),true);
  const p=preview(g,m.perItemBudget(),{b:{eligible:false,status:'historical_exact_evidence',run_id:'success',termination:{code:'complete'}}});assert.equal(m.candidateRows(null,g,[],p)[1].hasFailure,false);
});
test('render and navigation only request read/preview, never launch or mutate history',async()=>{
  const f=fixture(),history=[{id:'old',purpose:'prove',selected_transition_id:'a',graph_ref:{id:'G',revision:1},status:'failed'}],before=JSON.stringify([f.g,history]);
  try{f.workspace.render(null,f.g,history);await tick();assert.ok(f.calls.some(c=>c.path.endsWith('/preview')));assert.equal(f.calls.filter(c=>c.body&&c.path!=='/api/research/batches/preview').length,0);const map=descendants(f.container).find(n=>n.tagName==='BUTTON'&&n.textContent==='На карте');await map.onclick();assert.equal(f.actions[0][0],'select');assert.equal(f.actions[0][1],f.g);assert.equal(f.actions[0][2],f.g.transitions[0]);assert.equal(JSON.stringify([f.g,history]),before);}finally{f.workspace.destroy();}
});
test('MSC codes stay compact while provenance and full titles remain in a closed disclosure',async()=>{
  const f=fixture();try{f.workspace.render(null,f.g);await tick();const card=f.workspace.cards.children[0],details=card.children.find(n=>n.tagName==='DETAILS');assert.ok(details);assert.notEqual(details.open,true);assert.equal(details.children[0].textContent,'Рубрики MSC2020 · 13');assert.ok(details.textContent.includes(f.workspace.rows[0].msc.label));for(const item of f.workspace.rows[0].msc.items)assert.ok(details.textContent.includes(item.code+' — '+item.title));assert.equal(f.workspace.summary.textContent,'Связей: 3 · Проверены в этой версии: 0 · Доступны: 3');}finally{f.workspace.destroy();}
});
test('only the exact active batch overlays queued/running candidates without mutating the graph or preview',()=>{
  const g=graph(),p=preview(g),batch={id:'B',status:'running',graph_ref:{id:'G',revision:2},items:[{transition_id:'a',status:'running',run_id:'child'},{transition_id:'b',status:'queued'}]},before=JSON.stringify([g,p,batch]);
  const rows=m.candidateRows(null,g,[],p,batch);assert.equal(rows[0].status,'checking');assert.equal(rows[0].runId,'child');assert.equal(rows[0].eligible,false);assert.match(rows[1].label,/очереди/);assert.equal(rows[1].eligible,false);assert.equal(rows[2].eligible,true);assert.equal(JSON.stringify([g,p,batch]),before);
  const foreign={...batch,graph_ref:{id:'G',revision:1}};assert.equal(m.candidateRows(null,g,[],p,foreign)[0].eligible,true);assert.notEqual(m.candidateRows(null,g,[],p,foreign)[0].status,'checking');
  assert.equal(m.candidateRows(null,g,[],p,{...batch,status:'complete'})[0].eligible,true);
});
test('a completed queue entry does not imply a proof and preserves review or contract failures',()=>{
  assert.equal(m.batchItemLabel({status:'complete',outcome:'unknown'}),'Вывод не установлен');assert.equal(m.batchItemLabel({status:'complete',outcome:'unknown',termination:{code:'needs_review'}}),'Нужно уточнить постановку');assert.equal(m.batchItemLabel({status:'failed',termination:{code:'invalid_contract'}}),'Постановка не принята');assert.equal(m.batchItemLabel({status:'complete',outcome:'proved'}),'Есть результат проверки');
});
test('polling cloned data keeps buttons bound to current transition and prevents duplicate verify',async()=>{
  const f=fixture();let release;f.workspace.onVerify=(...args)=>{f.actions.push(args);return new Promise(resolve=>{release=resolve;});};
  try{f.workspace.render(null,f.g);await tick();const button=descendants(f.container).find(n=>n.tagName==='BUTTON'&&n.textContent==='Проверить связь'),copy=structuredClone(f.g);f.workspace.render(null,copy);const first=button.onclick(),second=button.onclick();await tick();assert.equal(f.actions.length,1);assert.equal(f.actions[0][0],copy);assert.equal(f.actions[0][1],copy.transitions[0]);release();await Promise.all([first,second]);}finally{f.workspace.destroy();}
});
test('batch review displays aggregate limits and creates only after explicit confirm',async()=>{
  const f=fixture();try{f.workspace.render(null,f.g);await tick();await f.workspace.openReview();assert.match(f.workspace.review.textContent,/48 вызовов и 90 минут/);assert.equal(f.calls.filter(c=>c.path==='/api/research/batches').length,0);await f.workspace.startBatch();const create=f.calls.find(c=>c.path==='/api/research/batches');assert.deepEqual(create.body.transition_ids,['a','b','c']);assert.equal(create.body.budget.max_calls,16);assert.equal(create.body.budget.timeout_seconds,1800);assert.ok(create.body.idempotency_key);assert.equal(create.body.graph_revision,2);}finally{f.workspace.destroy();}
});
test('uncertain batch create retries the identical key and body; concurrent click is a no-op',async()=>{
  let release,number=0;const f=fixture((path,body)=>{if(path==='/api/research/batches'){number++;if(number===1)return new Promise((resolve,reject)=>{release=()=>reject(Error('Connection lost'));});return {id:'same-server-batch',status:'complete',graph_ref:{id:'G',revision:2},items:[]};}});
  try{f.workspace.render(null,f.g);await tick();await f.workspace.openReview();const pending=f.workspace.startBatch();await f.workspace.startBatch();assert.equal(number,1);release();await pending;assert.equal(f.workspace.pending,false);await f.workspace.startBatch();assert.equal(number,2);const requests=f.calls.filter(c=>c.path==='/api/research/batches');assert.deepEqual(requests[0].body,requests[1].body);assert.equal(f.workspace.batch.id,'same-server-batch');}finally{f.workspace.destroy();}
});
test('a definite HTTP 400 rejection releases the payload but requires a new reviewed preview',async()=>{
  let creates=0;const f=fixture(path=>{if(path==='/api/research/batches'&&++creates===1)return Promise.reject(Object.assign(Error('Snapshot changed'),{status:400}));});
  try{f.workspace.render(null,f.g);await tick();await f.workspace.openReview();await f.workspace.startBatch();assert.equal(f.workspace.requestPayload,null);assert.equal(f.workspace.reviewDirty,true);assert.match(f.workspace.error.textContent,/Обновите список/);await f.workspace.startBatch();assert.equal(creates,1);await f.workspace.openReview();await f.workspace.startBatch();assert.equal(creates,2);const requests=f.calls.filter(c=>c.path==='/api/research/batches');assert.notEqual(requests[0].body.idempotency_key,requests[1].body.idempotency_key);}finally{f.workspace.destroy();}
});
test('retry after a terminal batch re-previews eligibility and creates a distinct batch',async()=>{
  let created=0;const f=fixture((path,body,g)=>{if(path==='/api/research/batches/preview'&&created)return preview(g,body.budget,{a:{eligible:false,status:'invalid_contract'},c:{eligible:false,status:'verified'}});if(path==='/api/research/batches'){created++;return {id:'batch-'+created,status:'failed',graph_ref:{id:'G',revision:2},items:[]};}});
  try{f.workspace.render(null,f.g);await tick();await f.workspace.openReview();await f.workspace.startBatch();await f.workspace.openReview();await f.workspace.startBatch();const requests=f.calls.filter(c=>c.path==='/api/research/batches');assert.equal(requests.length,2);assert.deepEqual(requests[1].body.transition_ids,['b']);assert.notEqual(requests[0].body.idempotency_key,requests[1].body.idempotency_key);}finally{f.workspace.destroy();}
});
test('uncertain create keeps the approved list and budget frozen across background refresh and reopen',async()=>{
  let uncertain=false;const f=fixture((path,body,g)=>{if(path==='/api/research/batches'){uncertain=true;return Promise.reject(Error('No response'));}if(path.endsWith('/preview')&&uncertain)return preview(g,body.budget,{a:{eligible:false},b:{eligible:false}});});
  try{f.workspace.render(null,f.g);await tick();await f.workspace.openReview();await f.workspace.startBatch();const approved=JSON.stringify(f.workspace.preview),count=f.calls.length;f.workspace.reviewOpen=false;await f.workspace.refreshPreview();await f.workspace.openReview();assert.equal(f.calls.length,count);assert.equal(JSON.stringify(f.workspace.preview),approved);assert.deepEqual(f.workspace.requestPayload.transition_ids,['a','b','c']);assert.equal(f.workspace.reviewOpen,true);assert.match(f.workspace.review.textContent,/48 вызовов и 90 минут/);}finally{f.workspace.destroy();}
});
test('cancel is explicit and idempotent while pending; suspend does not cancel server work',async()=>{
  let release;const f=fixture((path)=>{if(path.endsWith('/cancel'))return new Promise(resolve=>{release=()=>resolve({id:'B',status:'cancelled',graph_ref:{id:'G',revision:2},items:[],cancel_requested:true});});if(path.startsWith('/api/research/batches?'))return {batches:[{id:'B',status:'running',graph_ref:{id:'G',revision:2},items:[{transition_id:'a',title:'A',status:'running'}]}]};});
  try{f.workspace.render(null,f.g);await tick();f.workspace.suspend();assert.equal(f.calls.filter(c=>c.path.endsWith('/cancel')).length,0);const pending=f.workspace.cancelBatch();await f.workspace.cancelBatch();assert.equal(f.calls.filter(c=>c.path.endsWith('/cancel')).length,1);release();await pending;assert.equal(f.workspace.batch.status,'cancelled');assert.equal(f.workspace.suspended,true);}finally{f.workspace.destroy();}
});
test('changed budget cannot start before the aggregate is recalculated',async()=>{
  const f=fixture();try{f.workspace.render(null,f.g);await tick();await f.workspace.openReview();const input=descendants(f.workspace.review).find(n=>n.tagName==='INPUT');input.value='8';input.oninput();await f.workspace.startBatch();assert.equal(f.calls.filter(c=>c.path==='/api/research/batches').length,0);const recalc=descendants(f.workspace.review).find(n=>n.tagName==='BUTTON'&&n.textContent.startsWith('Пересчитать'));await recalc.onclick();assert.equal(f.workspace.preview.aggregate.max_calls,24);await f.workspace.startBatch();assert.equal(f.calls.find(c=>c.path==='/api/research/batches').body.budget.max_calls,8);}finally{f.workspace.destroy();}
});
test('foreign preview and empty eligibility cannot produce a batch payload',()=>{
  const g=graph(),p=preview(g);assert.throws(()=>m.batchPayload(g,{...p,graph_ref:{id:'G',revision:1}},m.perItemBudget(),'key'));assert.throws(()=>m.batchPayload(g,preview(g,m.perItemBudget(),{a:{eligible:false},b:{eligible:false},c:{eligible:false}}),m.perItemBudget(),'key'));assert.throws(()=>m.perItemBudget(25,30));
});
