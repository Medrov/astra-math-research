'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),vm=require('node:vm');
const workspace=require('../web/research-workspace.js'),guided=require('../web/guided-research.js');
const title='Подбор библиотечных лемм и импортов';
const snapshot=fields=>({id:'library-context',purpose:'prove',status:'running',phase:'library_context',active_stage:'formalize_transition',updated_at:'unchanged',
  draft_repair:{status:'typed',version:0,max_repairs:2},budget:{max_calls:16,timeout_seconds:1800},usage:{calls:2,elapsed_seconds:5},
  contract_verification:{kind:'lean_contract_preflight',status:'complete',target:'Bridge.goal',well_typed:true,proof_checked:false,audit:{status:'passed'}},...fields});

test('library preparation overrides its outer formalization stage without completing final types or starting proof',()=>{
  const run=snapshot(),before=JSON.stringify(run);
  assert.equal(guided.progressText(run),title);
  assert.deepEqual(workspace.stages(run).map(stage=>stage.state),['complete','active','pending','pending','pending','pending']);
  assert.equal(workspace.stages(run)[1].title,title);
  assert.equal(guided.formalEvidence(run),false);
  assert.equal(JSON.stringify(run),before);
  const unknown=snapshot({draft_repair:undefined,contract_verification:undefined});
  assert.deepEqual(workspace.stages(unknown).map(stage=>stage.state),['pending','active','pending','pending','pending','pending']);
});

test('interrupted library preparation stays stopped and a subsequent validated contract advances normally',()=>{
  for(const status of ['cancelled','budget_exhausted','failed']){
    const run=snapshot({status,termination:{code:status,stage:'library_context'}});
    assert.deepEqual(workspace.stages(run).map(stage=>stage.state),['complete','stopped','pending','pending','pending','pending']);
  }
  const next=snapshot({phase:'validate_contract',active_stage:'validate_contract',library_context:{input_sha256:'a'.repeat(64),receipt_sha256:'b'.repeat(64)}});
  assert.deepEqual(workspace.stages(next).map(stage=>stage.state),['complete','complete','active','pending','pending','pending']);
  assert.equal(workspace.stages(next)[1].title,'Типы Lean');
});

class Element{
  constructor(tag='div'){this.tagName=tag.toUpperCase();this.children=[];this.dataset={};this.attributes={};this.text='';this.classList={toggle(){},add(){},remove(){}};}
  append(...nodes){this.children.push(...nodes);}replaceChildren(...nodes){this.children=[];this.text='';this.append(...nodes);}setAttribute(name,value){this.attributes[name]=String(value);}
  removeAttribute(name){delete this.attributes[name];}
  set textContent(value){this.text=String(value);this.children=[];}get textContent(){return this.text+this.children.map(node=>node.textContent).join('');}
}

test('real parent render updates the library subphase and identifies accepted types as the baseline report',async()=>{
  const nodes=new Map(),node=id=>{if(!nodes.has(id))nodes.set(id,new Element());return nodes.get(id);};
  const document={createElement:tag=>new Element(tag),getElementById:node,querySelectorAll:()=>[]};
  const context={document,URL,location:{href:'http://localhost/#research'}};context.window=context;vm.createContext(context);
  for(const file of ['research-workspace.js','guided-research.js'])vm.runInContext(fs.readFileSync(require.resolve('../web/'+file),'utf8'),context,{filename:file});
  const requests=[],view=new context.GuidedResearch.Workspace({api:async route=>{requests.push(route);return {default:'native',backends:[]};}});
  await Promise.resolve();
  const initial=snapshot({phase:'lean_contract_preflight'}),state={run:initial,runs:[]};view.render(state);
  assert.doesNotMatch(node('guided-progress').textContent,new RegExp(title));
  state.run={...initial,phase:'library_context'};view.render(state);
  assert.match(node('guided-progress').textContent,new RegExp(title));
  assert.match(node('guided-progress').textContent,/относится к базовому черновику/);
  const descendants=element=>[element,...element.children.flatMap(descendants)];
  const stages=descendants(node('workspace-timeline')).find(child=>child.className==='workspace-stages');
  assert.equal(stages.children[1].dataset.state,'active');assert.match(stages.children[1].textContent,new RegExp(title));
  assert.ok(stages.children.slice(2).every(stage=>stage.dataset.state==='pending'));
  state.run={...state.run,phase:'validate_contract',active_stage:'validate_contract'};view.render(state);
  assert.doesNotMatch(node('guided-progress').textContent,/относится к базовому черновику/);
  assert.deepEqual(requests,['/api/research/backends']);
});
