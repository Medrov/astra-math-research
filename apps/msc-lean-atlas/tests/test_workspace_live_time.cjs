'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),vm=require('node:vm');
const workspace=require('../web/research-workspace.js');
const snapshot=fields=>({id:'clock-run',title:'Clock fixture',purpose:'structure',status:'running',phase:'structure_rank',mode:'multi',updated_at:'unchanged',budget:{max_calls:16,timeout_seconds:1800},usage:{calls:3,total_tokens:41310,elapsed_seconds:0},...fields});

test('server live time is authoritative, including terminal finalization, without adding saved time twice',()=>{
  for(const status of ['queued','running','cancelling','complete','failed','cancelled']){
    const run=snapshot({status,live_elapsed_seconds:65.25,usage:{elapsed_seconds:20}}),before=JSON.stringify(run);
    assert.equal(workspace.elapsedSeconds(run),65.25);assert.equal(workspace.resourceUsage(run).seconds,65.25);assert.equal(JSON.stringify(run),before);
  }
  assert.equal(workspace.elapsedSeconds(snapshot({live_elapsed_seconds:0,usage:{elapsed_seconds:20}})),0);
  for(const live of [undefined,null,'65',NaN,Infinity,-Infinity,-1])assert.equal(workspace.elapsedSeconds(snapshot({live_elapsed_seconds:live,usage:{elapsed_seconds:54.406}})),54.406);
  assert.equal(workspace.elapsedSeconds(snapshot({usage:{elapsed_seconds:'unknown'}})),0);
  assert.equal(workspace.elapsedSeconds(snapshot({status:'complete',live_elapsed_seconds:84,usage:{elapsed_seconds:0}})),84);
  assert.equal(workspace.elapsedSeconds(snapshot({status:'complete',usage:{elapsed_seconds:84}})),84);
});

class Element{
  constructor(tag='div'){this.tagName=tag.toUpperCase();this.children=[];this.dataset={};this.attributes={};this.text='';this.classList={toggle(){},add(){},remove(){}};}
  append(...nodes){this.children.push(...nodes);}replaceChildren(...nodes){this.children=[];this.text='';this.append(...nodes);}setAttribute(name,value){this.attributes[name]=String(value);}
  removeAttribute(name){delete this.attributes[name];}
  set textContent(value){this.text=String(value);this.children=[];}get textContent(){return this.text+this.children.map(node=>node.textContent).join('');}
}
test('poll snapshots redraw elapsed seconds even when updated_at and saved usage stay unchanged',()=>{
  const nodes=new Map(),document={createElement:tag=>new Element(tag),getElementById(id){if(!nodes.has(id))nodes.set(id,new Element());return nodes.get(id);}},actions=[];
  const view=new workspace.Workspace({document,onStart:()=>actions.push('start'),onCancel:()=>actions.push('cancel')}),run=snapshot({live_elapsed_seconds:0});
  const display=()=>nodes.get('workspace-timeline').textContent;
  view.render(run);assert.match(display(),/0 с \/ 30 мин/);
  view.render({...run,live_elapsed_seconds:12.9});assert.match(display(),/12 с \/ 30 мин/);
  view.render({...run,live_elapsed_seconds:125.2});assert.match(display(),/2 мин 5 с \/ 30 мин/);
  view.render({...run,status:'complete',live_elapsed_seconds:126});assert.match(display(),/2 мин 6 с \/ 30 мин/);
  view.render({...run,status:'complete',live_elapsed_seconds:undefined,usage:{...run.usage,elapsed_seconds:126}});assert.match(display(),/2 мин 6 с \/ 30 мин/);
  assert.deepEqual(actions,[]);assert.equal(run.usage.elapsed_seconds,0);
});

test('the real guided parent forwards clock-only polls without rebuilding unrelated research content',async()=>{
  const nodes=new Map(),node=id=>{if(!nodes.has(id))nodes.set(id,new Element());return nodes.get(id);};
  const document={createElement:tag=>new Element(tag),getElementById:node,querySelectorAll:()=>[]};
  const context={document,URL,location:{href:'http://localhost/#research'}};context.window=context;vm.createContext(context);
  // Real browser exports, constructor and parent/child render methods. Only the
  // DOM platform and the backend-list transport are fixtures; no renderer mock.
  for(const file of ['research-workspace.js','guided-research.js'])vm.runInContext(fs.readFileSync(require.resolve('../web/'+file),'utf8'),context,{filename:file});
  const requests=[],actions=[],view=new context.GuidedResearch.Workspace({api:async route=>{requests.push(route);assert.equal(route,'/api/research/backends');return {default:'native',backends:[]};},action:action=>actions.push(action)});
  await Promise.resolve();
  const initial=snapshot({live_elapsed_seconds:1}),state={run:initial,runs:[{id:initial.id,status:initial.status,updated_at:initial.updated_at}]};
  const display=()=>node('workspace-timeline').textContent;
  view.render(state);assert.match(display(),/1 с \/ 30 мин/);
  const progressHeading=node('guided-progress').children[0];assert.ok(progressHeading);
  for(const [seconds,label]of [[21.8,/21 с \/ 30 мин/],[65.2,/1 мин 5 с \/ 30 мин/]]){
    state.run={...initial,live_elapsed_seconds:seconds};view.render(state);assert.match(display(),label);
    assert.equal(node('guided-progress').children[0],progressHeading);
  }
  state.run={...initial,status:'complete',live_elapsed_seconds:66.4};view.render(state);assert.match(display(),/1 мин 6 с \/ 30 мин/);
  state.run={...state.run,live_elapsed_seconds:undefined,usage:{...initial.usage,elapsed_seconds:66.4}};view.render(state);assert.match(display(),/1 мин 6 с \/ 30 мин/);
  state.run={...state.run,live_elapsed_seconds:-1,usage:{...initial.usage,elapsed_seconds:67.4}};view.render(state);assert.match(display(),/1 мин 7 с \/ 30 мин/);
  assert.equal(initial.updated_at,'unchanged');assert.equal(initial.usage.elapsed_seconds,0);assert.deepEqual(actions,[]);assert.deepEqual(requests,['/api/research/backends']);
});

test('the existing research heading uses the same live snapshot and saved fallback',()=>{
  const source=fs.readFileSync(require.resolve('../web/research.js'),'utf8'),heading=source.split('\n').find(line=>line.trim().startsWith('function renderRunHeading('));assert.ok(heading);
  const nodes=new Map(),node=id=>{if(!nodes.has(id))nodes.set(id,new Element());return nodes.get(id);},state={run:snapshot({live_elapsed_seconds:65.4}),purpose:'structure'};
  const context={state,$:node,label:value=>value,phaseIndex:()=>0,activeStates:new Set(['queued','running','cancelling']),document:{querySelectorAll:()=>[]},window:{ResearchWorkspaceView:workspace,GuidedResearch:{canRetry:()=>false}}};vm.createContext(context);vm.runInContext(heading,context);
  vm.runInContext('renderRunHeading()',context);assert.match(node('research-budget-status').textContent,/65 \/ 1800 с/);
  state.run={...state.run,status:'failed',live_elapsed_seconds:66.2};vm.runInContext('renderRunHeading()',context);assert.match(node('research-budget-status').textContent,/66 \/ 1800 с/);
  state.run={...state.run,live_elapsed_seconds:undefined,usage:{...state.run.usage,elapsed_seconds:66.2}};vm.runInContext('renderRunHeading()',context);assert.match(node('research-budget-status').textContent,/66 \/ 1800 с/);
});

test('collapsed process keeps stop reachable and retains a user expansion through clock polls',()=>{
  const nodes=new Map(),document={createElement:tag=>new Element(tag),getElementById(id){if(!nodes.has(id))nodes.set(id,new Element());return nodes.get(id);}},actions=[];
  const view=new workspace.Workspace({document,onCancel:()=>actions.push('cancel')});
  const run=snapshot({live_elapsed_seconds:1});view.render(run,null,{step:'connections'});
  const timeline=nodes.get('workspace-timeline'),process=timeline.children.find(node=>node.tagName==='DETAILS');
  assert.equal(process.open,false);
  const controls=timeline.children.find(node=>node!==process);
  controls.children.find(node=>node.tagName==='BUTTON'&&node.textContent==='Остановить и сохранить').onclick();
  assert.deepEqual(actions,['cancel']);
  process.open=true;view.render({...run,live_elapsed_seconds:2},null,{step:'connections'});
  assert.equal(timeline.children.find(node=>node.tagName==='DETAILS').open,true);
  view.render({...run,live_elapsed_seconds:2},null,{step:'source'});
  assert.equal(timeline.children.find(node=>node.tagName==='DETAILS').open,false);
  view.render({...run,id:'another',live_elapsed_seconds:0},null,{step:'connections'});
  assert.equal(timeline.children.find(node=>node.tagName==='DETAILS').open,false);
});

test('the result keeps its own verdict while source context retains the exact version and parent',()=>{
  const nodes=new Map(),document={createElement:tag=>new Element(tag),getElementById(id){if(!nodes.has(id))nodes.set(id,new Element());return nodes.get(id);}};
  const view=new workspace.Workspace({document}),run=snapshot({status:'failed',source_lineage:{version:2,parent_run_id:'parent'}});
  const descendants=node=>[node,...node.children.flatMap(descendants)];
  view.render(run,null,{step:'result'});let context=nodes.get('workspace-context');
  assert.equal(descendants(context).filter(node=>node.className==='workspace-status').length,0);
  assert.match(context.textContent,/Версия 2/);assert.match(context.textContent,/Предыдущая попытка/);
  view.render(run,null,{step:'source'});
  assert.equal(descendants(context).filter(node=>node.className==='workspace-status').length,1);
});
