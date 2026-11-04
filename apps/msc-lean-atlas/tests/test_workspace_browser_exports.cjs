'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');

// Browser platform surface only. Modules, exports, startup and dialog caller run unmodified.
class Element{
  constructor(tag='div'){this.tagName=tag.toUpperCase();this.children=[];this.attributes={};this.dataset={};this.text='';this.value='';this.classList={toggle(){},add(){},remove(){}};}
  append(...nodes){this.children.push(...nodes);}prepend(...nodes){this.children.unshift(...nodes);}replaceChildren(...nodes){this.children=[];this.text='';this.append(...nodes);}
  setAttribute(key,value){this.attributes[key]=String(value);}get textContent(){return this.text+this.children.map(node=>node.textContent).join('');}set textContent(value){this.text=String(value);this.children=[];}
  addEventListener(){}querySelectorAll(){return [];}focus(){}scrollIntoView(){}showModal(){this.open=true;}close(){this.open=false;this.onclose?.();}remove(){}
}
const all=node=>[node,...node.children.flatMap(all)];
test('browser script order preserves both the app controller and view exports, and the actual revision dialog compares Lean types',async()=>{
  const root=path.resolve(__dirname,'../web'),nodes=new Map(),node=id=>{if(!nodes.has(id))nodes.set(id,new Element());return nodes.get(id);};
  const document={body:new Element('body'),createElement:tag=>new Element(tag),getElementById:node,querySelector:node,querySelectorAll:()=>[]};
  const oldType='∀ (f : Nat → Nat) (n : Nat), Function.iterate f n = Function.iterate f n',newType=oldType.replaceAll('Function.iterate','Nat.iterate');
  const previous={id:'previous',source_card:{title:'Iteration bridge',formal_statement:oldType}},current={id:'current',source_lineage:{parent_run_id:'previous',reason:'Resolve the pinned library name'},source_card:{title:'Iteration bridge',formal_statement:newType}};
  const requests=[],backends={default:'native',backends:[{id:'native',title:'SHAIM',available:true,description:'Native'}]};
  const transport=async route=>{requests.push(route);if(route==='/api/research/backends')return backends;if(route==='/api/research/runs/previous')return {run:previous};throw Error('Unexpected request: '+route);};
  const context={document,URL,location:{href:'http://localhost/#research',hash:'#research'},ResizeObserver:class{observe(){}},addEventListener(){},fetch:async route=>({ok:true,json:()=>transport(route)}),setTimeout,clearTimeout};context.window=context;
  vm.createContext(context);
  const required=new Set(['object-graph.js','structure-search.js','research-workspace.js','guided-research.js','research.js']);
  const order=[...fs.readFileSync(path.join(root,'index.html'),'utf8').matchAll(/<script\b[^>]*\bsrc="\/([^"?]+)[^"]*"/g)].map(match=>match[1]).filter(file=>required.has(file));
  assert.equal(order.length,required.size);
  for(const file of order)vm.runInContext(fs.readFileSync(path.join(root,file),'utf8'),context,{filename:file});
  assert.equal(typeof context.ResearchWorkspace.show,'function');assert.equal(typeof context.ResearchWorkspace.hide,'function');
  assert.equal(typeof context.ResearchWorkspaceView.Workspace,'function');assert.equal(typeof context.ResearchWorkspaceView.compareCards,'function');assert.notEqual(context.ResearchWorkspace,context.ResearchWorkspaceView);
  const view=new context.GuidedResearch.Workspace({api:transport});assert.ok(view.workspace instanceof context.ResearchWorkspaceView.Workspace);
  await view.compareRevision(current);
  const dialog=document.body.children.find(node=>node.tagName==='DIALOG');assert.equal(dialog.open,true);assert.doesNotMatch(dialog.textContent,/Не удалось загрузить|is not a function/);
  const pres=all(dialog).filter(node=>node.tagName==='PRE');assert.ok(pres.some(node=>node.textContent===oldType));assert.ok(pres.some(node=>node.textContent===newType));assert.match(dialog.textContent,/Тип Lean/);assert.match(dialog.textContent,/Resolve the pinned library name/);
  assert.equal(requests.filter(route=>route==='/api/research/runs/previous').length,1);assert.ok(requests.every(route=>!route.endsWith('/resume')));
});
