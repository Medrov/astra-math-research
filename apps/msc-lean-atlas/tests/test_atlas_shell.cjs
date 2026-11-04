'use strict';
const test=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const vm=require('node:vm');

class Element{
  constructor(tag='div'){this.tagName=tag.toUpperCase();this.children=[];this.attributes={};this.dataset={};this.value='';this.hidden=false;this.clientWidth=600;this.text='';this.listeners={};this.classList={toggle(){}};}
  append(...nodes){this.children.push(...nodes);}replaceChildren(...nodes){this.children=[];this.text='';this.append(...nodes);}
  setAttribute(key,value){this.attributes[key]=String(value);if(key.startsWith('data-'))this.dataset[key.slice(5)]=String(value);}
  getAttribute(key){return this.attributes[key]??null;}
  addEventListener(type,fn){this.listeners[type]=fn;}
  scrollIntoView(){this.scrolled=true;}
  focus(){this.focused=true;}
  set textContent(value){this.text=String(value);this.children=[];}
  get textContent(){return this.text+this.children.map(n=>typeof n==='string'?n:n.textContent).join('');}
}
const descendants=node=>[node,...node.children.filter(n=>typeof n!=='string').flatMap(descendants)];
async function mount(wide=false){
  const nodes=new Map(),get=id=>{if(!nodes.has(id))nodes.set(id,new Element());return nodes.get(id);};
  get('research-selected').disabled=true; // Initial disabled attribute in index.html.
  const tabs=['map','research'].map(tab=>{const e=new Element('button');e.dataset.tab=tab;return e;}),skip=new Element('a'),brand=new Element('a');
  const document={getElementById:get,createElement:tag=>new Element(tag),createTextNode:text=>String(text),querySelectorAll:()=>tabs,querySelector:selector=>selector==='.brand'?brand:selector==='.workspace-skip'?skip:tabs.find(e=>selector.includes('"'+e.dataset.tab+'"'))};
  const graph={nodes:[{id:'11',code:'11',title:'Number theory',level:0},{id:'15',code:'15',title:'Linear algebra',level:0},{id:'11A',code:'11A',title:'Elementary number theory',level:1,parent_id:'11'},{id:'11A01',code:'11A01',title:'Divisibility',level:2,parent_id:'11A'}],edges:[],meta:{}};
  const requests=[],contexts=[],views=[],events={};
  class GraphView{constructor(){this.selected=null;views.push(this);}resize(){}select(id){this.selected=id;}navigate(id){this.selected=id;}}
  const context={document,URL,location:{href:'http://localhost/#map',hash:'#map'},history:{replaceState(){}},fetch:async path=>{requests.push(path);return {ok:true,json:async()=>graph};},requestAnimationFrame:()=>0,cancelAnimationFrame(){},ResizeObserver:class{observe(){}},MSCGraphView:GraphView,Event:class{},setTimeout,console};
  context.window=context;context.matchMedia=()=>({matches:wide});context.addEventListener=(name,fn)=>{events[name]=fn;};context.dispatchEvent=()=>{};
  context.ResearchWorkspace={show(){},hide(){},setContext:n=>contexts.push(n)};
  vm.createContext(context);vm.runInContext(fs.readFileSync(require.resolve('../web/app.js'),'utf8'),context);
  await new Promise(resolve=>setImmediate(resolve));
  return {get,tabs,skip,requests,contexts,views,context};
}

test('collapsed atlas catalog opens for search and child-list navigation even with an empty query',async()=>{
  const {get,views,requests}=await mount();
  assert.equal(get('catalog-results').hidden,true);assert.equal(get('catalog-toggle').getAttribute('aria-expanded'),'false');
  get('catalog-toggle').onclick();assert.equal(get('catalog-results').hidden,false);
  get('catalog-list').children.find(n=>n.dataset.msc==='11').onclick();
  get('catalog-toggle').onclick();assert.equal(get('catalog-results').hidden,true);
  descendants(get('category-panel')).find(n=>n.tagName==='BUTTON'&&n.textContent==='Показать список рубрик →').onclick();
  assert.equal(get('msc-search').value,'');assert.equal(get('catalog-results').hidden,false);
  assert.equal(get('catalog-heading').textContent,'В выбранном разделе');assert.equal(get('catalog-list').children[0].dataset.msc,'11A');
  get('msc-search').value='no match';get('msc-search').listeners.input();assert.equal(get('catalog-count').textContent,'0');assert.match(get('catalog-list').textContent,/Ничего не найдено/);
  get('msc-search').value='алгебра';get('msc-search').listeners.input();assert.equal(get('catalog-count').textContent,'1');assert.equal(get('catalog-list').children[0].dataset.msc,'15');
  get('show-roots').onclick();assert.equal(get('msc-search').value,'');assert.equal(get('catalog-count').textContent,'2');assert.equal(get('catalog-results').hidden,false);
  assert.equal(views.length,1,'catalog controls must not recreate the graph or its camera');assert.deepEqual(requests,['/api/graph']);
});

test('wide catalog starts open and atlas research action only transfers the selected context',async()=>{
  const {get,tabs,skip,views,requests,contexts}=await mount(true);
  assert.equal(get('catalog-results').hidden,false);assert.equal(skip.href,'#map-title');assert.equal(get('research-selected').disabled,true);
  get('msc-search').value='11A01';get('msc-search').listeners.input();get('catalog-list').children[0].onclick();
  assert.equal(get('research-selected').disabled,false);get('research-selected').onclick();
  assert.equal(contexts.length,1);assert.equal(contexts[0].code,'11A01');assert.equal(get('research-panel').hidden,false);assert.equal(skip.href,'#research-title');
  let prevented=false;skip.listeners.click({preventDefault(){prevented=true;}});assert.equal(prevented,true);assert.equal(get('research-title').focused,true);assert.equal(get('research-panel').hidden,false);
  tabs[0].onclick();assert.equal(get('map-panel').hidden,false);assert.equal(skip.href,'#map-title');
  assert.equal(views.length,1);assert.equal(views[0].selected,'11A01');assert.deepEqual(requests,['/api/graph']);
});
