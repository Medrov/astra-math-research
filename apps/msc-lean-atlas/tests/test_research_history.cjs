const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const history=require('../web/research-history.js');

// Minimal native DOM surface. The actual Workspace and its registered handlers
// run unchanged; no API, browser, model or theorem verifier is substituted.
class Element {
  constructor(tag,doc){this.tagName=tag.toUpperCase();this.ownerDocument=doc;this.children=[];this.parentNode=null;this.attributes={};this.dataset={};this.listeners=new Map();this.value='';this.hidden=false;this.open=false;this.scrollTop=0;this._text='';}
  setAttribute(name,value){this.attributes[name]=String(value);}
  getAttribute(name){return this.attributes[name]??null;}
  removeAttribute(name){delete this.attributes[name];}
  append(...items){for(const item of items)this.insertBefore(item,null);}
  insertBefore(item,before){if(item===before)return;item.remove();const index=before?this.children.indexOf(before):this.children.length;if(index<0)throw Error('Missing insertion point');this.children.splice(index,0,item);item.parentNode=this;}
  remove(){if(this.parentNode){this.parentNode.children.splice(this.parentNode.children.indexOf(this),1);this.parentNode=null;}}
  get isConnected(){return this===this.ownerDocument.body||!!this.parentNode?.isConnected;}
  get textContent(){return this._text+this.children.map(child=>child.textContent).join('');}
  set textContent(value){for(const child of this.children)child.parentNode=null;this.children=[];this._text=String(value);}
  addEventListener(type,handler){if(!this.listeners.has(type))this.listeners.set(type,[]);this.listeners.get(type).push(handler);}
  dispatch(type,extra={}){const event={target:this,defaultPrevented:false,preventDefault(){this.defaultPrevented=true;},...extra};for(const handler of this.listeners.get(type)||[])handler(event);return event;}
  focus(){this.ownerDocument.activeElement=this;}
  showModal(){this.open=true;this.modalCalls=(this.modalCalls||0)+1;}
  close(){this.open=false;this.dispatch('close');}
  getBoundingClientRect(){return {left:400,right:1000,top:0,bottom:800};}
}
function fixture(options={}){
  const doc={createElement(tag){return new Element(tag,this);}};doc.body=new Element('body',doc);doc.activeElement=doc.body;
  const container=doc.createElement('div'),opener=doc.createElement('button');opener.textContent='История';doc.body.append(opener,container);opener.focus();
  const opened=[],errors=[],workspace=new history.Workspace({container,onOpen:options.onOpen|| (async id=>opened.push(id)),onError:options.onError|| (error=>errors.push(error))});
  return {workspace,doc,container,opener,opened,errors};
}
const run=(id,fields={})=>({id,title:'Полиномиальная замена',purpose:'prove',status:'complete',outcome:'unknown',created_at:'2026-10-31T14:26:46+03:00',...fields});
const tick=()=>new Promise(resolve=>setImmediate(resolve));

test('finished searches never inherit a proof or counterexample badge',()=>{
  for(const purpose of ['structure','discover'])for(const outcome of ['proved','refuted','unknown']){
    const status=history.statusOf(run('s',{purpose,outcome}));assert.deepEqual(status,{kind:'search',label:'Поиск завершён'});
  }
  assert.equal(history.statusOf(run('p',{outcome:'proved'})).label,'Есть результат Lean');
  assert.equal(history.statusOf(run('n',{outcome:'refuted'})).label,'Отрицательная цель проверена');
  assert.match(history.statusOf(run('f',{formal_outcome:'proved'})).label,/смысл не подтверждён/);
});

test('active, failed and interrupted attempts cannot inherit old success; catenoid search and proof differ',()=>{
  for(const status of ['running','queued','cancelling','failed','timeout','cancelled','interrupted','budget_exhausted']){
    assert.notEqual(history.statusOf(run('p',{status,outcome:'proved'})).kind,'result');
  }
  assert.equal(history.statusOf(run('search',{purpose:'discover',status:'complete'})).label,'Поиск завершён');
  assert.equal(history.statusOf(run('proof',{status:'failed'})).label,'Проверка не завершена');
  assert.equal(history.statusOf(run('limit',{status:'budget_exhausted'})).label,'Достигнут лимит работы');
});

test('history uses saved termination causes while preserving successful formal-only evidence',()=>{
  for(const[code,title]of [['invalid_plan','План отклонён до проверки Lean'],['proof_not_produced','Текст доказательства не получен'],['lean_unproved','Lean не подтвердил доказательство'],['infrastructure','Сбой сервиса или окружения']])assert.deepEqual(history.statusOf(run('attempt',{status:'failed',termination:{code,stage:'prove',message:'Exact'}})),{kind:'incomplete',label:title});
  assert.equal(history.statusOf(run('old',{status:'failed',error:'Тип леммы не должен содержать команды Lean.'})).label,'План отклонён до проверки Lean');assert.equal(history.statusOf(run('scope',{requires_review:true})).label,'Нужно уточнить постановку');
  assert.equal(history.statusOf(run('formal',{formal_outcome:'proved',termination:{code:'needs_review'}})).kind,'formal');
  const stopped=history.statusOf(run('later-limit',{status:'budget_exhausted',formal_outcome:'proved',termination:{code:'budget_exhausted',stage:'semantic_review'}}));assert.equal(stopped.kind,'formal');assert.match(stopped.label,/Lean-цель проверена/);assert.match(stopped.label,/Достигнут лимит/);
});

test('only provided titles, sources and dates are used; generated Lean identifier is not a visible title',()=>{
  const item=history.summaryOf(run('technical-id',{title:'Найти общую структуру для Lean-теоремы Arxiv261038474.subtract_restore',purpose:'structure',case_id:'pretend-paper',graph_ref:{id:'hidden-graph'},created_at:'not-a-date'}));
  assert.equal(item.title,'Поиск общей структуры');assert.equal(item.source,'');assert.equal(item.date,'Дата не сохранена');assert.equal(item.datetime,'');
  const explicit=history.summaryOf(run('id',{display_title:'Связь метрик',source_title:'Catenoids in hyperbolic space'}));
  assert.equal(explicit.title,'Связь метрик');assert.equal(explicit.source,'Catenoids in hyperbolic space');assert.match(explicit.date,/2026/);assert.equal(explicit.datetime,'2026-10-31T11:26:46.000Z');
  assert.equal(history.summaryOf(run('empty',{title:'',created_at:null})).title,'Проверка связи');
});

test('search matches title and real source, independent of case, ё and spacing; technical IDs are not search metadata',()=>{
  const item=history.summaryOf(run('secret-id',{title:'Обратимость отображений',source_title:'Трёхмерная геометрия'}));
  assert.ok(history.matches(item,'  ГЕОМЕТРИЯ   обратимость '));assert.ok(history.matches(item,'трехмерная'));assert.ok(!history.matches(item,'secret-id'));
  assert.ok(!history.matches(item,'несуществующая статья'));
});

test('native dialog is named, opens focused search, and Escape / close restore the opener',()=>{
  const {workspace:w,opener,doc}=fixture();assert.equal(w.dialog.tagName,'DIALOG');assert.ok(w.dialog.getAttribute('aria-labelledby'));assert.ok(w.dialog.getAttribute('aria-describedby'));
  w.show();assert.ok(w.dialog.open);assert.equal(doc.activeElement,w.search);w.show();assert.equal(w.dialog.modalCalls,1);
  const cancel=w.dialog.dispatch('cancel');assert.ok(cancel.defaultPrevented);assert.equal(w.dialog.open,false);assert.equal(doc.activeElement,opener);
  w.show();w.closeButton.dispatch('click');assert.equal(w.dialog.open,false);assert.equal(doc.activeElement,opener);
  w.show();w.dialog.dispatch('click',{clientX:20,clientY:100});assert.equal(w.dialog.open,false);
});

test('one card click invokes async opening once, waits for success and then closes',async()=>{
  let finish;const calls=[];const {workspace:w}=fixture({onOpen:id=>{calls.push(id);return new Promise(resolve=>{finish=resolve;});}});
  w.render([run('a'),run('b')],'a');w.show();
  const a=w.rows.get('a');assert.equal(a.button.getAttribute('aria-current'),'page');assert.equal(a.current.hidden,false);assert.equal(w.rows.get('b').current.hidden,true);
  a.button.dispatch('click');a.button.dispatch('click');w.rows.get('b').button.dispatch('click');
  assert.deepEqual(calls,['a']);assert.ok(w.dialog.open);assert.equal(w.list.getAttribute('aria-busy'),'true');assert.equal(a.status.textContent,'Открываем…');
  finish();await tick();assert.equal(w.dialog.open,false);assert.equal(w.pendingId,null);assert.equal(a.button.getAttribute('aria-disabled'),'false');
});

test('opening failure stays readable in the panel, calls onError and allows retry',async()=>{
  let attempts=0;const original=new Error('<script>private traceback</script>');const {workspace:w,errors}=fixture({onOpen:async()=>{attempts++;if(attempts===1)throw original;}});
  w.render([run('a')],null);w.show();await w.open('a');
  assert.ok(w.dialog.open);assert.equal(w.error.hidden,false);assert.match(w.error.textContent,/Не удалось открыть/);assert.doesNotMatch(w.error.textContent,/script|traceback/);assert.deepEqual(errors,[original]);
  await w.open('a');assert.equal(attempts,2);assert.equal(w.dialog.open,false);
});

test('polling retains query, scroll, current marker and focused card across status change and reorder',()=>{
  const {workspace:w,doc}=fixture();const a=run('a'),b=run('b',{title:'Полиномы над кольцом'});
  w.render([a,b],'a');w.show();w.search.value='пол';w.search.dispatch('input');
  const card=w.rows.get('b').button;card.focus();w.scroll.scrollTop=184;
  w.render([{...b,status:'running'},a,run('c')],'b');
  assert.equal(w.search.value,'пол');assert.equal(w.scroll.scrollTop,184);assert.equal(w.rows.get('b').button,card);assert.equal(doc.activeElement,card);assert.equal(w.list.children[0],w.rows.get('b').item);assert.equal(card.getAttribute('aria-current'),'page');
  assert.equal(w.rows.get('a').button.getAttribute('aria-current'),null);assert.equal(w.rows.get('b').status.textContent,'Идёт проверка');
  w.search.focus();w.search.selectionStart=1;w.search.selectionEnd=2;w.render([b,a],'b');assert.equal(doc.activeElement,w.search);assert.equal(w.search.selectionStart,1);assert.equal(w.search.selectionEnd,2);
});

test('filtering reports empty results and removed focus falls back to the search field',()=>{
  const {workspace:w,doc}=fixture();w.render([run('a'),run('a'),null,{},run('b',{source_title:'Гиперболические поверхности'})],null);assert.equal(w.rows.size,2);
  w.search.value='гиперболические';w.search.dispatch('input');assert.equal(w.rows.get('a').item.hidden,true);assert.equal(w.rows.get('b').item.hidden,false);assert.equal(w.count.textContent,'Найдено: 1 из 2');
  w.rows.get('b').button.focus();w.render([run('a')],null);assert.equal(doc.activeElement,w.search);assert.equal(w.empty.hidden,false);assert.match(w.empty.textContent,/Ничего не найдено/);
  w.search.value='';w.search.dispatch('input');w.render([],null);assert.match(w.empty.textContent,/Здесь появятся/);
});

test('closing and reopening during an outstanding open does not close the new panel session',async()=>{
  let finish;const {workspace:w}=fixture({onOpen:()=>new Promise(resolve=>{finish=resolve;})});w.render([run('a')],null);w.show();const opening=w.open('a');w.hide();w.show();finish();await opening;assert.ok(w.dialog.open);
});

test('metadata remains text, never markup, and IDs are absent from the visible card',()=>{
  const {workspace:w}=fixture();w.render([run('secret-id',{title:'<img src=x onerror=attack()>',source_title:'<script>attack()</script>',graph_ref:{id:'graph-secret'},selected_transition_id:'transition-secret'})],null);
  const card=w.rows.get('secret-id');assert.equal(card.title.textContent,'<img src=x onerror=attack()>');assert.equal(card.title.children.length,0);assert.equal(card.source.children.length,0);
  assert.doesNotMatch(card.button.textContent,/secret-id|graph-secret|transition-secret/);
  const code=fs.readFileSync(require.resolve('../web/research-history.js'),'utf8');assert.doesNotMatch(code,/innerHTML|\bfetch\s*\(|XMLHttpRequest|\/api\//);
});

test('panel layout has bounded mobile width, independent scrolling, visible focus and reduced motion',()=>{
  const css=fs.readFileSync(require.resolve('../web/research-history.css'),'utf8');
  for(const token of ['width:min(600px,100%)','100dvh','overflow:auto','overscroll-behavior:contain',':focus-visible','prefers-reduced-motion','::backdrop'])assert.ok(css.includes(token),token);
});

test('closed native dialog explicitly overrides legacy research-history display rules',()=>{
  const css=fs.readFileSync(require.resolve('../web/research-history.css'),'utf8');
  assert.match(css,/dialog\.research-history:not\(\[open\]\)\s*\{\s*display\s*:\s*none\s*\}/);
  assert.match(css,/dialog\.research-history\[open\]\s*\{\s*display\s*:\s*flex/);
  assert.doesNotMatch(css,/(?:^|\n)\.research-history\[open\]/);
});
