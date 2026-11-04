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

test('compact rows keep the opening action separate from a complete native reason disclosure',()=>{
  const {workspace:w,opened}=fixture(),reason='  Точное уточнение\n'+('Сохранить все предпосылки. '.repeat(120))+'<img src=x onerror=attack()>  ';
  w.render([run('version',{source_lineage:{parent_run_id:'parent',kind:'correction',reason}})],null);
  const row=w.rows.get('version');assert.equal(w.list.dataset.layout,'rows');assert.deepEqual(row.button.children.map(n=>n.className),['research-history-main','research-history-meta']);assert.equal(row.reasonDetails.tagName,'DETAILS');assert.equal(row.reasonDetails.parentNode,row.item);assert.equal(row.reasonDetails.open,false);assert.equal(row.reasonSummary.tagName,'SUMMARY');assert.equal(row.reasonSummary.textContent,'Причина исправления');assert.match(row.reasonSummary.getAttribute('aria-label'),/Полиномиальная замена/);assert.equal(row.reason.textContent,reason);assert.equal(row.reason.children.length,0);assert.equal(row.version.textContent,'Исправленная версия');assert.equal(row.button.textContent.includes(reason),false);
  row.reasonSummary.dispatch('click');row.reasonDetails.open=true;assert.deepEqual(opened,[]);assert.equal(w.pendingId,null);
});

test('lineage labels use only the explicit kind and do not call a continuation a correction',()=>{
  const {workspace:w}=fixture(),cases=[['correct','correction','Исправленная версия','Причина исправления'],['continue','atlas_continuation','Продолжение поиска','Контекст продолжения'],['unknown','future_kind','Связанная попытка','Контекст связанной попытки'],['legacy',undefined,'Связанная попытка','Контекст связанной попытки']],runs=cases.map(([id,kind])=>run(id,{source_lineage:{parent_run_id:'parent',root_run_id:'root',kind,reason:'Полный сохранённый контекст'}}));
  const before=JSON.stringify(runs);w.render(runs,null);
  for(const[id,,label,heading]of cases){const row=w.rows.get(id);assert.equal(row.version.textContent,label);assert.equal(row.reasonSummary.textContent,heading);assert.equal(row.reasonDetails.hidden,false);assert.doesNotMatch(row.button.textContent,/parent|root|future_kind/);}
  assert.equal(JSON.stringify(runs),before);assert.equal(history.summaryOf(run('unrelated')).version,'');
});

test('all status filters report visible and total counts even without a search query',()=>{
  const {workspace:w}=fixture();w.render([run('active',{status:'running'}),run('failure',{status:'failed'}),run('proof',{outcome:'proved'}),run('search',{purpose:'structure'})],null);assert.equal(w.count.textContent,'Сохранено: 4');
  for(const name of ['active','attention','search','result']){w.filterButtons.get(name).dispatch('click');assert.equal(w.count.textContent,'Показано: 1 из 4');assert.equal([...w.rows.values()].filter(row=>!row.item.hidden).length,1);for(const[key,button]of w.filterButtons)assert.equal(button.getAttribute('aria-pressed'),String(key===name));}
  w.search.value='Нет совпадения';w.search.dispatch('input');assert.equal(w.count.textContent,'Найдено: 0 из 4');assert.equal(w.empty.hidden,false);assert.match(w.empty.textContent,/запрос или фильтр/);assert.equal(w.filter,'result');w.search.value='';w.search.dispatch('input');w.filterButtons.get('all').dispatch('click');assert.equal(w.count.textContent,'Сохранено: 4');
});

test('source headings restart for each visible context segment without changing the existing run order',()=>{
  const {workspace:w}=fixture(),runs=[run('a1',{source_title:'Источник A',source_lineage:{root_run_id:'r1'}}),run('a2',{source_title:'Источник A',source_lineage:{root_run_id:'r2'}}),run('b',{source_title:'Источник B',outcome:'proved',source_lineage:{root_run_id:'r3'}}),run('a3',{source_title:'Источник A',source_lineage:{root_run_id:'r4'}})],before=JSON.stringify(runs);
  w.render(runs,null);assert.deepEqual(w.runs.map(r=>r.id),['a1','a2','b','a3']);assert.deepEqual(['a1','a2','b','a3'].map(id=>w.rows.get(id).group.hidden),[false,true,false,false]);assert.equal(w.rows.get('a3').group.textContent,'Источник A');assert.equal(w.rows.get('a3').group.tagName,'H3');
  w.filterButtons.get('attention').dispatch('click');assert.equal(w.rows.get('b').item.hidden,true);assert.deepEqual(['a1','a2','a3'].map(id=>w.rows.get(id).group.hidden),[false,true,true]);w.filterButtons.get('all').dispatch('click');assert.equal(w.rows.get('a3').group.hidden,false);assert.equal(JSON.stringify(runs),before);
});

test('polling preserves an open reason, its keyboard focus and scroll while updating exact text',()=>{
  const {workspace:w,doc}=fixture(),version=run('v',{source_lineage:{parent_run_id:'parent',kind:'correction',reason:'Первая причина'}}),other=run('other');
  w.render([version,other],null);w.show();const row=w.rows.get('v'),summary=row.reasonSummary;row.reasonDetails.open=true;summary.focus();w.scroll.scrollTop=165;w.render([other,{...version,status:'running',source_lineage:{...version.source_lineage,reason:'Новая сохранённая\nпричина'}}],'v');
  assert.equal(w.rows.get('v'),row);assert.equal(row.reasonDetails.open,true);assert.equal(row.reasonSummary,summary);assert.equal(doc.activeElement,summary);assert.equal(w.scroll.scrollTop,165);assert.equal(row.reason.textContent,'Новая сохранённая\nпричина');assert.equal(row.status.textContent,'Идёт проверка');assert.equal(row.button.getAttribute('aria-current'),'page');
});

test('hidden or removed reason focus falls back to a visible control',()=>{
  const {workspace:w,doc}=fixture(),version=run('v',{source_lineage:{parent_run_id:'parent',kind:'correction',reason:'Уточнение'}});w.render([version],null);w.show();const row=w.rows.get('v');row.reasonSummary.focus();w.render([{...version,source_lineage:{...version.source_lineage,reason:''}}],null);assert.equal(row.reasonDetails.hidden,true);assert.equal(doc.activeElement,row.button);
  w.render([version],null);row.reasonSummary.focus();w.filter='active';w.updateVisibility();assert.equal(row.item.hidden,true);assert.equal(doc.activeElement,w.search);assert.equal(w.count.textContent,'Показано: 0 из 1');
});

test('a reason without lineage is preserved as record context without fabricating a version',()=>{
  const {workspace:w}=fixture();w.render([run('context',{source_lineage:{reason:'Сохранённое замечание без parent'}})],null);const row=w.rows.get('context');assert.equal(row.version.hidden,true);assert.equal(row.reasonDetails.hidden,false);assert.equal(row.reasonSummary.textContent,'Контекст записи');assert.equal(row.reason.textContent,'Сохранённое замечание без parent');
});
