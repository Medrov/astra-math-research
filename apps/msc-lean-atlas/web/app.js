'use strict';

(() => {
  const $ = id => document.getElementById(id);
  const state = {graph:null,nodeMap:new Map(),children:new Map(),outgoing:new Map(),incoming:new Map(),selected:null,catalogMode:'roots',catalogPage:0,activeTab:'map'};
  const SEARCH_PAGE=30;
  let graphView=null;
  const MSC_ROOT={id:'__msc__',code:'MSC2020',title:'Полный классификатор математики',parent_id:null,level:-1};
  const viewNode=id=>id===MSC_ROOT.id?MSC_ROOT:state.nodeMap.get(id);
  const childNodes=id=>id===MSC_ROOT.id?rootNodes():(state.children.get(id)||[]);
  function showOverview(){if(!state.graph)return;$('msc-search').value='';state.catalogMode='roots';state.catalogPage=0;selectNode(MSC_ROOT.id);}
  const relationLabels={broader:'Входит в раздел',see_also:'Смотрите также',classify_elsewhere:'Классифицировать в',avoid_classification:'Исключение из рубрики',co_classify:'Совместная классификация',classification_alternative:'Альтернатива классификации',related_topic:'Связанная тема',grouped:'Групповая отсылка'};
  const aliases={'алгебра':'algebra','геометрия':'geometry','граф':'graph','графы':'graph','топология':'topology','числа':'number','теория чисел':'number theory','вероятность':'probability','вероятности':'probability','оптимизация':'optimization','решетки':'lattices','решётки':'lattices','порядок':'order','логика':'logic','анализ':'analysis','комбинаторика':'combinatorics','кодирование':'coding','группы':'group','кольца':'ring','модули':'module','категории':'category','дифференциальные':'differential','уравнения':'equations','спектр':'spectral','квантовая':'quantum','персистентность':'persistence','гомология':'homology','выпуклость':'convex','полиномы':'polynomial'};

  function el(tag,attrs={},text){const node=document.createElement(tag);for(const [k,v]of Object.entries(attrs)){if(k==='class')node.className=v;else node.setAttribute(k,String(v));}if(text!==undefined)node.textContent=String(text);return node;}
  function textValue(value){if(value===null||value===undefined)return '';return typeof value==='string'?value:JSON.stringify(value,null,2);}
  function formatNumber(value){return Number(value).toLocaleString('ru-RU');}
  function notice(target,text){target.textContent=text;target.hidden=!text;}
  function relationName(type){return relationLabels[type]||type.replaceAll('_',' ');}
  async function api(path){const response=await fetch(path);let result;try{result=await response.json();}catch{throw new Error(`Сервер вернул некорректный ответ (${response.status}).`);}if(!response.ok)throw new Error(textValue(result.error||result.detail||`Ошибка HTTP ${response.status}`));return result;}
  function download(name,value,type='application/json'){const blob=new Blob([typeof value==='string'?value:JSON.stringify(value,null,2)],{type});const url=URL.createObjectURL(blob),a=el('a',{href:url,download:name});a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);}

  function showTab(tab,writeURL=true){
    state.activeTab=tab==='research'?'research':'map';
    $('map-panel').hidden=state.activeTab!=='map';
    $('research-panel').hidden=state.activeTab!=='research';
    for(const button of document.querySelectorAll('[data-tab]')){
      const active=button.dataset.tab===state.activeTab;
      button.classList.toggle('active',active);button.setAttribute('aria-selected',String(active));
    }
    if(writeURL){const url=new URL(location.href);url.searchParams.delete('run');url.hash=state.activeTab;history.replaceState(null,'',url);}
    if(state.activeTab==='map'){window.ResearchWorkspace?.hide();requestAnimationFrame(renderGraph);}
    else window.ResearchWorkspace?.show();
  }
  function showMap(){showTab('map');}
  function route(){showTab(location.hash==='#research'?'research':'map');}
  function startResearch(){const node=viewNode(state.selected);showTab('research');window.ResearchWorkspace?.setContext(node?.id===MSC_ROOT.id?null:node);}
  window.MSCAtlas={
    open(code){if(state.nodeMap.has(code)){showMap();selectNode(code);}},
    selected(){return viewNode(state.selected);},
    lookup(code){
      const node=state.nodeMap.get(code);if(!node)return null;
      const path=[],seen=new Set();let current=node;
      while(current&&!seen.has(current.id)){
        seen.add(current.id);path.unshift({code:current.code,title:current.title,parent_id:current.parent_id});
        current=state.nodeMap.get(current.parent_id);
      }
      return {code:node.code,title:node.title,parent_id:node.parent_id,path};
    }
  };
  function selectNode(id,fromResult=false,fromGraph=false){
    if(!viewNode(id))return;
    state.selected=id;renderCatalog();renderCategory();renderBreadcrumbs();
    $('research-selected').disabled=id===MSC_ROOT.id;
    if(fromResult)showMap();
    if(!graphView&&state.activeTab==='map')renderGraph();
    if(graphView){if(fromGraph)graphView.select(id);else graphView.navigate(id);}
    updateGraphParent();
    if(fromResult)$('map-title').scrollIntoView({behavior:'smooth',block:'start'});
  }
  function updateGraphParent(){
    const n=viewNode(state.selected),parent=n?.id===MSC_ROOT.id?null:state.nodeMap.get(n?.parent_id)||MSC_ROOT;
    $('graph-up').disabled=!parent;
    $('graph-up').onclick=()=>{if(parent)selectNode(parent.id);};
  }
  function rootNodes(){return state.graph.nodes.filter(n=>!n.parent_id||!state.nodeMap.has(n.parent_id));}
  function searchNodes(query){const lower=query.toLowerCase().trim();const translated=aliases[lower]||lower.split(/\s+/).map(t=>aliases[t]||t).join(' ');const terms=[...new Set([lower,translated])];return state.graph.nodes.map(n=>{const code=String(n.code).toLowerCase(),hay=[n.title,n.title_ru,n.description].filter(Boolean).join(' ').toLowerCase();let score=0;for(const term of terms){if(code===term)score=Math.max(score,100);else if(code.startsWith(term))score=Math.max(score,80);else if(hay.includes(term))score=Math.max(score,50);else if(term.split(/\s+/).every(t=>hay.includes(t)))score=Math.max(score,30);}return {n,score};}).filter(x=>x.score).sort((a,b)=>b.score-a.score||a.n.code.localeCompare(b.n.code)).map(x=>x.n);}
  function pagination(container,total,page,size,onChange){container.replaceChildren();if(total<=size)return;const pages=Math.ceil(total/size),prev=el('button',{type:'button','aria-label':'Предыдущая страница'},'←'),next=el('button',{type:'button','aria-label':'Следующая страница'},'→');prev.disabled=page===0;next.disabled=page>=pages-1;prev.onclick=()=>onChange(page-1);next.onclick=()=>onChange(page+1);container.append(prev,el('span',{},`${page+1} / ${pages}`),next);}
  function renderCatalog(){if(!state.graph)return;const query=$('msc-search').value.trim();let list;if(query){list=searchNodes(query);$('catalog-heading').textContent='Результаты поиска';}else if(state.catalogMode==='children'){list=childNodes(state.selected);$('catalog-heading').textContent='В выбранном разделе';}else{list=rootNodes();$('catalog-heading').textContent='Основные разделы';}$('catalog-count').textContent=formatNumber(list.length);const pages=Math.max(1,Math.ceil(list.length/SEARCH_PAGE));state.catalogPage=Math.min(state.catalogPage,pages-1);const target=$('catalog-list');target.replaceChildren();for(const n of list.slice(state.catalogPage*SEARCH_PAGE,(state.catalogPage+1)*SEARCH_PAGE)){const b=el('button',{type:'button',class:'catalog-item'+(n.id===state.selected?' selected':''),'data-msc':n.id,'aria-label':`${n.code}: ${n.title}`});b.append(el('span',{class:'category-code'},n.code),el('span',{},n.title));b.onclick=()=>selectNode(n.id);target.append(b);}if(!list.length)target.append(el('div',{class:'empty-state'},'Ничего не найдено. Попробуйте код MSC или английское название.'));pagination($('catalog-pagination'),list.length,state.catalogPage,SEARCH_PAGE,p=>{state.catalogPage=p;renderCatalog();});}
  function renderBreadcrumbs(){const container=$('breadcrumbs');container.replaceChildren();const all=el('button',{type:'button'},'MSC2020');all.onclick=showOverview;container.append(all);const chain=[],seen=new Set();let n=state.nodeMap.get(state.selected);while(n&&!seen.has(n.id)){seen.add(n.id);chain.unshift(n);n=state.nodeMap.get(n.parent_id);}for(const entry of chain){container.append(el('span',{class:'separator'},'/'));const b=el('button',{type:'button'},entry.code);b.onclick=()=>selectNode(entry.id);container.append(b);}}
  function outgoingRelations(id){return (state.outgoing.get(id)||[]).filter(e=>e.type!=='broader');}
  function renderCategory(){const n=viewNode(state.selected);if(!n)return;const panel=$('category-panel');panel.replaceChildren();const heading=el('div',{class:'category-heading'});heading.append(el('span',{class:'category-code'},n.code),el('h2',{},n.title),el('span',{class:'category-level'},n.id===MSC_ROOT.id?'Обзор классификатора':['Основной раздел','Подраздел','Подробная рубрика'][Number(n.level)]||'Рубрика MSC'));panel.append(heading);if(n.id===MSC_ROOT.id){const d=el('div',{class:'category-detail'});d.append(el('h3',{},formatNumber(state.graph.nodes.length)+' рубрик · '+rootNodes().length+' основных раздела'),el('p',{},'Все рубрики официального классификатора доступны через иерархию и поиск. Центральная вершина MSC2020 служит обзором; она не добавляет новую рубрику в исходные данные.'),el('p',{},'Линии от обзора к основным разделам показывают навигацию по классификатору. Они не утверждают математическую эквивалентность.'));panel.append(d);return;}if(n.description&&n.description!==n.title){const d=el('div',{class:'category-detail'});d.append(el('h3',{},'Описание'),el('p',{},n.description));panel.append(d);}const children=state.children.get(n.id)||[];if(children.length){const d=el('div',{class:'category-detail'});d.append(el('h3',{},`${formatNumber(children.length)} дочерних рубрик`));const b=el('button',{type:'button',class:'text-button'},'Показать список рубрик →');b.onclick=()=>{state.catalogMode='children';state.catalogPage=0;$('msc-search').value='';renderCatalog();$('catalog-heading').scrollIntoView({behavior:'smooth',block:'nearest'});};d.append(b);panel.append(d);}const references=outgoingRelations(n.id);const incoming=(state.incoming.get(n.id)||[]).filter(e=>e.type!=='broader');for(const [title,rels,reverse]of [['Отсылки классификатора',references,false],['На эту рубрику ссылаются',incoming,true]]){const d=el('div',{class:'category-detail'});d.append(el('h3',{},title+(rels.length?` · ${rels.length}`:'')));if(!rels.length)d.append(el('p',{},'В исходном классификаторе не указаны.'));else{const list=el('div',{class:'reference-list'});for(const e of rels){const id=reverse?e.source:e.target,target=state.nodeMap.get(id),b=el('button',{type:'button',class:'reference-link'});b.append(el('span',{class:'reference-kind'},relationName(e.type)),el('code',{},target?.code||id),el('span',{class:'reference-title'},target?.title||e.reference_text||''));if(e.reference_text)b.append(el('span',{class:'reference-context'},e.reference_text));b.onclick=()=>selectNode(id);if(!target)b.disabled=true;list.append(b);}d.append(list);}panel.append(d);}const d=el('div',{class:'category-detail'});d.append(el('p',{},'Отсылки MSC описывают тематическую классификацию. Математические соответствия между конкретными объектами проверяются отдельно.'));panel.append(d);}
  function renderGraph(){
    if(!state.graph||state.activeTab!=='map'||$('graph-canvas').clientWidth<100)return;
    if(!graphView){
      graphView=new MSCGraphView({container:$('graph-canvas'),dataset:state.graph,onSelect:id=>selectNode(id,false,true)});
    }
    graphView.resize();graphView.select(state.selected||MSC_ROOT.id);updateGraphParent();
  }
  function renderMetadata(){const graph=state.graph,meta=graph.meta||{},roots=rootNodes(),refs=graph.edges.filter(e=>e.type!=='broader');const stats=$('dataset-stats');stats.replaceChildren();for(const [value,label]of [[graph.nodes.length,'рубрик в графе'],[roots.length,'основных разделов'],[refs.length,'явных отсылок']]){const item=el('div',{class:'dataset-stat'});item.append(el('strong',{},formatNumber(value)),el('span',{},label));stats.append(item);}const footer=$('source-attribution');footer.replaceChildren();const source=el('p');source.append('Источник: ',el('a',{href:meta.source_url||'https://msc2020.org/',target:'_blank',rel:'noopener noreferrer'},'MSC2020 · Mathematical Reviews и zbMATH'),'. ',textValue(meta.license||'CC BY-NC-SA'));footer.append(source);const date=meta.retrieved_at||meta.fetched_at||meta.downloaded_at;footer.append(el('p',{},`Все ${formatNumber(graph.nodes.length)} рубрик загружены; доступны обзор, отдельная ветвь и полный граф.${date?' Данные получены: '+String(date).slice(0,10)+'.':''}`));if(meta.count_note)footer.append(el('p',{},'Количество рубрик рассчитано по полному официальному CSV/TeX; оно отличается от сводных чисел на главной странице MSC. Исходные данные и расхождение сохранены в метаданных графа.'));if(meta.counts?.unresolved_references)footer.append(el('p',{},'Неоднозначных отсылок в отдельной очереди: '+meta.counts.unresolved_references+'. Они не превращены в вымышленные рёбра.'));$('download-graph').disabled=false;}

  document.querySelector('[data-tab="map"]').onclick=showMap;
  document.querySelector('[data-tab="research"]').onclick=()=>showTab('research');
  $('research-selected').onclick=startResearch;
  document.querySelector('.brand').onclick=event=>{event.preventDefault();showMap();};
  $('msc-search').addEventListener('input',()=>{state.catalogPage=0;renderCatalog();});
  $('show-roots').onclick=showOverview;
  $('download-graph').onclick=()=>{if(state.graph)download('msc2020-graph.json',state.graph);};
  window.addEventListener('hashchange',route);
  window.addEventListener('popstate',route);
  let resizeFrame;
  new ResizeObserver(()=>{cancelAnimationFrame(resizeFrame);resizeFrame=requestAnimationFrame(renderGraph);}).observe($('graph-canvas'));

  async function init(){
    route();
    try{
      state.graph=await api('/api/graph');
      state.nodeMap=new Map(state.graph.nodes.map(n=>[n.id,n]));
      for(const n of state.graph.nodes){
        if(n.parent_id){
          if(!state.children.has(n.parent_id))state.children.set(n.parent_id,[]);
          state.children.get(n.parent_id).push(n);
        }
      }
      for(const children of state.children.values())children.sort((a,b)=>(a.level===1?0:1)-(b.level===1?0:1)||a.code.localeCompare(b.code));
      for(const edge of state.graph.edges){
        if(!state.outgoing.has(edge.source))state.outgoing.set(edge.source,[]);
        state.outgoing.get(edge.source).push(edge);
        if(!state.incoming.has(edge.target))state.incoming.set(edge.target,[]);
        state.incoming.get(edge.target).push(edge);
      }
      state.selected=MSC_ROOT.id;
      window.dispatchEvent(new Event('msc-atlas-ready'));
      renderMetadata();renderCatalog();renderCategory();renderBreadcrumbs();renderGraph();
      $('connection-status').className='connection-status ready';
      $('connection-status').replaceChildren(el('i'),document.createTextNode('Локальная карта готова'));
    }catch(error){
      $('connection-status').className='connection-status failed';
      $('connection-status').replaceChildren(el('i'),document.createTextNode('Карта недоступна'));
      notice($('global-error'),'Не удалось загрузить полный классификатор: '+error.message);
    }
  }
  init();
})();
