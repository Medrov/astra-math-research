'use strict';

/* Cytoscape owns rendering and interactions; fCoSE owns node placement. */
class MSCGraphView {
  constructor({container,dataset,onSelect}) {
    this.container=container;this.dataset=dataset;this.model=new MSCGraphModel(dataset);this.onSelect=onSelect;
    this.mode='overview';this.focusId='__msc__';this.selected='__msc__';this.references=false;this.labels=true;
    this.depth=1;this.activeGroups=null;this.rootFilter='all';this.colorMode='groups';this.labelStyle='code';this.hoverFocus=true;
    this.history=[];this.historyIndex=-1;this.bookmarks=new Set();this.immersive=false;
    this.cache=new Map();this.currentKey=null;this.generation=0;this.worker=null;this.graph=null;
    this.$=id=>document.getElementById(id);
    this.cy=cytoscape({container,elements:[],layout:{name:'preset'},minZoom:0.025,maxZoom:6,
      pixelRatio:Math.min(devicePixelRatio||1,1.5),selectionType:'single',boxSelectionEnabled:false,
      style:[
        {selector:'node',style:{width:'data(size)',height:'data(size)','background-color':'data(color)',
          'border-width':1,'border-color':'#fff',label:'data(code)','font-family':'system-ui, sans-serif',
          'font-size':16,color:'#444','text-valign':'bottom','text-margin-y':7,'min-zoomed-font-size':11,
          'overlay-opacity':0,'z-index':2}},
        {selector:'node[level = 0]',style:{'font-size':34,'min-zoomed-font-size':9,'font-weight':600,color:'#333','z-index':4}},
        {selector:'node[level = 1]',style:{'font-size':20,'z-index':3}},
        {selector:'node[level = 2]',style:{'background-opacity':0.8}},
        {selector:'node[level = -1]',style:{'background-color':'#111','font-size':34,'font-weight':600,'min-zoomed-font-size':10,'z-index':5}},
        {selector:'node.context-node',style:{width:14,height:14,'background-color':'#aaa','font-size':16,'font-weight':400,'min-zoomed-font-size':11,'z-index':1}},
        {selector:'node.focus-node',style:{'border-color':'#252525','border-width':3,
          'background-opacity':1,'border-opacity':0.85,'border-style':'double','font-weight':700,color:'#111','font-size':24,
          'min-zoomed-font-size':0,'z-index':10}},
        {selector:'node.neighbor-node',style:{'background-opacity':1}},
        {selector:'edge',style:{width:1,'line-color':'data(edgeColor)','curve-style':'straight','opacity':0.3,'overlay-opacity':0}},
        {selector:'edge[type = "overview"]',style:{'line-color':'#ddd','line-style':'dotted','width':1.2}},
        {selector:'edge[type != "broader"][type != "overview"]',style:{'line-color':'#9f9f9f','line-style':'dashed',
          'target-arrow-shape':'triangle','target-arrow-color':'#999','arrow-scale':0.7,'width':1.1,'opacity':0.6}},
        {selector:'edge[type = "classify_elsewhere"], edge[type = "classification_alternative"]',style:{'line-style':'dotted','target-arrow-shape':'vee'}},
        {selector:'edge[type = "avoid_classification"]',style:{'line-style':'dotted','target-arrow-shape':'tee','width':1.6}},
        {selector:'edge.focus-edge',style:{'target-arrow-color':'#555','width':2,'opacity':0.85,'z-index':6}},
        {selector:'edge.hover-edge',style:{'line-color':'#333','target-arrow-color':'#333','width':3,'opacity':1,'z-index':8}},
        {selector:'.hover-muted',style:{opacity:0.09,'text-opacity':0.12}},
        {selector:'edge.hover-muted',style:{opacity:0.035}},
        {selector:'node.hover-neighbor',style:{'background-opacity':1,'z-index':9}},
        {selector:'edge.hover-neighbor',style:{opacity:0.9,width:2,'z-index':7}}
      ]});
    container.mscGraph=this;
    this.layoutCache=fetch('/graph-layouts.json').then(r=>{if(!r.ok)throw Error('layout cache');return r.json();})
      .then(data=>data.meta.source_sha256===dataset.meta.source_sha256&&data.meta.node_count===dataset.nodes.length?data:null).catch(()=>null);
    this.readPreferences();this.bindControls();this.bindGraph();this.renderColorGroups();this.renderBookmarks();
    this.show({mode:'overview',focusId:'__msc__'});
  }

  bindControls(){
    this.$('graph-mode').onchange=e=>this.setMode(e.target.value);
    this.$('graph-references').onchange=e=>{this.references=e.target.checked;this.show({mode:this.mode,focusId:this.focusId});};
    this.$('graph-labels').onchange=e=>{this.labels=e.target.checked;this.applyAppearance();};
    this.$('graph-depth').onchange=e=>{this.captureHistoryViewport();this.depth=Number(e.target.value);this.show({mode:'local',focusId:this.focusId});};
    this.$('graph-local').onclick=()=>this.openLocal(this.selected);
    this.$('graph-history-back').onclick=()=>this.goHistory(-1);
    this.$('graph-history-forward').onclick=()=>this.goHistory(1);
    this.$('graph-fullscreen').onclick=()=>this.toggleImmersive();
    this.$('graph-bookmark-toggle').onclick=()=>this.toggleBookmark();
    this.$('graph-color-mode').value=this.colorMode;
    this.$('graph-label-style').value=this.labelStyle;
    this.$('graph-color-mode').onchange=e=>{this.colorMode=e.target.value;this.applyAppearance();this.savePreferences();};
    this.$('graph-label-style').onchange=e=>{this.labelStyle=e.target.value;this.applyAppearance();this.savePreferences();};
    this.$('graph-hover-focus').onchange=e=>{this.hoverFocus=e.target.checked;this.clearHover();};
    for(const node of this.dataset.nodes.filter(n=>n.level===0)){
      const option=document.createElement('option');option.value=node.id;option.textContent=node.code+' · '+node.title;this.$('graph-root-filter').append(option);
    }
    this.$('graph-root-filter').onchange=e=>{this.rootFilter=e.target.value;this.show({mode:this.mode,focusId:this.focusId});};
    this.$('graph-reset-filters').onclick=()=>this.resetFilters();
    this.$('graph-fit').onclick=()=>this.fit();
    this.$('graph-zoom-in').onclick=()=>this.zoom(1.35);
    this.$('graph-zoom-out').onclick=()=>this.zoom(1/1.35);
    this.$('graph-relayout').onclick=()=>this.show({mode:this.mode,focusId:this.focusId,reset:true});
    this.$('graph-expand').onclick=()=>this.openBranch(this.selected);
    this.container.addEventListener('keydown',event=>{
      if(['+','=','-','0','Enter','ArrowLeft','ArrowRight','ArrowUp','ArrowDown'].includes(event.key))event.preventDefault();
      if(event.key==='+'||event.key==='=')this.zoom(1.35);
      if(event.key==='-')this.zoom(1/1.35);
      if(event.key==='0')this.fit();
      if(event.key==='Enter')this.openBranch(this.selected);
      const step=event.shiftKey?120:35;
      if(event.altKey&&event.key==='ArrowLeft')this.goHistory(-1);
      else if(event.altKey&&event.key==='ArrowRight')this.goHistory(1);
      else if(event.key.startsWith('Arrow'))this.cy.panBy({x:event.key==='ArrowLeft'?step:event.key==='ArrowRight'?-step:0,y:event.key==='ArrowUp'?step:event.key==='ArrowDown'?-step:0});
    });
    document.addEventListener('keydown',event=>{if(event.key==='Escape'&&this.immersive)this.toggleImmersive();});
    document.querySelectorAll('[data-tab]').forEach(button=>button.addEventListener('click',()=>{if(button.dataset.tab!=='map'&&this.immersive)this.toggleImmersive();}));
  }

  bindGraph(){
    this.container.addEventListener('mouseleave',()=>{this.clearHover();this.hideTooltip();this.container.style.cursor='default';});
    this.cy.on('tap','node',event=>{this.captureHistoryViewport();const id=event.target.id();this.select(id);this.onSelect(id);this.remember();});
    this.cy.on('dbltap','node',event=>this.openBranch(event.target.id()));
    this.cy.on('mouseover','node,edge',event=>{
      this.container.style.cursor=event.target.isNode()?'grab':'help';
      if(event.target.isEdge())event.target.addClass('hover-edge');
      else this.highlightNeighbors(event.target);
      this.tooltip(event.target,event.renderedPosition);
    });
    this.cy.on('mouseout','node,edge',event=>{event.target.removeClass('hover-edge');this.clearHover();this.hideTooltip();this.container.style.cursor='default';});
    this.cy.on('pan zoom grab drag',()=>{this.hideTooltip();this.clearHover();});
    this.cy.on('tap','edge',event=>this.tooltip(event.target,event.renderedPosition));
  }

  tooltip(element,point){
    const box=this.$('graph-tooltip');box.replaceChildren();
    const add=(tag,text)=>{const n=document.createElement(tag);n.textContent=text;box.append(n);};
    if(element.isNode()){
      add('strong',element.data('code')+' · '+element.data('title'));
      add('small',element.id()==='__msc__'?'Навигационный центр; не рубрика MSC.':'Клик — выбрать. Двойной клик — открыть ветвь.');
    }else{
      const labels={broader:'Входит в раздел',overview:'Навигационная связь с обзором',see_also:'Смотрите также',
        classify_elsewhere:'Условно классифицировать в другой рубрике',avoid_classification:'Исключение: не классифицировать здесь',
        co_classify:'Совместная классификация',classification_alternative:'Альтернатива классификации',related_topic:'Связанная тема'};
      add('strong',labels[element.data('type')]||element.data('type'));
      add('code',element.data('source')+' → '+element.data('target'));
      if(element.data('reference_text'))add('small',element.data('reference_text'));
    }
    box.hidden=false;const p=point||element.renderedPosition();
    const width=box.offsetWidth,height=box.offsetHeight;
    box.style.left=Math.max(8,Math.min(p.x+16,this.container.clientWidth-width-8))+'px';
    box.style.top=Math.max(8,Math.min(p.y+16,this.container.clientHeight-height-8))+'px';
  }
  hideTooltip(){this.$('graph-tooltip').hidden=true;}
  readPreferences(){
    try{
      const prefs=JSON.parse(localStorage.getItem('msc-atlas-appearance-v1')||'{}');
      if(['groups','mono'].includes(prefs.colorMode))this.colorMode=prefs.colorMode;
      if(['code','name'].includes(prefs.labelStyle))this.labelStyle=prefs.labelStyle;
      const bookmarks=JSON.parse(localStorage.getItem('msc-atlas-bookmarks-v1')||'[]');
      if(Array.isArray(bookmarks))this.bookmarks=new Set(bookmarks.filter(id=>this.model.nodeMap.has(id)));
    }catch{/* A restricted storage context still supports the graph. */}
  }
  savePreferences(){try{localStorage.setItem('msc-atlas-appearance-v1',JSON.stringify({colorMode:this.colorMode,labelStyle:this.labelStyle}));}catch{}}
  applyAppearance(){
    this.cy.style().selector('node').style({
      'background-color':node=>this.colorMode==='mono'?(node.data('level')<1?'#444':node.data('level')===1?'#888':'#b4b4b4'):node.data('color'),
      label:this.labels?(this.labelStyle==='name'?'data(displayLabel)':'data(code)'):'',
      'text-wrap':this.labelStyle==='name'?'wrap':'none','text-max-width':180
    }).selector('edge[type = "broader"]').style('line-color',edge=>this.colorMode==='mono'?'#bbb':edge.data('edgeColor')).update();
  }
  highlightNeighbors(node){
    this.clearHover();
    if(!this.hoverFocus||node.id()==='__msc__')return;
    const neighborhood=node.closedNeighborhood();
    this.cy.batch(()=>{this.cy.elements().not(neighborhood).addClass('hover-muted');neighborhood.addClass('hover-neighbor').removeClass('hover-muted');});
  }
  clearHover(){this.cy.elements('.hover-muted,.hover-neighbor').removeClass('hover-muted hover-neighbor');}
  renderColorGroups(){
    const container=this.$('graph-color-groups');container.replaceChildren();
    for(const group of MSCGraphPresentation.groups){
      const button=document.createElement('button');button.type='button';button.dataset.group=group.id;
      button.style.setProperty('--group-color',group.color);button.setAttribute('aria-pressed',String(!this.activeGroups||this.activeGroups.has(group.id)));
      button.title=group.label+' · клик для фильтрации';
      const dot=document.createElement('i');dot.setAttribute('aria-hidden','true');
      const name=document.createElement('span');name.textContent=group.shortLabel;button.append(dot,name);
      button.onclick=()=>{
        if(!this.activeGroups)this.activeGroups=new Set([group.id]);
        else if(this.activeGroups.has(group.id)){this.activeGroups.delete(group.id);if(!this.activeGroups.size)this.activeGroups=null;}
        else this.activeGroups.add(group.id);
        this.renderColorGroups();this.show({mode:this.mode,focusId:this.focusId});
      };
      container.append(button);
    }
  }
  resetFilters(){this.activeGroups=null;this.rootFilter='all';this.$('graph-root-filter').value='all';this.renderColorGroups();this.show({mode:this.mode,focusId:this.focusId});}
  decorateAndFilter(graph){
    let result=MSCGraphPresentation.decorate(graph);
    result.nodes=result.nodes.filter(n=>n.data.id==='__msc__'||((!this.activeGroups||this.activeGroups.has(n.data.colorGroup))&&(this.rootFilter==='all'||n.data.root===this.rootFilter)));
    result.realNodeCount=result.nodes.filter(n=>n.data.id!=='__msc__').length;
    if(!result.realNodeCount)result.nodes=[];
    const ids=new Set(result.nodes.map(n=>n.data.id)),byId=new Map(result.nodes.map(n=>[n.data.id,n]));
    result.nodes.forEach(n=>{n.data.displayLabel=n.data.code+'\n'+(n.data.title.length>70?n.data.title.slice(0,67)+'…':n.data.title);});
    result.edges=result.edges.filter(e=>ids.has(e.data.source)&&ids.has(e.data.target)).map(e=>({...e,data:{...e.data,edgeColor:byId.get(e.data.source).data.color}}));
    result.referenceCount=result.edges.filter(e=>!['broader','overview'].includes(e.data.type)).length;
    return result;
  }
  renderInspector(){
    const box=this.$('graph-node-inspector'),node=this.model.nodeMap.get(this.selected);box.replaceChildren();box.hidden=!node;
    if(!node)return;
    const title=document.createElement('strong');title.textContent=node.code+' · '+node.title;box.append(title);
    const meta=document.createElement('p'),group=MSCGraphPresentation.groupForRoot(this.model.rootOf(node.id));
    box.style.setProperty('--group-color',group?.color||'#64748b');
    meta.textContent=(group?.label||'')+(this.cy.getElementById(node.id).empty()?' · скрыто текущим фильтром':'');box.append(meta);
    const edges=this.dataset.edges.filter(e=>e.source===node.id||e.target===node.id),neighbors=[...new Set(edges.map(e=>e.source===node.id?e.target:e.source))];
    const links=document.createElement('div');links.className='inspector-links';
    const label=document.createElement('small');label.textContent=`Связанные рубрики: ${neighbors.length}. Перейдите к любой из них:`;box.append(label);
    for(const id of neighbors.slice(0,10)){
      const entry=this.model.nodeMap.get(id),button=document.createElement('button');button.type='button';button.textContent=id;button.title=entry.title;
      button.onclick=()=>this.openLocal(id);links.append(button);
    }
    if(neighbors.length>10){const more=document.createElement('button');more.type='button';more.textContent=`Все ${neighbors.length} →`;more.onclick=()=>{this.references=true;this.$('graph-references').checked=true;this.openLocal(node.id);};links.append(more);}
    box.append(links);
  }
  renderBookmarks(){
    const box=this.$('graph-bookmarks');box.replaceChildren();
    if(this.bookmarks.size){const label=document.createElement('span');label.textContent='Сохранено';box.append(label);}
    for(const id of this.bookmarks){const node=this.model.nodeMap.get(id);const button=document.createElement('button');button.type='button';button.textContent=id;button.title=node.title;button.onclick=()=>{this.onSelect(id);this.navigate(id);};box.append(button);}
    const valid=this.model.nodeMap.has(this.selected),saved=this.bookmarks.has(this.selected),toggle=this.$('graph-bookmark-toggle');
    toggle.disabled=!valid;toggle.textContent=saved?'★':'☆';toggle.setAttribute('aria-pressed',String(saved));toggle.setAttribute('aria-label',saved?'Убрать рубрику из сохранённых':'Сохранить выбранную рубрику');
  }
  toggleBookmark(){
    if(!this.model.nodeMap.has(this.selected))return;
    if(this.bookmarks.has(this.selected))this.bookmarks.delete(this.selected);else this.bookmarks.add(this.selected);
    try{localStorage.setItem('msc-atlas-bookmarks-v1',JSON.stringify([...this.bookmarks]));}catch{this.$('graph-selection-status').textContent='Рубрика сохранена только до закрытия этой вкладки.';}
    this.renderBookmarks();
  }
  toggleImmersive(){
    this.immersive=!this.immersive;document.body.classList.toggle('graph-immersive',this.immersive);
    const button=this.$('graph-fullscreen');button.setAttribute('aria-pressed',String(this.immersive));button.setAttribute('aria-label',this.immersive?'Свернуть карту':'Развернуть карту');
    this.$('graph-settings').open=false;requestAnimationFrame(()=>{this.cy.resize();this.fit();button.focus();});
  }
  historyState(){return {mode:this.mode,focusId:this.focusId,selected:this.selected,references:this.references,depth:this.depth,rootFilter:this.rootFilter,groups:this.activeGroups?[...this.activeGroups].sort():null};}
  captureHistoryViewport(){const entry=this.history[this.historyIndex];if(entry)entry.viewport={zoom:this.cy.zoom(),pan:{...this.cy.pan()}};}
  remember(){
    if(!this.graph||this.container.getAttribute('aria-busy')==='true')return;
    const state=this.historyState(),signature=JSON.stringify(state),previous=this.history[this.historyIndex];
    if(previous?.signature===signature){this.captureHistoryViewport();return;}
    this.history=this.history.slice(0,this.historyIndex+1);this.history.push({state,signature,viewport:{zoom:this.cy.zoom(),pan:{...this.cy.pan()}}});
    if(this.history.length>100)this.history.shift();this.historyIndex=this.history.length-1;this.updateHistoryButtons();
  }
  updateHistoryButtons(){this.$('graph-history-back').disabled=this.historyIndex<=0;this.$('graph-history-forward').disabled=this.historyIndex>=this.history.length-1;}
  async goHistory(delta){
    const index=this.historyIndex+delta;if(index<0||index>=this.history.length)return;
    this.captureHistoryViewport();this.historyIndex=index;const entry=this.history[index],state=entry.state;
    this.depth=state.depth;this.references=state.references;this.rootFilter=state.rootFilter;this.activeGroups=state.groups?new Set(state.groups):null;
    this.selected=state.selected;this.$('graph-depth').value=String(this.depth);this.$('graph-references').checked=this.references;this.$('graph-root-filter').value=this.rootFilter;
    this.renderColorGroups();this.onSelect(this.selected);this.updateHistoryButtons();
    await this.show({mode:state.mode,focusId:state.focusId,record:false,viewport:entry.viewport});
  }
  zoom(factor){const cy=this.cy;cy.zoom({level:Math.max(cy.minZoom(),Math.min(cy.maxZoom(),cy.zoom()*factor)),renderedPosition:{x:cy.width()/2,y:cy.height()/2}});}
  fit(){if(this.cy.nodes().length){this.cy.resize();this.cy.fit(this.cy.elements(),['focus','local'].includes(this.mode)?60:40);if(this.cy.nodes().length<10&&this.cy.zoom()>1.4){this.cy.zoom(1.4);this.cy.center();}}}
  resize(){this.cy.resize();}

  select(id){
    this.selected=id;this.cy.batch(()=>{
      this.cy.elements().removeClass('focus-node neighbor-node focus-edge');
      const node=this.cy.getElementById(id);
      if(node.length){node.addClass('focus-node');if(id!=='__msc__'){node.connectedEdges().addClass('focus-edge');node.neighborhood('node').addClass('neighbor-node');}}
    });
    const node=this.model.nodeMap.get(id);
    this.$('graph-selection-status').textContent=node?`${node.code} · ${node.title}`:'MSC2020 · выберите область или найдите нужную рубрику в каталоге';
    this.$('graph-expand').disabled=!node;
    this.$('graph-local').disabled=!node;this.renderInspector();this.renderBookmarks();
  }

  navigate(id){
    this.captureHistoryViewport();
    this.select(id);
    if(id==='__msc__'){this.setMode('overview');return;}
    if(this.mode==='full'&&this.cy.getElementById(id).length){
      const n=this.cy.getElementById(id);this.cy.zoom(Math.max(this.cy.zoom(),1.2));this.cy.center(n);this.remember();return;
    }
    if(this.mode==='local'){this.show({mode:'local',focusId:id});return;}
    this.show({mode:'focus',focusId:id});
  }
  openBranch(id){
    if(id==='__msc__')id='05';
    if(!this.model.nodeMap.has(id))return;
    this.captureHistoryViewport();this.select(id);this.onSelect(id);this.show({mode:'focus',focusId:id});
  }
  openLocal(id){
    if(id==='__msc__')id='05';
    if(!this.model.nodeMap.has(id))return;
    this.captureHistoryViewport();
    if(this.mode!=='local'){this.references=true;this.$('graph-references').checked=true;}
    this.select(id);this.onSelect(id);this.show({mode:'local',focusId:id});
  }
  setMode(mode){
    this.captureHistoryViewport();
    if(mode==='local'){this.openLocal(this.selected);return;}
    if(mode==='focus'){this.openBranch(this.selected);return;}
    if(mode==='overview'){this.selected='__msc__';this.onSelect('__msc__');}
    this.show({mode,focusId:mode==='overview'?'__msc__':this.selected});
  }

  positions(){const result={};this.cy.nodes().forEach(n=>{result[n.id()]={...n.position()};});return result;}
  validPositions(positions,nodes){return positions&&nodes.every(n=>Number.isFinite(positions[n.data.id]?.x)&&Number.isFinite(positions[n.data.id]?.y));}
  async show({mode,focusId,reset=false,record=true,viewport=null}){
    const key=JSON.stringify([mode,['focus','local'].includes(mode)?focusId:'',this.references,mode==='local'?this.depth:0,this.rootFilter,this.activeGroups?[...this.activeGroups].sort():null]);
    if(key===this.currentKey&&!reset&&this.container.getAttribute('aria-busy')!=='true'&&!this.container.dataset.error){this.select(this.selected);this.resize();if(viewport)this.cy.viewport(viewport);if(record)this.remember();return;}
    if(record)this.captureHistoryViewport();
    const sameScope=this.currentKey&&this.mode===mode&&this.focusId===focusId;
    const previousPositions=sameScope?this.positions():null;
    if(this.currentKey)this.cache.set(this.currentKey,this.positions());
    this.cancelLayout?.();const generation=++this.generation;
    this.mode=mode;this.focusId=focusId;this.$('graph-mode').value=mode;
    this.$('graph-depth-control').hidden=mode!=='local';
    const graph=this.decorateAndFilter(this.model.elements({mode,focusId,references:this.references,depth:this.depth}));
    if(mode==='focus'){
      const selected=this.model.nodeMap.get(focusId);
      let ancestor=selected?.level===2?this.model.nodeMap.get(selected.parent_id):selected;
      const context=new Set(['__msc__']);
      while(ancestor?.parent_id){context.add(ancestor.parent_id);ancestor=this.model.nodeMap.get(ancestor.parent_id);}
      graph.nodes=graph.nodes.map(n=>context.has(n.data.id)?{...n,data:{...n.data,size:14},classes:'context-node'}:n);
    }
    this.$('graph-loading').textContent=mode==='focus'?'Раскладываем выбранную ветвь…':'Открываем карту…';this.$('graph-loading').hidden=false;
    this.container.setAttribute('aria-busy','true');this.container.dataset.ready='false';delete this.container.dataset.error;this.hideTooltip();
    try{
      let positions=reset?null:this.cache.get(key);
      if(!positions&&!reset&&this.validPositions(previousPositions,graph.nodes))positions=previousPositions;
      if(!positions&&['overview','full'].includes(mode))positions=(await this.layoutCache)?.layouts[mode]?.positions;
      if(!positions&&graph.realNodeCount>700)positions=(await this.layoutCache)?.layouts.full?.positions;
      if(generation!==this.generation)return;
      if(!graph.nodes.length)positions={};
      else if(!this.validPositions(positions,graph.nodes))positions=await this.calculate(graph);
      if(generation!==this.generation)return;
      this.cy.batch(()=>{
        this.cy.elements().remove();
        this.cy.add(graph.nodes.map(n=>({...n,position:positions[n.data.id]})));
        this.cy.add(graph.edges);
      });
      this.graph=graph;this.currentKey=key;this.cache.set(key,positions);
      this.applyAppearance();this.select(this.selected);this.updateSummary();
      if(viewport)this.cy.viewport(viewport);else this.fit();
      this.container.dataset.ready='true';this.container.dataset.mode=mode;
    }catch(error){
      if(generation!==this.generation)return;
      this.$('graph-selection-status').textContent='Не удалось построить карту: '+error.message;
      this.container.dataset.error=error.message;
    }finally{
      if(generation===this.generation){this.$('graph-loading').hidden=true;this.container.setAttribute('aria-busy','false');if(record&&!this.container.dataset.error)this.remember();}
    }
  }

  calculate(graph){
    return new Promise((resolve,reject)=>{
      const worker=new Worker('/graph-layout-worker.js');this.worker=worker;
      const cleanup=()=>{worker.terminate();if(this.worker===worker){this.worker=null;this.cancelLayout=null;}};
      this.cancelLayout=()=>{cleanup();reject(Error('Раскладка отменена'));};
      worker.onmessage=({data})=>{cleanup();data.error?reject(Error(data.error)):resolve(data.positions);};
      worker.onerror=event=>{cleanup();reject(Error(event.message||'Ошибка раскладки fCoSE'));};
      worker.postMessage({elements:[...graph.nodes,...graph.edges]});
    });
  }

  updateSummary(){
    const graph=this.graph,node=this.model.nodeMap.get(this.focusId),format=n=>n.toLocaleString('ru-RU');
    this.$('graph-title').textContent=this.mode==='overview'?'MSC2020 · обзор областей':this.mode==='full'?'MSC2020 · весь классификатор':this.mode==='local'?`${node?.code} · локальные связи`:`${node?.code||''} · ${node?.title||'Выбранная ветвь'}`;
    this.$('graph-subtitle').textContent=this.mode==='overview'?'Цвет объединяет области. Наведите на узел, чтобы выделить его связи.':this.mode==='full'?'Все рубрики на одной карте. Используйте цветовые фильтры и поиск.':this.mode==='local'?`До ${this.depth} ${this.depth===1?'перехода':'переходов'} по связям MSC. Выберите соседа, чтобы продолжить исследование.`:'Все рубрики выбранной ветви; для конечной рубрики показаны и соседние темы.';
    this.$('graph-coverage').textContent=`${format(graph.realNodeCount)} из ${format(this.dataset.nodes.length)} рубрик · ${format(graph.referenceCount)} отсылок${this.references?'':' (скрыты)'}${this.mode==='local'?' · расстояние по классификатору':' · MSC2020 — навигационный центр'}`;
    if(!graph.realNodeCount)this.$('graph-selection-status').textContent='Фильтры скрыли все рубрики в этом виде. Сбросьте фильтры в настройках.';
  }

  snapshot(){return {library:cytoscape.version,layout:'fCoSE',mode:this.mode,ready:this.container.dataset.ready==='true',
    nodeCount:this.cy.nodes().length,realNodeCount:this.graph?.realNodeCount,edgeCount:this.cy.edges().length,
    referenceCount:this.graph?.referenceCount,selected:this.selected,zoom:this.cy.zoom(),pan:{...this.cy.pan()},
    layoutRunning:!!this.worker,sourceNodeCount:this.dataset.nodes.length,depth:this.depth,rootFilter:this.rootFilter,
    colorMode:this.colorMode,groups:this.activeGroups?[...this.activeGroups]:null,historyIndex:this.historyIndex,historyLength:this.history.length,bookmarks:[...this.bookmarks],immersive:this.immersive};}
}
globalThis.MSCGraphView=MSCGraphView;
