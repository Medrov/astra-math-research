(function (root, factory) {
  'use strict';
  const model = factory();
  if (typeof module === 'object' && module.exports) module.exports = model;
  if (root) root.ObjectGraphModel = model;
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';
  const STATUS = {
    hypothesis: {label:'Гипотеза', color:'#a48445', background:'#fbf5e9'},
    incomplete: {label:'Неполно', color:'#7c778d', background:'#f2f0f6'},
    needs_recheck: {label:'Нужна новая проверка', color:'#7c778d', background:'#f2f0f6'},
    proved: {label:'Доказано', color:'#407457', background:'#edf6ef'},
    refuted: {label:'Контрпример', color:'#a3664d', background:'#fbefea'},
    checking: {label:'Проверяется', color:'#527aa9', background:'#edf3fb'}
  };
  const RELATIONS = {identity:'Тождество', equivalence:'Эквивалентность', implication:'Следствие',
    construction:'Конструкция', representation:'Представление', correspondence:'Соответствие',
    reduction:'Сведение', analogy:'Аналогия', embedding:'Вложение', isomorphism:'Изоморфизм',
    invariant:'Инвариант', counterexample:'Контрпример', transfer:'Перенос результата', property_transfer:'Перенос свойства'};
  function array(value) { return Array.isArray(value) ? value : []; }
  function formulation(transition) {
    const task=transition?.agent_task;
    const formalized=transition?.formulation_status!=='literature_only'&&!!task&&!!task.target&&!!task.statement&&array(transition?.obligations).length>0;
    return {formalized,status:formalized?'formalized':transition?.formulation_status==='literature_only'?'literature_only':'unformalized',
      label:formalized?'Точная Lean-постановка подготовлена':transition?.formulation_status==='literature_only'?'Утверждение статьи · Lean-постановка ещё не подготовлена':'Lean-постановка ещё не подготовлена',
      action:formalized?'Проверить выбранный переход':'Формализовать и проверить'};
  }
  function defaultPaperSection(paper) {
    const sections=array(paper?.sections).filter(s=>array(s.chunk_ids).length>0);
    if(sections.some(s=>s.id===paper?.recommended_section_id))return paper.recommended_section_id;
    return sections.find(s=>!/(?:^|\b)(abstract|introduction|background|acknowledg\w*|references|bibliography|conclusion|related work|введение|литература|благодарности)(?:\b|$)/i.test(s.title||s.heading||''))?.id||'';
  }
  function paperScope(paper,sectionId='') {
    if(!paper)return {};
    if(!paper.versioned_id)throw new Error('Источник не имеет зафиксированной версии arXiv.');
    const ids=[...new Set(Array.isArray(sectionId)?sectionId:sectionId?[sectionId]:[])];
    if(ids.some(id=>!array(paper.sections).some(s=>s.id===id&&array(s.chunk_ids).length)))throw new Error('В этой версии статьи нет текста выбранного раздела.');
    return {paper_ids:[paper.versioned_id],section_ids:ids};
  }
  function sourcePaperScope(graph,transition) {
    const papers=new Set(),sections=new Set();
    for(const source of relatedSources(graph,transition)) {
      let id=source.versioned_id,section=source.section_id;
      if(!id&&source.url){try{const url=new URL(source.url);if(/^(?:www\.)?arxiv\.org$/i.test(url.hostname)){const candidate=url.pathname.replace(/^\/(?:abs|html|pdf)\//,'').replace(/\.pdf$/,'');if(/v\d+$/.test(candidate)){id=candidate;section=section||decodeURIComponent(url.hash.slice(1));}}}catch{}}
      if(id){papers.add(id);if(section)sections.add(section);}
    }
    return {paper_ids:[...papers],section_ids:[...sections]};
  }
  function transitionStatus(transition) {
    const value = transition?.status;
    if(transition?.formulation_status==='literature_only'&&['proved','verified','refuted','counterexample'].includes(value))return 'incomplete';
    if (['proved','verified'].includes(value)) return transition.certificate ? 'proved' : 'incomplete';
    if (['refuted','counterexample'].includes(value)) return transition.certificate ? 'refuted' : 'incomplete';
    if (['checking','running','queued','verifying'].includes(value)) return 'checking';
    if (value==='needs_recheck') return 'needs_recheck';
    if (['incomplete','partial','failed','interrupted','cancelled','budget_exhausted','needs_review','needs_recheck','unknown'].includes(value)) return 'incomplete';
    return 'hypothesis';
  }
  function presentation(transition) {
    const value = transitionStatus(transition);
    const item={status:value, ...STATUS[value]};
    if(value==='hypothesis'&&transition?.formulation_status==='literature_only')item.label='Утверждение статьи';
    return item;
  }
  function relationLabel(value) { return RELATIONS[value] || String(value || 'Переход').replaceAll('_',' '); }
  function obligationEvidence(transition, obligation) {
    const checked=array(transition?.certificate?.result?.verification?.obligations)
      .find(item=>item.id===obligation.id&&item.target===obligation.target);
    if(checked?.ok===true)return {status:'verified',label:obligation.expected_outcome==='refuted'?'Отрицание проверено в Lean':'Проверено в Lean'};
    const attempted=array(transition?.last_result?.result?.verification?.obligations)
      .find(item=>item.id===obligation.id&&item.target===obligation.target);
    return attempted?{status:'incomplete',label:'Проверка не завершена'}:{status:'pending',label:'Ожидает проверки'};
  }
  function proofSlice(graph,transition) {
    if(!transition)return graph;
    if(transition.formulation_status==='literature_only')return {nodes:[],edges:[]};
    const targets=new Set([...array(transition.obligations).map(o=>o.target),transition.agent_task?.target].filter(Boolean));
    const keep=new Set(array(graph.nodes).filter(n=>targets.has(n.id)||targets.has(n.target)||targets.has(n.name)).map(n=>String(n.id)));
    if(!keep.size)return graph;
    let changed=true;while(changed){changed=false;for(const edge of array(graph.edges)){if(keep.has(String(edge.target))&&!keep.has(String(edge.source))){keep.add(String(edge.source));changed=true;}}}
    return {nodes:array(graph.nodes).filter(n=>keep.has(String(n.id))),edges:array(graph.edges).filter(e=>keep.has(String(e.source))&&keep.has(String(e.target)))};
  }
  function elements(graph) {
    const objects = array(graph?.objects), transitions = array(graph?.transitions);
    const known = new Set(objects.map(o=>String(o.id)));
    const nodes = objects.map(o=>({data:{id:'object:'+o.id, entityId:String(o.id), kind:'object',
      label:o.title||o.id, display:o.title||o.id}}));
    const edges = [];
    for (const transition of transitions) {
      const p = presentation(transition), id = 'transition:'+transition.id;
      nodes.push({data:{id, entityId:String(transition.id), kind:'transition', status:p.status,
        label:transition.title||relationLabel(transition.relation_type),
        display:(transition.title||relationLabel(transition.relation_type))+'\n'+p.label}});
      for (const [side, endpoints] of [['source',transition.source_ids],['target',transition.target_ids]]) {
        for (const [index, endpoint] of array(endpoints).entries()) {
          if (!known.has(String(endpoint))) continue;
          edges.push({data:{id:`link:${transition.id}:${side}:${index}`, transitionId:String(transition.id),
            source:side==='source'?'object:'+endpoint:id, target:side==='source'?id:'object:'+endpoint,
            status:p.status, kind:'object_transition'}});
        }
      }
    }
    return [...nodes,...edges];
  }
  function selected(graph, selection) {
    if (!selection) return null;
    const split = selection.indexOf(':'), kind = selection.slice(0,split), id = selection.slice(split+1);
    const value = array(kind==='object'?graph?.objects:graph?.transitions).find(x=>String(x.id)===id);
    return value ? {kind, value} : null;
  }
  function relatedSources(graph, transition) {
    const refs = new Set([...array(transition?.source_refs),...array(transition?.sources),...array(transition?.source_ids_refs)]
      .map(s=>typeof s==='string'?s:s?.id).filter(Boolean));
    return refs.size ? array(graph?.sources).filter(s=>refs.has(s.id)) : array(graph?.sources);
  }
  function verificationPayload(graph, transition, {mode='single', budget, msc_codes=[]}={}) {
    if (!graph?.id || !Number.isInteger(graph.revision) || !transition?.id) throw new Error('Сначала сохраните граф и выберите переход.');
    if (!array(graph.transitions).some(t=>t.id===transition.id)) throw new Error('Переход отсутствует в этой версии графа.');
    if (mode==='pilot' && (!transition.case_id||transition.formulation_status==='literature_only')) throw new Error('Для этой постановки нет локального пилота. Выберите режим Astra.');
    const payload={purpose:'prove',graph_id:graph.id,graph_revision:graph.revision,transition_id:transition.id,
      mode,budget,msc_codes:msc_codes.length?msc_codes:array(graph.msc_codes)};
    if (transition.case_id) payload.case_id=transition.case_id;
    return payload;
  }
  function revisionDraft(graph) {
    const draft=JSON.parse(JSON.stringify(graph));
    for (const transition of array(draft.transitions)) {
      transition.status='hypothesis';
      transition.semantic_review={status:'pending'};
      delete transition.certificates; delete transition.certificate; delete transition.results;
      delete transition.last_result; delete transition.formal_outcome; delete transition.previous_certificate;
      delete transition.certificate_id; delete transition.certificate_ids;
      for(const obligation of array(transition.obligations)) {
        delete obligation.status;delete obligation.result;delete obligation.certificate;delete obligation.certificate_id;
      }
    }
    return draft;
  }
  class Workspace {
    constructor(callbacks) {
      this.callbacks=callbacks;this.graph=null;this.run=null;this.selection=null;this.cy=null;this.key='';this.editing=null;
      this.$=id=>document.getElementById(id);
      this.$('objects-fit').onclick=()=>this.fit();
      this.$('objects-edit').onclick=()=>this.edit();
      this.$('objects-edit-cancel').onclick=()=>this.closeEditor();
      this.$('objects-edit-form').onsubmit=event=>{event.preventDefault();this.saveRevision();};
      this.$('objects-custom-research').onclick=()=>this.customResearch();
      this.$('objects-library').onchange=event=>{if(event.target.value)this.open(event.target.value);};
      this.$('objects-refresh').onclick=()=>this.refreshLibrary();
      this.$('objects-graph').addEventListener('keydown',event=>{
        if(!this.cy)return;
        if(event.key==='0'){this.fit();event.preventDefault();}
        else if(['+','=','-'].includes(event.key)){this.cy.zoom(this.cy.zoom()*(event.key==='-'?1/1.2:1.2));event.preventDefault();}
      });
      new ResizeObserver(()=>{if(!this.$('research-objects-view').hidden){this.cy?.resize();}}).observe(this.$('objects-graph'));
    }
    node(tag,attrs={},text) {
      const element=document.createElement(tag);
      for(const [key,value] of Object.entries(attrs)){if(key==='class')element.className=value;else element.setAttribute(key,String(value));}
      if(text!==undefined)element.textContent=typeof text==='string'?text:String(text??'');return element;
    }
    text(value) {
      if(value===undefined||value===null)return '';
      if(typeof value==='string')return value;
      if(Array.isArray(value))return value.map(item=>this.text(item)).join('\n');
      if(typeof value==='object')return Object.entries(value).map(([key,item])=>key+': '+this.text(item)).join('\n');
      return String(value);
    }
    section(box,title,value) {
      if(value===undefined||value===null||value===''||(Array.isArray(value)&&!value.length))return;
      box.append(this.node('h4',{},title),this.node('p',{class:'objects-value'},this.text(value)));
    }
    badge(transition) {const p=presentation(transition);return this.node('span',{class:'research-status '+p.status},p.label);}
    details(title,value) {const d=this.node('details',{class:'research-raw'});d.append(this.node('summary',{},title),this.node('pre',{},typeof value==='string'?value:JSON.stringify(value,null,2)));return d;}
    report(error){this.callbacks.onError?.(error.message||String(error));}
    async refreshLibrary() {
      try {
        const data=await this.callbacks.api('/api/objects/graphs'),graphs=array(data.graphs||data);
        const select=this.$('objects-library');select.replaceChildren(this.node('option',{value:''},'Выбрать сохранённый граф…'));
        for(const graph of graphs)select.append(this.node('option',{value:graph.id},(graph.title||'Граф объектов')+' · v'+(graph.revision||graph.latest_revision||1)));
        if(this.graph?.id&&graphs.some(g=>g.id===this.graph.id))select.value=this.graph.id;
        this.$('objects-library-status').textContent=graphs.length?graphs.length+' сохранённых графов':'Граф появится здесь после первого запуска.';
      } catch(error) {this.$('objects-library-status').textContent='Не удалось загрузить графы: '+error.message;}
    }
    async open(id,revision) {
      const token=this.loadToken={};
      try {const graph=await this.callbacks.api('/api/objects/graphs/'+encodeURIComponent(id)+(revision?'?revision='+encodeURIComponent(revision):''));if(this.loadToken===token)this.callbacks.onGraph?.(graph.graph||graph);}
      catch(error){if(this.loadToken===token)this.report(error);}
    }
    setGraph(graph,run=null) {
      const previous=this.graph,identityChanged=(previous?.id||previous?.title)!==(graph?.id||graph?.title),changed=identityChanged||previous?.revision!==graph?.revision;
      this.graph=graph||null;this.run=run;
      this.$('objects-library').value=graph?.id||'';
      if(identityChanged)this.selection=null;
      if(changed)this.closeEditor();
      const selectedId=run?.selected_transition_id||run?.transition_id;
      if(!this.selection&&selectedId)this.selection='transition:'+selectedId;
      if(!selected(this.graph,this.selection))this.selection=graph?.transitions?.[0]?'transition:'+graph.transitions[0].id:graph?.objects?.[0]?'object:'+graph.objects[0].id:null;
      this.render();
    }
    render() {
      const graph=this.graph,items=elements(graph),hasItems=items.some(x=>!x.data.source);
      this.$('objects-title').textContent=graph?.title||'Объекты и переходы';
      const version=this.$('objects-version');version.replaceChildren();
      if(graph?.id){
        const choice=this.node('select',{'aria-label':'Версия графа',class:'objects-revision-select'}),latest=graph.current_revision||graph.revision;
        const revisions=[...new Set([graph.revision,...Array.from({length:Math.min(latest,30)},(_,i)=>latest-i)])].sort((a,b)=>b-a);
        for(const revision of revisions)choice.append(this.node('option',{value:revision},'Версия '+revision+(revision===latest?' · текущая':'')));
        choice.value=String(graph.revision);choice.onchange=()=>this.open(graph.id,Number(choice.value));version.append(choice,this.node('span',{},' '+(graph.semantic_hash||'').slice(0,10)));
      }else if(graph)version.textContent='Предварительная постановка · ещё не проверена';
      const historical=graph?.id&&graph.current_revision>graph.revision;
      this.$('objects-edit').disabled=!graph||historical||['queued','running','cancelling'].includes(this.run?.status);
      this.$('objects-edit').title=historical?'Выбрана историческая версия. Откройте текущую версию, чтобы уточнить постановку.':'';
      this.$('objects-empty').hidden=hasItems;
      const buttons=this.$('objects-item-list');buttons.replaceChildren();
      for(const item of items.filter(x=>!x.data.source)) {
        const data=item.data,button=this.node('button',{type:'button','data-object-item':data.id,class:this.selection===data.id?'selected':''},(data.kind==='transition'?'↗ ':'')+data.label);
        button.onclick=()=>this.select(data.id,true);buttons.append(button);
      }
      if(!hasItems){this.cy?.elements().remove();this.key='';this.topology='';this.inspect();return;}
      if(!window.cytoscape){this.$('objects-empty').hidden=false;this.$('objects-empty').replaceChildren(this.node('p',{},'Графическая библиотека недоступна. Выберите объект или переход в списке.'));this.inspect();return;}
      const key=JSON.stringify(items);
      if(this.key!==key) {
        const positions=new Map(this.cy?.nodes().map(n=>[n.id(),{...n.position()}])||[]);
        const topology=items.filter(x=>!x.data.source).map(x=>x.data.id).join('|')+';'+items.filter(x=>x.data.source).map(x=>x.data.source+'>'+x.data.target).join('|');
        const layoutChanged=topology!==this.topology;
        if(!this.cy) {
          this.cy=window.cytoscape({container:this.$('objects-graph'),elements:items,layout:{name:'preset'},minZoom:.18,maxZoom:3,wheelSensitivity:.18,style:[
            {selector:'node',style:{shape:'round-rectangle',width:232,height:100,'background-color':'#eef3fa','border-color':'#aebfd5','border-width':1.5,label:'data(display)','font-family':'Segoe UI,sans-serif','font-size':16,'text-wrap':'wrap','text-max-width':208,'text-valign':'center','text-halign':'center',color:'#43546b'}},
            {selector:'node[kind="transition"]',style:{shape:'round-diamond',width:244,height:144,'background-color':'#fbf5e9','border-color':'#c8ad77','border-style':'dashed',color:'#806b44','text-max-width':204}},
            {selector:'node[status="proved"]',style:{'background-color':'#edf6ef','border-color':'#80a98c','border-style':'solid',color:'#407457'}},
            {selector:'node[status="refuted"]',style:{'background-color':'#fbefea','border-color':'#c48e74','border-style':'solid',color:'#9c624a'}},
            {selector:'node[status="incomplete"], node[status="needs_recheck"]',style:{'background-color':'#f2f0f6','border-color':'#b7b1c2',color:'#7c778d'}},
            {selector:'node[status="checking"]',style:{'background-color':'#edf3fb','border-color':'#7395c4','border-width':3,color:'#527aa9'}},
            {selector:'edge',style:{'curve-style':'bezier',width:1.4,'line-color':'#b9bec7','target-arrow-color':'#b9bec7','target-arrow-shape':'triangle','arrow-scale':.85,'line-style':'dashed'}},
            {selector:'edge[status="proved"]',style:{'line-style':'solid','line-color':'#8cae97','target-arrow-color':'#8cae97'}},
            {selector:'node:selected',style:{'border-color':'#323944','border-width':3}}
          ]});
          this.$('objects-graph').objectGraph=this.cy;
          this.cy.on('tap','node',event=>this.select(event.target.id(),true));
          this.cy.on('tap','edge',event=>this.select('transition:'+event.target.data('transitionId'),true));
        } else this.cy.json({elements:items});
        if(layoutChanged){this.cy.layout({name:'dagre',rankDir:'TB',nodeSep:45,rankSep:35,edgeSep:15,animate:false,padding:30}).run();requestAnimationFrame(()=>this.fit());}
        else this.cy.nodes().forEach(n=>{if(positions.has(n.id()))n.position(positions.get(n.id()));});
        this.topology=topology;this.key=key;
      }
      this.select(this.selection);
    }
    select(id,pan=false) {
      this.selection=id;this.cy?.nodes().unselect();
      if(this.cy&&id){const node=this.cy.getElementById(id);node.select();if(pan){this.cy.stop();if(this.cy.zoom()<.9)this.cy.zoom(.9);this.cy.center(node);}}
      for(const button of this.$('objects-item-list').querySelectorAll('button'))button.classList.toggle('selected',button.dataset.objectItem===id);
      const entry=selected(this.graph,id);if(entry?.kind==='transition')this.callbacks.onSelect?.(entry.value);
      this.inspect();
    }
    fit(){if(this.cy?.nodes().length&&!this.$('research-objects-view').hidden){this.cy.stop();this.cy.resize();this.cy.fit(undefined,35);if(this.cy.zoom()>1.1){this.cy.zoom(1.1);this.cy.center();}}}
    inspect() {
      const box=this.$('objects-inspector'),entry=selected(this.graph,this.selection);box.replaceChildren();
      if(!entry){box.append(this.node('p',{class:'research-small-label'},'Объекты и переходы'),this.node('h3',{},'Выберите отправную точку'),this.node('p',{class:'research-hint'},'Здесь будут определения объектов, точная связь и условия её проверки.'));return;}
      const item=entry.value;box.append(this.node('p',{class:'research-small-label'},entry.kind==='object'?'Математический объект':relationLabel(item.relation_type)),this.node('h3',{},item.title||item.id));
      if(entry.kind==='object') {
        this.section(box,'Определение',item.definition);this.section(box,'Параметры',item.parameters);this.section(box,'Условия',item.assumptions);
        const tags=this.node('div',{class:'research-msc-tags'});for(const code of array(item.msc_codes)){const b=this.node('button',{type:'button'},code);b.onclick=()=>this.callbacks.onMSC?.(code);tags.append(b);}box.append(tags);
        this.section(box,'Формальные определения',item.lean_refs);
        const relations=array(this.graph.transitions).filter(t=>[...array(t.source_ids),...array(t.target_ids)].includes(item.id));
        if(relations.length){box.append(this.node('h4',{},'Связанные переходы'));for(const transition of relations){const b=this.node('button',{type:'button',class:'objects-relation-link'},transition.title||transition.id);b.onclick=()=>this.select('transition:'+transition.id,true);box.append(b);}}
        return;
      }
      box.append(this.badge(item));
      const formal=formulation(item);
      if(!formal.formalized)box.append(this.node('p',{class:'objects-formulation-note','data-formulation-status':formal.status},formal.label));
      this.section(box,'Утверждение',item.claim);this.section(box,'Условия перехода',item.assumptions);this.section(box,'Преобразование',item.construction);
      const names=ids=>array(ids).map(id=>this.graph.objects.find(o=>o.id===id)?.title||id).join(' + ');
      this.section(box,'Откуда → куда',names(item.source_ids)+' → '+names(item.target_ids));
      const actions=this.node('div',{class:'objects-transition-actions'}),verify=this.node('button',{type:'button',class:'button primary','data-verify-transition':item.id},formal.action);
      verify.disabled=['queued','running','cancelling'].includes(this.run?.status);
      verify.onclick=()=>this.callbacks.onVerify?.(this.graph,item);actions.append(verify);
      const proof=this.node('button',{type:'button',class:'button secondary'},'Открыть граф лемм →');proof.disabled=!formal.formalized;proof.title=formal.formalized?'':'Сначала нужно подготовить точную постановку и обязательства Lean.';proof.onclick=()=>this.callbacks.onProof?.(null,item);actions.append(proof);box.append(actions);
      const obligations=array(item.obligations);box.append(this.node('h4',{},'Обязательства доказательства · '+obligations.length));
      if(!obligations.length)box.append(this.node('p',{class:'research-hint'},'Формальные обязательства ещё не заданы. Сначала требуется формализация постановки.'));
      for(const obligation of obligations) {
        const card=this.node('div',{class:'objects-obligation'}),button=this.node('button',{type:'button','data-obligation-id':obligation.id},obligation.title||obligation.target||obligation.id);
        button.onclick=()=>this.callbacks.onProof?.(obligation.target||obligation.id,item);card.append(button);
        const evidence=obligationEvidence(item,obligation);
        card.append(this.node('span',{class:'research-hint','data-obligation-status':evidence.status},evidence.label));
        if(obligation.expected_outcome==='refuted')card.append(this.node('p',{class:'research-hint'},'Цель — проверить отрицание утверждения.'));
        if(obligation.statement)card.append(this.details('Точное утверждение',obligation.statement));box.append(card);
      }
      const review=item.semantic_review||{};
      this.section(box,'Соответствие замыслу',review.reason||review.summary||({aligned:'Соответствие проверено отдельно от Lean.',reviewed_fixture:'Подготовленная постановка сверена.',mismatch:'Обнаружено расхождение с постановкой.',uncertain:'Нужна содержательная проверка.',pending:'Содержательная проверка ещё не выполнена.'}[review.status]||'Содержательная проверка ещё не выполнена.'));
      if(review.limitations)this.section(box,'Ограничения',review.limitations);
      const sources=relatedSources(this.graph,item);if(sources.length){box.append(this.node('h4',{},'Источники'));for(const source of sources){const p=this.node('p',{class:'objects-source'},source.title||source.id);let url;try{const parsed=new URL(source.url,location.origin);if(source.url&&['http:','https:'].includes(parsed.protocol))url=parsed.href;}catch{}if(url){const a=this.node('a',{href:url,target:'_blank',rel:'noopener noreferrer'},'Открыть ↗');p.append(a);}if(source.locator)p.append(this.node('small',{},this.text(source.locator)));box.append(p);}}
      if(item.certificate)box.append(this.details('Свидетельство проверки',item.certificate));
      if(item.last_result)box.append(this.details('Последний результат',item.last_result));
      if(item.status==='needs_recheck')box.append(this.node('p',{class:'research-hint'},'Постановка изменена. Для этой версии нужна новая проверка.'));
    }
    input(box,label,value,setter,{rows=3,lines=false}={}) {
      const id='object-editor-'+(++this.fieldIndex),field=this.node('textarea',{id,rows});field.value=this.text(value);
      const wrapper=this.node('div',{class:'objects-editor-field'});wrapper.append(this.node('label',{for:id},label),field);box.append(wrapper);
      field.oninput=()=>setter(lines?field.value.split('\n').map(s=>s.trim()).filter(Boolean):field.value);return field;
    }
    edit() {
      if(!this.graph)return;this.editing=revisionDraft(this.graph);this.fieldIndex=0;const graph=this.editing,box=this.$('objects-edit-fields');box.replaceChildren();
      this.input(box,'Название графа',graph.title,value=>graph.title=value,{rows:1});
      this.input(box,'Исследовательский вопрос',graph.question,value=>graph.question=value);
      for(const object of array(graph.objects)) {
        const group=this.node('fieldset');group.append(this.node('legend',{},object.title||object.id));
        this.input(group,'Определение',object.definition,value=>object.definition=value);this.input(group,'Условия · по одному на строку',object.assumptions,value=>object.assumptions=value,{lines:true});box.append(group);
      }
      for(const transition of array(graph.transitions)) {
        const group=this.node('fieldset');group.append(this.node('legend',{},transition.title||transition.id));
        this.input(group,'Утверждение перехода',transition.claim,value=>transition.claim=value);this.input(group,'Условия перехода · по одному на строку',transition.assumptions,value=>transition.assumptions=value,{lines:true});
        this.input(group,'Преобразование',transition.construction,value=>transition.construction=value);
        const formal=this.node('details',{class:'objects-formal-editor'});formal.append(this.node('summary',{},'Формальная постановка Lean'));
        formal.append(this.node('p',{class:'research-hint'},'Все переменные и условия должны присутствовать в типах целей. Новая формулировка требует нового доказательства.'));
        if(transition.agent_task){const task=transition.agent_task;
          this.input(formal,'Импорты · по одному на строку',task.imports,value=>task.imports=value,{lines:true});
          this.input(formal,'Определения и контекст Lean',task.prelude,value=>task.prelude=value,{rows:8});
          formal.append(this.node('p',{class:'research-hint'},'Итоговая цель: '+task.target+'. Её имя и тип редактируются в соответствующем обязательстве ниже.'));
        }
        for(const obligation of array(transition.obligations)) {
          const heading=this.node('h4',{},obligation.title||obligation.id);formal.append(heading);
          this.input(formal,'Имя цели',obligation.target,value=>{if(transition.agent_task?.target===obligation.target)transition.agent_task.target=value;obligation.target=value;},{rows:1});
          this.input(formal,'Точное утверждение',obligation.statement,value=>{if(transition.agent_task?.target===obligation.target)transition.agent_task.statement=value;obligation.statement=value;},{rows:5});
        }
        group.append(formal);box.append(group);
      }
      this.$('objects-editor').hidden=false;this.$('objects-edit-save').disabled=!graph.id;
      if(!graph.id)box.prepend(this.node('p',{class:'research-hint'},'Это предварительный пример. Изменения можно перенести в новый вопрос для Astra. Сохранённый граф поддерживает отдельные версии.'));
      this.$('objects-editor').scrollIntoView({behavior:'smooth',block:'start'});
    }
    closeEditor(){this.editing=null;this.$('objects-editor').hidden=true;}
    async saveRevision() {
      if(!this.editing?.id)return;const button=this.$('objects-edit-save'),draft=this.editing;button.disabled=true;
      try {const graph=await this.callbacks.api('/api/objects/graphs/'+encodeURIComponent(draft.id)+'/revisions',{graph:draft,expected_revision:this.graph.revision});if(this.editing===draft){this.closeEditor();this.callbacks.onGraph?.(graph.graph||graph);}await this.refreshLibrary();}
      catch(error){this.report(error);}finally{button.disabled=!this.editing?.id;}
    }
    customResearch() {
      const graph=this.editing||this.graph;if(!graph)return;
      const parts=[graph.question||graph.title,'Объекты:',...array(graph.objects).map(o=>(o.title||o.id)+': '+this.text(o.definition)+'\nУсловия: '+this.text(o.assumptions)),
        'Проверяемые переходы:',...array(graph.transitions).map(t=>(t.title||t.id)+': '+this.text(t.claim)+'\nУсловия: '+this.text(t.assumptions)+'\nПреобразование: '+this.text(t.construction))];
      this.closeEditor();this.callbacks.onCustom?.(parts.filter(Boolean).join('\n\n'),array(graph.msc_codes));
    }
  }
  return {STATUS, transitionStatus, presentation, formulation, defaultPaperSection, paperScope, sourcePaperScope, relationLabel, obligationEvidence, proofSlice, elements, selected, relatedSources,
    verificationPayload, revisionDraft, Workspace};
});
