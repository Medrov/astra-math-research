/* Read-only graph presentation. Verification is requested only through onVerify. */
(function(root,factory){const api=factory(root);if(typeof module==='object'&&module.exports)module.exports=api;else root.ResearchMap=api;})(typeof globalThis==='undefined'?this:globalThis,function(root){
  'use strict';
  const list=value=>Array.isArray(value)?value:[];
  const str=value=>value==null?'':String(value);
  const compact=value=>str(value).replace(/\s+/g,' ').trim();
  const brief=(value,max=45)=>{const t=compact(value);return t.length>max?t.slice(0,max-1).trimEnd()+'…':t;};
  const active=new Set(['queued','running','cancelling']);
  const localAppearance=typeof module==='object'&&module.exports?require('./research-appearance.js'):null;
  const appearanceAPI=()=>root.ResearchAppearance||localAppearance;
  const palette={object:['#edf3fc','#4d6786'],defined:['#edf3fc','#4d6786'],pending:['#f3f4f7','#687183'],hypothesis:['#fbf5e9','#876a37'],proved:['#edf6ef','#407457'],refuted:['#fbefea','#a3664d'],formal_only:['#fbf5e9','#876a37'],checking:['#edf3fb','#527aa9'],incomplete:['#f2f0f6','#7c778d'],needs_recheck:['#f2f0f6','#7c778d']};
  const edgeNames={proof_dependency:'Зависимость доказательства',type_dependency:'Зависимость типа',planned_dependency:'Запланированная зависимость',object_transition:'Объект и переход'};
  function terminal(run){return ['complete','completed'].includes(run?.status);}
  function reportPassed(report,target){return !!report&&report.success===true&&report.target_preserved===true&&report.audit?.status==='passed'&&report.target===target;}
  function finalTarget(run){return run?.formal_contract?.target||run?.result?.verification?.target||run?.object_graph?.transitions?.find(t=>t.id===run.selected_transition_id)?.agent_task?.target||'';}
  function compiledTheoremEvidence(run,node){
    const target=node.target||node.name||node.id,graph=run?.object_graph,transition=list(graph?.transitions).find(item=>item.id===run?.selected_transition_id),certificate=transition?.certificate,report=run?.result?.verification,saved=certificate?.result?.verification;
    if(!terminal(run)||run?.purpose!=='prove'||node.planned||node.extraction!=='lean_environment'||!node.statement||!graph||graph.id!==run.graph_ref?.id||graph.revision!==run.graph_ref?.revision)return false;
    if(!certificate||certificate.run_id!==run.id||certificate.graph_id!==graph.id||certificate.revision!==graph.revision||certificate.transition_id!==transition.id||list(certificate.validation_errors).length)return false;
    if(!reportPassed(report,finalTarget(run))||!reportPassed(saved,finalTarget(run))||report.compilation_success!==true||saved.compilation_success!==true||report.obligations_passed!==true||saved.obligations_passed!==true)return false;
    for(const key of ['source_sha256','olean_sha256','environment_fingerprint'])if(!/^[a-f0-9]{64}$/i.test(report[key]||'')||report[key]!==saved[key])return false;
    if(certificate.environment_fingerprint!==report.environment_fingerprint||graph.environment_fingerprint!==report.environment_fingerprint||(graph.active_environment_fingerprint&&graph.active_environment_fingerprint!==report.environment_fingerprint))return false;
    for(const checked of [report,saved]){
      if(!list(checked.audit.audited_roots).includes(target))return false;
      const declaration=list(checked.declarations).find(item=>item.name===target&&item.kind==='theorem'&&item.module==='Candidate');
      if(!declaration||declaration.unsafe!==false||compact(declaration.type)!==compact(node.statement))return false;
    }
    return true;
  }
  function proofStatus(run,node,verdict=root.GuidedResearch?.verdict){
    const target=node.target||node.name||node.id;
    if(target===finalTarget(run)){
      const result=typeof verdict==='function'?verdict(run):null;
      const checked=!active.has(run?.status)&&(terminal(run)||run.result?.verification?.compilation_success===true)&&reportPassed(run.result?.verification,target)&&run.result.verification.obligations_passed===true;
      if(terminal(run)&&checked&&result?.kind==='proved')return {status:'proved',label:'Итог проверен в Lean'};
      if(terminal(run)&&checked&&result?.kind==='refuted'&&['aligned','reviewed_fixture'].includes((run.result?.semantic_review||run.semantic_review)?.status))return {status:'refuted',label:'Контрпример проверен в Lean'};
      if(checked&&result?.kind==='formal_only')return {status:'formal_only',label:'Lean-цель проверена · смысл не подтверждён'};
      return {status:active.has(run?.status)?'checking':'incomplete',label:active.has(run?.status)?'Итог проверяется':'Итог не подтверждён'};
    }
    if(['def','definition','opaque','inductive','structure'].includes(node.kind))return {status:'defined',label:'Определение · не отдельная цель'};
    const report=run?.result?.verification;
    const obligation=list(run?.formal_contract?.required_obligations).find(o=>o.target===target);
    if(terminal(run)&&reportPassed(report,finalTarget(run))&&report.obligations_passed===true&&obligation&&list(report.obligations).some(o=>o.id===obligation.id&&o.target===target&&o.ok===true&&o.expected_outcome===obligation.expected_outcome))return {status:obligation.expected_outcome==='refuted'?'refuted':'proved',label:obligation.expected_outcome==='refuted'?'Отрицание проверено в Lean':'Обязательство проверено в Lean'};
    if(compiledTheoremEvidence(run,node))return {status:'proved',label:'Проверено в итоговой сборке'};
    const nodeReports=[node.verification,node.result?.verification,node.report?.verification,node.last_result?.verification];
    const verified=nodeReports.find(r=>reportPassed(r,target)&&(!node.statement||compact(node.statement)===compact(r.expected_statement||r.actual_statement)));
    if(verified)return {status:verified.outcome==='refuted'?'refuted':'proved',label:verified.outcome==='refuted'?'Отрицание проверено в Lean':'Проверено отчётом Lean'};
    if(['running','checking','verifying'].includes(node.status))return {status:'checking',label:'Проверяется'};
    if(['failed','rejected','interrupted','cancelled'].includes(node.status))return {status:'incomplete',label:'Проверка не завершена'};
    return {status:'pending',label:'Нет подтверждающего отчёта'};
  }
  function defaultView(){return 'objects';}
  function shortLabel(value){return brief(str(value).split('.').at(-1).replaceAll('_',' '),22);}
  function canvasLabel(value){const label=compact(value);if(label.length<=18)return label;const spaces=Array.from(label.matchAll(/ /g),m=>m.index);if(!spaces.length)return label;const middle=spaces.reduce((a,b)=>Math.abs(b-label.length/2)<Math.abs(a-label.length/2)?b:a);return label.slice(0,middle)+'\n'+label.slice(middle+1);}
  function labelMetrics(){return {size:26,width:52};}
  function numberModel(model,numbers=new Map()){
    let next=Math.max(0,...numbers.values())+1;
    for(const node of model.nodes){if(!numbers.has(node.id))numbers.set(node.id,next++);node.number=numbers.get(node.id);}
    return model;
  }
  function transitionContext(model,selected){
    const id=typeof selected==='string'?selected:selected?.id,transition=list(model?.nodes).find(node=>node.id===id&&node.kind==='transition');if(!transition)return null;
    const objects=new Map(list(model.nodes).filter(node=>node.kind==='object').map(node=>[str(node.value?.id),node]));
    const endpoints=ids=>[...new Set(list(ids).map(str))].map(objectId=>{const node=objects.get(objectId);return node?{id:node.id,objectId,number:node.number,title:node.title,missing:false}:{id:null,objectId,number:null,title:'Объект «'+(objectId||'пустой идентификатор')+'» не найден в карте',missing:true};});
    const inputs=endpoints(transition.value.source_ids),outputs=endpoints(transition.value.target_ids),missing=[...new Set([...inputs,...outputs].filter(item=>item.missing).map(item=>item.objectId))];
    return {transition,inputs,outputs,missing,endpointsComplete:inputs.length>0&&outputs.length>0&&missing.length===0};
  }
  function endpointRole(context,id){if(!context)return '';const input=context.inputs.some(item=>!item.missing&&item.id===id),output=context.outputs.some(item=>!item.missing&&item.id===id);return input&&output?'both':input?'input':output?'output':'';}
  function endpointLabel(role){return ({input:'Вход перехода',output:'Выход перехода',both:'Вход и выход перехода'})[role]||'';}
  function kindLabel(node){return node.kind==='object'?'Объект':node.kind==='transition'?'Переход':node.value?.planned?'План леммы':node.goal?'Итоговая цель':['def','definition','opaque','inductive','structure'].includes(node.value?.kind)?'Определение':'Лемма';}
  function shortStatus(node){if(node.value?.formulation_status==='literature_only')return node.statusLabel;return ({object:'',defined:'Определение',pending:node.value?.planned?'План · не проверено':'Не проверено',hypothesis:'Кандидат',proved:'Проверено',refuted:'Контрпример',formal_only:'Смысл не подтверждён',checking:'Проверяется',incomplete:'Проверка не завершена',needs_recheck:'Нужна новая проверка'})[node.status]||node.statusLabel;}
  function appearanceFor(node){
    if(node.kind==='proof'){const colors=palette[node.status]||palette.pending;return {classification:'status',label:node.statusLabel,families:[],fill:colors[0],border:colors[1],text:'#26364b',shape:'round-rectangle',tint:colors[0]};}
    return appearanceAPI()?.forNode(node,node.mscContext)||{classification:'unknown',label:'Область не определена',families:[],fill:node.kind==='transition'?'#64748b':'#eef1f5',border:'#64748b',text:node.kind==='transition'?'#ffffff':'#243247',shape:node.kind==='transition'?'round-hexagon':'round-rectangle',tint:'#f8fafc'};
  }
  function priorAttempt(run,transition,runs=[]){
    const graph=run?.object_graph,match=ref=>!!graph?.id&&ref?.id===graph.id&&ref.revision===graph.revision;
    const matches=list(runs).filter(item=>item.id&&item.selected_transition_id===transition?.id&&(!item.purpose||item.purpose==='prove')&&(match(item.graph_ref)||match(item.source_graph_ref)))
      .map((item,index)=>({item,index,time:Date.parse(item.finished_at||item.updated_at||item.created_at)||0})).sort((a,b)=>b.time-a.time||a.index-b.index);
    if(matches.length){const item=matches[0].item;return {runId:item.id,label:terminal(item)?'Открыть проверку':'Открыть попытку',origin:'history'};}
    const validRecord=record=>record?.run_id&&(record.graph_id===undefined||record.graph_id===graph?.id)&&(record.revision===undefined||record.revision===graph?.revision)&&(record.transition_id===undefined||record.transition_id===transition?.id);
    const last=validRecord(transition?.last_result)?transition.last_result:null,certificate=validRecord(transition?.certificate)?transition.certificate:null;
    if(last?.run_id)return {runId:last.run_id,label:certificate?.run_id===last.run_id?'Открыть проверку':'Открыть попытку',origin:'record'};
    if(certificate?.run_id)return {runId:certificate.run_id,label:'Открыть проверку',origin:'certificate'};
    if(run?.id&&run.purpose==='prove'&&run.selected_transition_id===transition?.id&&(!run.graph_ref||match(run.graph_ref)))return {runId:run.id,label:terminal(run)?'Открыть проверку':'Открыть попытку',origin:'current'};
    return null;
  }
  function sourceTransition(run){const snapshot=run?.contract?.source_transition||list(run?.object_graph?.sources).find(source=>source?.structure_transition)?.structure_transition;return snapshot?.kind==='literature_transition'&&snapshot.graph_ref?.id&&snapshot.transition?.id?snapshot:null;}
  function transitionRole(run,transition){
    if(transition?.formulation_status==='candidate'||run?.purpose==='structure'||sourceTransition(run)||list(run?.structure_routes).some(route=>list(route.candidates).some(candidate=>candidate.transition_id===transition?.id)))return 'bridge';
    const article=list(run?.object_graph?.sources).some(source=>source?.versioned_id||/^https?:\/\/(?:www\.)?arxiv\.org\//i.test(source?.url||''));
    return transition?.formulation_status==='literature_only'&&article?'article':'direct';
  }
  function descendants(node){return [node,...Array.from(node.children||[]).flatMap(descendants)];}
  function summaryFor(run,kind,value,renderer=root.MathPresentation){try{return renderer?.entitySummary?.(run,kind,value)||null;}catch{return null;}}
  function ancestors(nodes,edges,targets){
    const keep=new Set(nodes.filter(n=>targets.has(n.value.target||n.value.name||n.value.id)).map(n=>n.id));
    let changed=true;while(changed){changed=false;for(const edge of edges)if(keep.has(edge.target)&&!keep.has(edge.source)){keep.add(edge.source);changed=true;}}
    return keep;
  }
  function buildModel(run,options={}){
    const view=options.view||defaultView(run),objectModel=options.objectModel||root.ObjectGraphModel,renderer=options.renderer||root.MathPresentation;
    const graph=run?.object_graph,focus=options.focusTransitionId===undefined?run?.selected_transition_id:options.focusTransitionId,scope='all';
    const transition=list(graph?.transitions).find(t=>t.id===focus)||null;
    const model={view,nodes:[],edges:[],transition,emptyReason:'',scope,focusTransitionId:focus,counts:{obligations:0,verified:0}};
    if(view==='objects'){
      if(!graph||typeof objectModel?.elements!=='function'){model.emptyReason='Объектная карта ещё не получена.';return model;}
      const values=new Map([...list(graph.objects).map(v=>['object:'+v.id,v]),...list(graph.transitions).map(v=>['transition:'+v.id,v])]);
      const items=objectModel.elements(graph);
      for(const item of items){const d=item.data;if(d.source!==undefined)continue;const value=values.get(d.id);if(!value)continue;
        const status=d.kind==='transition'?objectModel.presentation(value):{status:'object',label:'Математический объект'};
        const summary=summaryFor(run,d.kind,value,renderer),route=list(run?.structure_routes).find(r=>list(r.candidates).some(c=>c.transition_id===value.id));
        const routeCode=route?.msc_code||list(value.msc_codes)[0];
        const label=summary?.graphLabel||value.title||summary?.title||(d.kind==='transition'&&routeCode?'MSC '+routeCode:value.id);
        model.nodes.push({id:d.id,kind:d.kind,value,title:summary?.title||value.title||value.id,label,status:status.status,statusLabel:status.label,shape:'round-rectangle'});
      }
      const ids=new Set(model.nodes.map(n=>n.id));for(const item of items){const d=item.data;if(d.source!==undefined&&ids.has(d.source)&&ids.has(d.target))model.edges.push({id:d.id,source:d.source,target:d.target,type:d.kind||'object_transition',value:{...d}});}
      if(!model.nodes.length)model.emptyReason='В сохранённой карте пока нет объектов и переходов.';
      return numberModel(model);
    }
    if(run?.purpose!=='prove'){model.emptyReason='В этом запуске исследовались связи. Откройте отдельную проверку перехода для просмотра лемм.';return model;}
    if(focus&&focus!==run?.selected_transition_id){model.emptyReason='У выбранной связи пока нет доказательства в этом запуске. Выберите «Объекты» для её формализации.';return model;}
    if(graph&&run?.graph_ref&&(graph.id!==run.graph_ref.id||graph.revision!==run.graph_ref.revision)){model.emptyReason='Доказательство относится к другой версии объектной карты. Откройте связанный с ним запуск.';return model;}
    if(graph&&run?.selected_transition_id&&!transition){model.emptyReason='Выбранный переход отсутствует в этой объектной карте. Чужое доказательство не показано.';return model;}
    if(transition&&['candidate','literature_only'].includes(transition.formulation_status)){model.emptyReason='Для выбранной связи ещё не подготовлена Lean-постановка.';return model;}
    if(transition?.agent_task?.target&&finalTarget(run)&&transition.agent_task.target!==finalTarget(run)){model.emptyReason='Формальная цель не совпадает с выбранным переходом. Откройте его собственную проверку.';return model;}
    const plannedOnly=!list(run?.nodes).length,proofNodes=plannedOnly?list(run?.planned_nodes||run?.plan?.nodes).map(value=>({...value,target:value.target||value.id,planned:true})):list(run.nodes);
    const seen=new Set();for(const value of proofNodes){
      if(value.id==null||seen.has(String(value.id)))continue;seen.add(String(value.id));
      const planned=list(run.planned_nodes).find(n=>n.id===value.id||n.id===value.target),summary=summaryFor(run,'proof',value,renderer),status=value.planned?{status:'pending',label:'План · ещё не проверено'}:proofStatus(run,value,options.verdict||root.GuidedResearch?.verdict);
      const target=value.target||value.name||value.id,goal=target===finalTarget(run);
      model.nodes.push({id:'proof:'+value.id,kind:'proof',value,title:summary?.title||planned?.title||value.label||value.name||value.id,label:goal?brief(summary?.graphLabel||'Итоговая цель',32):brief(summary?.graphLabel||summary?.title||planned?.title||shortLabel(value.label||value.id),32),status:status.status,statusLabel:status.label,shape:'round-rectangle',goal});
    }
    const ids=new Set(model.nodes.map(n=>n.id));for(const [i,edge]of list(run?.edges).entries()){
      const source='proof:'+edge.source,target='proof:'+edge.target;if(ids.has(source)&&ids.has(target))model.edges.push({id:'proof-edge:'+i,source,target,type:edge.type||edge.kind||'dependency',value:{...edge}});
    }
    if(plannedOnly&&!model.edges.length)for(const value of proofNodes)for(const dependency of list(value.dependencies)){const source='proof:'+dependency,target='proof:'+value.id;if(ids.has(source)&&ids.has(target))model.edges.push({id:'plan-edge:'+model.edges.length,source,target,type:'planned_dependency',value:{source:dependency,target:value.id,type:'planned_dependency',evidence:'saved_plan'}});}
    const obligations=list(run?.formal_contract?.required_obligations);model.counts.obligations=obligations.length;
    model.counts.verified=obligations.filter(o=>model.nodes.some(n=>(n.value.target||n.value.id)===o.target&&['proved','refuted'].includes(n.status))).length;
    if(model.nodes.length){
      const roots=new Set([...obligations.map(o=>o.target),finalTarget(run)].filter(Boolean)),keep=ancestors(model.nodes,model.edges,roots);
      if(roots.size&&!keep.size){model.nodes=[];model.edges=[];model.emptyReason='Цели выбранной связи ещё не появились в этом графе доказательства.';}
    }
    if(!model.nodes.length&&!model.emptyReason)model.emptyReason='Граф лемм появится после подготовки постановки и плана доказательства.';
    return numberModel(model);
  }
  function cyElements(model){const metrics=labelMetrics();return [...model.nodes.map(n=>{const appearance=n.appearance||appearanceFor(n);return {data:{id:n.id,number:n.number,label:String(n.number),labelFont:metrics.size,labelWidth:metrics.width,kind:n.kind,status:n.status,shape:appearance.shape,color:appearance.fill,border:appearance.border,textColor:appearance.text}};}),...model.edges.map(e=>({data:{id:e.id,source:e.source,target:e.target,type:e.type}}))];}
  let instance=0;
  class Workspace{
    constructor({container,onVerify,onSearchAnalogies,onSelection,onOpenRun}={}){
      if(!container?.append)throw new Error('ResearchMap требует DOM-контейнер.');
      this.container=container;this.onVerify=onVerify;this.onSearchAnalogies=onSearchAnalogies;this.onSelection=onSelection;this.onOpenRun=onOpenRun;this.runs=[];this.run=null;this.view='objects';this.selection={objects:null,proof:null};this.numbers={objects:new Map(),proof:new Map()};this.focus=null;this.cy=null;this.layout=null;this.destroyed=false;this.key='';this.topology='';this.frame=null;
      this.uid='research-map-'+(++instance);this.root=this.el('section',{class:'research-map','aria-label':'Математическая карта'});container.append(this.root);this.makeUI();
      if(typeof root.ResizeObserver==='function'){this.observer=new root.ResizeObserver(()=>{if(this.destroyed)return;this.cy?.resize();this.overviewLabels();if(this.cy&&this.model?.nodes.length&&this.layoutDirection!==this.direction()){this.positionGraph();this.schedule(()=>this.initialFrame());}});this.observer.observe(this.canvas);}
      this.atlasReady=()=>{if(this.destroyed||!this.run)return;this.listKey='';this.inspectorKey='';this.selectionBarKey='';this.paint();};if(typeof root.addEventListener==='function')root.addEventListener('msc-atlas-ready',this.atlasReady);
    }
    el(tag,attrs={},text){const node=document.createElement(tag);for(const[k,v]of Object.entries(attrs))node.setAttribute(k,String(v));if(text!==undefined)node.textContent=str(text);return node;}
    prose(text,tag='p'){const node=this.el(tag);node.textContent=str(text);try{root.MathPresentation?.render?.(node,str(text));}catch{node.textContent=str(text);}return node;}
    button(label,action,attrs={}){const b=this.el('button',{type:'button',...attrs},label);b.onclick=action;return b;}
    detail(label,value){const node=this.el('details');node.append(this.el('summary',{},label),this.el('pre',{},typeof value==='string'?value:JSON.stringify(value,null,2)));return node;}
    makeUI(){
      const header=this.el('div',{class:'research-map-header'});header.append(this.el('h3',{},'Математическая карта'));
      const tabs=this.el('div',{class:'research-map-tabs',role:'tablist','aria-label':'Представление карты'});this.tabs={};
      for(const[view,label]of [['objects','Объекты и переходы'],['proof','Граф лемм']]){const b=this.button(label,()=>this.setView(view),{role:'tab','aria-controls':this.uid+'-panel'});this.tabs[view]=b;tabs.append(b);}header.append(tabs);this.root.append(header);
      const tools=this.el('div',{class:'research-map-tools'});
      tools.append(this.button('−',()=>this.zoom(1/1.25),{'aria-label':'Уменьшить карту'}),this.button('+',()=>this.zoom(1.25),{'aria-label':'Увеличить карту'}),this.button('Вместить',()=>this.fit()),this.button('К выбранному',()=>this.centerSelection()));this.root.append(tools);
      this.description=this.el('p',{class:'research-map-description'});this.root.append(this.description);
      this.selectionBar=this.el('div',{class:'research-map-selection','aria-label':'Выбранная карточка и действие'});this.root.append(this.selectionBar);
      this.body=this.el('div',{class:'research-map-body',id:this.uid+'-panel',role:'tabpanel'});const main=this.el('div',{class:'research-map-main'}),stage=this.el('div',{class:'research-map-stage'});
      this.canvas=this.el('div',{class:'research-map-canvas',tabindex:'0',role:'group','aria-label':'Интерактивная карта. Стрелки — перемещение, плюс и минус — масштаб, 0 — обзор. Узлы также доступны в списке ниже.'});
      this.empty=this.el('p',{class:'research-map-empty'});stage.append(this.canvas,this.empty);this.flowPanel=this.el('section',{class:'research-map-flow','aria-label':'Входы и выходы выбранного перехода'});this.flowPanel.hidden=true;main.append(this.flowPanel,stage);
      this.legend=this.el('div',{class:'research-map-legend','aria-label':'Цвета и обозначения карты'});main.append(this.legend);
      this.listDetails=this.el('details',{class:'research-map-node-list'});this.listDetails.open=true;this.listSummary=this.el('summary',{},'Узлы по номерам');this.listBox=this.el('div');this.listDetails.append(this.listSummary,this.listBox);
      this.inspector=this.el('aside',{class:'research-map-inspector','aria-label':'Выбранный узел'});this.body.append(main,this.listDetails,this.inspector);this.root.append(this.body);
      this.live=this.el('p',{class:'research-map-announcement','aria-live':'polite','aria-atomic':'true'});this.root.append(this.live);
      this.canvas.onkeydown=event=>{if(!this.cy)return;const k=event.key;if(['+','=','-','0','ArrowLeft','ArrowRight','ArrowUp','ArrowDown','Enter'].includes(k))event.preventDefault();if(k==='+'||k==='=')this.zoom(1.25);else if(k==='-')this.zoom(1/1.25);else if(k==='0')this.fit();else if(k==='Enter')this.centerSelection();else if(k.startsWith('Arrow')){const d=event.shiftKey?100:35;this.cy.panBy({x:k==='ArrowLeft'?d:k==='ArrowRight'?-d:0,y:k==='ArrowUp'?d:k==='ArrowDown'?-d:0});}};
    }
    render(run,{view,selection,runs,proofTransitionId}={}){
      if(this.destroyed)return this;const identity=JSON.stringify([run?.id||null,run?.object_graph?.id||null,run?.object_graph?.revision??null,run?.selected_transition_id||null]),changed=this.identity!==identity;this.identity=identity;this.run=run||null;
      if(runs!==undefined)this.runs=list(runs);
      this.proofFocus=proofTransitionId===run?.selected_transition_id?proofTransitionId:null;
      if(changed){this.view=defaultView(run);this.selection={objects:null,proof:null};this.numbers={objects:new Map(),proof:new Map()};this.focus=run?.selected_transition_id||list(run?.object_graph?.transitions)[0]?.id||null;this.key='';this.inspectorKey='';this.listKey='';this.inspectorSelection=null;}
      if(!this.focus)this.focus=run?.selected_transition_id||(this.view==='objects'?list(run?.object_graph?.transitions)[0]?.id:null)||null;
      if(['objects','proof'].includes(view))this.view=view;
      if(selection)this.applySelection(selection);this.paint(changed);return this;
    }
    setView(view){if(!['objects','proof'].includes(view))throw new Error('Неизвестное представление карты.');if(this.destroyed)return this;this.view=view;this.paint(true);return this;}
    applySelection(id){
      const raw=str(id),graph=this.run?.object_graph;
      if(raw.startsWith('transition:')||raw.startsWith('object:')){this.view='objects';this.selection.objects=raw;if(raw.startsWith('transition:'))this.focus=raw.slice(11);return;}
      if(raw.startsWith('proof:')){this.view='proof';this.selection.proof=raw;return;}
      if(this.view==='proof')this.selection.proof='proof:'+raw;
      else if(list(graph?.transitions).some(t=>String(t.id)===raw)){this.selection.objects='transition:'+raw;this.focus=raw;}
      else this.selection.objects='object:'+raw;
    }
    select(id){if(this.destroyed)return this;this.applySelection(id);this.paint();const selected=this.model?.nodes.find(n=>n.id===this.selection[this.view]);if(selected){this.live.textContent=selected.title+' · '+selected.statusLabel;this.onSelection?.({view:this.view,id:selected.id,kind:selected.kind,value:selected.value});}return this;}
    paint(reframe=false){
      if(this.destroyed)return;const proof=buildModel(this.run,{view:'proof',focusTransitionId:this.proofFocus||this.focus});this.proofAvailable=proof.nodes.length>0;this.tabs.proof.hidden=!this.proofAvailable;this.tabs.proof.disabled=!this.proofAvailable;if(this.view==='proof'&&!this.proofAvailable)this.view='objects';this.model=numberModel(this.view==='proof'?proof:buildModel(this.run,{view:'objects',focusTransitionId:this.focus}),this.numbers[this.view]);const model=this.model;for(const node of model.nodes){node.mscContext=this.mscContext(node);node.appearance=appearanceFor(node);}
      if(model.nodes.length&&!model.nodes.some(n=>n.id===this.selection[this.view]))this.selection[this.view]=(this.view==='objects'?model.nodes.find(n=>n.id==='transition:'+this.focus):model.nodes.find(n=>n.goal))?.id||model.nodes[0]?.id||null;
      this.context=transitionContext(model,this.selection[this.view]);
      for(const[key,b]of Object.entries(this.tabs)){b.setAttribute('aria-selected',String(key===this.view));b.tabIndex=key===this.view?0:-1;b.onkeydown=e=>{if(['ArrowLeft','ArrowRight'].includes(e.key)&&this.proofAvailable){e.preventDefault();const next=this.view==='objects'?'proof':'objects';this.setView(next);this.tabs[next].focus();}};}
      this.description.textContent=this.view==='objects'?'Номера расшифрованы в списке под картой. Выберите номер, чтобы открыть описание и действие. Стрелки связывают объекты и переходы.':(model.counts.obligations?'Проверено обязательств: '+model.counts.verified+' из '+model.counts.obligations+'. ':'')+'Номера лемм — в списке под картой. Пунктир — зависимость типа или план; план ещё не является доказательством.';
      this.empty.hidden=!!model.nodes.length;this.empty.textContent=model.emptyReason;this.canvas.setAttribute('aria-label',(this.view==='objects'?'Карта объектов и переходов':'Граф лемм')+'. Стрелки — перемещение, плюс и минус — масштаб, 0 — обзор. Список узлов ниже.');
      const key=JSON.stringify({view:this.view,nodes:model.nodes.map(n=>[n.id,n.number,n.status,n.appearance.fill,n.appearance.border,n.appearance.text,n.appearance.shape]),edges:model.edges.map(e=>[e.id,e.source,e.target,e.type])});
      if(key!==this.key){this.draw(model,reframe);this.key=key;}
      this.paintLegend();this.paintList();this.paintSelectionBar();this.paintFlow();this.paintInspector();this.highlight();
      if(reframe)this.schedule(()=>this.initialFrame());
    }
    draw(model,reframe){
      if(typeof root.cytoscape!=='function'){if(model.nodes.length){this.empty.hidden=false;this.empty.textContent='Графическая библиотека недоступна. Используйте список узлов ниже.';this.listDetails.open=true;}return;}
      const topology=JSON.stringify([this.view,model.nodes.map(n=>n.id).sort(),model.edges.map(e=>[e.id,e.source,e.target]).sort((a,b)=>a[0].localeCompare(b[0]))]),changed=topology!==this.topology;
      const positions=new Map(this.cy?.nodes().map(n=>[n.id(),{...n.position()}])||[]);
      if(!this.cy){this.cy=root.cytoscape({container:this.canvas,elements:[],layout:{name:'preset'},minZoom:.15,maxZoom:3.5,boxSelectionEnabled:false,selectionType:'single',style:[
        {selector:'node',style:{shape:'data(shape)',width:60,height:60,'background-color':'data(color)','border-color':'data(border)','border-width':2,label:'data(label)','font-family':'system-ui, sans-serif','font-size':'data(labelFont)','font-weight':600,color:'data(textColor)','text-valign':'center','text-wrap':'none','text-max-width':'data(labelWidth)','min-zoomed-font-size':0,'overlay-opacity':0}},
        {selector:'node.map-input',style:{'border-width':4,'border-color':'#334155','border-style':'dashed'}},
        {selector:'node.map-output',style:{'border-width':4,'border-color':'#334155','border-style':'solid'}},
        {selector:'node.map-both',style:{'border-width':5,'border-color':'#334155','border-style':'double'}},
        {selector:'node.map-selected',style:{'border-width':5,'border-color':'#111827','border-style':'solid','font-weight':600}},
        {selector:'edge',style:{width:1.5,'line-color':'#8997aa','target-arrow-color':'#8997aa','target-arrow-shape':'triangle','curve-style':'bezier','arrow-scale':.9,'overlay-opacity':0,opacity:.65}},
        {selector:'edge[type="type_dependency"]',style:{'line-style':'dashed','line-color':'#a9b4c3','target-arrow-color':'#a9b4c3'}},
        {selector:'edge[type="planned_dependency"],edge[type="candidate"],edge[type="analogy"]',style:{'line-style':'dotted','line-color':'#9c8fba','target-arrow-color':'#9c8fba'}},
        {selector:'edge.map-adjacent',style:{width:3,'line-color':'#5d7290','target-arrow-color':'#5d7290'}},
        {selector:'edge.map-input-edge',style:{width:3,'line-color':'#334155','target-arrow-color':'#334155','line-style':'dashed',opacity:1}},
        {selector:'edge.map-output-edge',style:{width:3,'line-color':'#334155','target-arrow-color':'#334155','line-style':'solid',opacity:1}}
      ]});this.cy.on('tap','node',event=>this.select(event.target.id()));this.cy.on('zoom',()=>this.overviewLabels());this.cy.on('tap','edge',event=>{const edge=this.model.edges.find(e=>e.id===event.target.id());if(edge)this.inspectEdge(edge);});}
      this.cy.batch(()=>{this.cy.elements().remove();this.cy.add(cyElements(model));if(!changed)for(const node of this.cy.nodes()){const p=positions.get(node.id());if(p)node.position({...p});}});this.overviewLabels();
      if(changed&&model.nodes.length){this.positionGraph();this.schedule(()=>this.initialFrame());}
      else if(reframe)this.schedule(()=>this.initialFrame());this.topology=topology;
    }
    schedule(fn){if(this.frame!==null&&root.cancelAnimationFrame)root.cancelAnimationFrame(this.frame);if(root.requestAnimationFrame)this.frame=root.requestAnimationFrame(()=>{this.frame=null;if(!this.destroyed)fn();});else if(!this.destroyed)fn();}
    direction(){return this.canvas.clientWidth>650?'LR':'TB';}
    positionGraph(){this.layout?.stop();this.layoutDirection=this.direction();if(this.canvas.style)this.canvas.style.height='';try{this.layout=this.cy.layout({name:'dagre',rankDir:this.layoutDirection,nodeSep:24,rankSep:64,edgeSep:14,nodeDimensionsIncludeLabels:false,padding:28,animate:false,fit:false});this.layout.run();}catch{this.layout=this.cy.layout({name:'breadthfirst',directed:true,padding:28,spacingFactor:1.1,animate:false,fit:false});this.layout.run();}}
    initialFrame(){if(!this.cy?.nodes().length)return;this.cy.resize();this.cy.fit(this.cy.elements(),32);this.overviewLabels();}
    fit(){if(this.cy?.nodes().length){this.initialFrame();this.live.textContent='Показаны все узлы карты. Выберите узел, чтобы открыть описание.';}return this;}
    overviewLabels(){if(!this.cy)return;const metrics=labelMetrics(this.cy.zoom());this.cy.nodes().data('labelFont',metrics.size);this.cy.nodes().data('labelWidth',metrics.width);}
    zoom(factor){if(!this.cy)return;const extent=this.cy.extent();this.cy.zoom({level:Math.max(.15,Math.min(3.5,this.cy.zoom()*factor)),position:{x:(extent.x1+extent.x2)/2,y:(extent.y1+extent.y2)/2}});}
    centerSelection(){if(!this.cy)return;const item=this.cy.getElementById(this.selection[this.view]||'');if(item.length){this.cy.zoom(Math.max(.95,this.cy.zoom()));this.cy.center(item);}}
    highlight(){
      if(!this.cy)return;this.cy.elements().removeClass('map-selected map-adjacent map-input map-output map-both map-input-edge map-output-edge');const node=this.cy.getElementById(this.selection[this.view]||'');if(node.length)node.addClass('map-selected');
      if(!this.context){if(node.length)node.connectedEdges().addClass('map-adjacent');return;}
      for(const item of this.model.nodes){const role=endpointRole(this.context,item.id);if(role)this.cy.getElementById(item.id).addClass('map-'+role);}
      const transitionId=this.context.transition.id,inputs=new Set(this.context.inputs.filter(item=>!item.missing).map(item=>item.id)),outputs=new Set(this.context.outputs.filter(item=>!item.missing).map(item=>item.id));
      for(const edge of this.model.edges){if(inputs.has(edge.source)&&edge.target===transitionId)this.cy.getElementById(edge.id).addClass('map-input-edge');if(edge.source===transitionId&&outputs.has(edge.target))this.cy.getElementById(edge.id).addClass('map-output-edge');}
    }
    paintLegend(){
      const labels={object:'Объект',defined:'Определение',pending:'Не проверено',hypothesis:'Связь без проверки Lean',proved:'Проверено',refuted:'Контрпример',formal_only:'Lean проверен, смысл не подтверждён',checking:'Проверяется',incomplete:'Проверка не завершена',needs_recheck:'Нужна новая проверка'},entries=new Map(),roles=this.context?[...new Set(this.model.nodes.map(node=>endpointRole(this.context,node.id)).filter(Boolean))]:[];
      for(const node of this.model.nodes){const appearance=node.appearance;if(this.view==='proof'){entries.set(node.status,{label:labels[node.status]||node.statusLabel,color:appearance.fill,border:appearance.border});}else{const family=appearance.classification==='family'?appearance.families[0]:null;entries.set(family?.id||appearance.classification,{label:family?.shortLabel||appearance.label,color:family?.color||'#64748b',border:family?.color||'#64748b'});}}
      const key=JSON.stringify([this.view,[...entries],roles]);if(key===this.legendKey)return;this.legendKey=key;this.legend.replaceChildren();
      if(this.view==='objects'){this.legend.append(this.el('span',{class:'research-map-legend-note'},'Цвет — область MSC; статус проверки — в подписи.'));for(const[kind,label]of [['object','Объект'],['transition','Переход']]){const item=this.el('span',{class:'research-map-legend-item'});item.append(this.el('span',{class:'research-map-legend-swatch research-map-kind-'+kind,'aria-hidden':'true'}),this.el('span',{},label));this.legend.append(item);}}
      for(const entry of entries.values()){const item=this.el('span',{class:'research-map-legend-item'});item.append(this.el('span',{class:'research-map-legend-swatch','aria-hidden':'true',style:'background:'+entry.color+';border-color:'+entry.border}),this.el('span',{},entry.label));this.legend.append(item);}
      const selected=this.el('span',{class:'research-map-legend-item'});selected.append(this.el('span',{class:'research-map-legend-swatch research-map-legend-selected','aria-hidden':'true'}),this.el('span',{},'Выбранный узел'));this.legend.append(selected);
      for(const role of roles){const item=this.el('span',{class:'research-map-legend-item'});item.append(this.el('span',{class:'research-map-legend-swatch research-map-role-'+role,'aria-hidden':'true'}),this.el('span',{},endpointLabel(role)+' · рамка'));this.legend.append(item);}
    }
    numberBadge(node){const appearance=node.appearance||appearanceFor(node);return this.el('span',{class:'research-map-node-number','data-node-id':node.id,'data-number':node.number,'data-kind':node.kind,style:'--node-bg:'+appearance.fill+';--node-border:'+appearance.border+';--node-text:'+appearance.text},node.number);}
    mscContext(node){try{const context=root.MSCContext?.forNode?.(this.run,node,code=>root.MSCAtlas?.lookup?.(code));if(context)return context;}catch{}return {origin:'none',label:'Контекст MSC2020 ещё не загружен',items:[]};}
    mscChip(item,withTitle=true){const colors=appearanceAPI()?.forMSC(item),style=colors?'--msc-chip-bg:'+colors.fill+';--msc-chip-border:'+colors.border+';--msc-chip-text:'+colors.text:'';return this.el('span',{class:'research-map-msc-chip','data-family':colors?.family?.id||'context',style},item.code+(withTitle?' — '+item.title:''));}
    mscCaption(context,compactOnMobile=false,appearance=null){
      const caption=this.el('span',{class:'research-map-msc-caption','data-msc-origin':context.origin});if(appearance?.classification==='mixed')caption.append(this.el('span',{class:'research-map-family-label'},'Несколько областей'));caption.append(this.el('span',{class:'research-map-msc-origin'},'MSC2020 · '+context.label));
      if(list(context.items).length){const full=this.el('span',{class:'research-map-msc-full'});for(const[i,item]of context.items.entries()){if(i)full.append(this.el('span',{},'; '));full.append(this.mscChip(item));}caption.append(full);if(compactOnMobile){const codes=this.el('span',{class:'research-map-msc-codes'});for(const[i,item]of context.items.entries()){if(i)codes.append(this.el('span',{},' · '));codes.append(this.mscChip(item,false));}caption.append(codes);}}return caption;
    }
    mscPanel(context,appearance=null){
      const panel=this.el('section',{class:'research-map-msc-panel','aria-label':'MSC2020','data-msc-origin':context.origin});panel.append(this.el('h5',{},'MSC2020'));if(appearance?.classification==='mixed')panel.append(this.el('p',{class:'research-map-family-label'},'Несколько областей'));panel.append(this.el('p',{class:'research-map-msc-origin'},context.label));
      for(const item of list(context.items)){
        const row=this.el('div',{class:'research-map-msc-item'}),label=this.el('p');label.append(this.mscChip(item));row.append(label);
        if(item.known===true){const open=this.button('Открыть MSC '+item.code+' на карте',()=>root.MSCAtlas?.open?.(item.code),{class:'research-map-msc-open'});open.disabled=typeof root.MSCAtlas?.open!=='function';row.append(open);}
        panel.append(row);
      }
      const originals=list(context.items).filter(item=>item.officialTitle||list(item.path).length);if(originals.length){const details=this.el('details');details.append(this.el('summary',{},'Официальные названия и иерархия'));for(const item of originals){details.append(this.el('p',{},item.code+' — '+(item.officialTitle||item.title)));if(list(item.path).length)details.append(this.el('p',{class:'research-map-msc-path'},item.path.map(part=>part.code+' — '+part.title).join(' → ')));}panel.append(details);}
      return panel;
    }
    paintList(){const key=JSON.stringify([this.identity,this.view,this.selection[this.view],this.model.nodes.map(n=>[n.id,n.number,n.title,n.statusLabel,n.kind,n.mscContext,n.appearance,endpointRole(this.context,n.id)])]);if(key===this.listKey)return;this.listKey=key;const focused=descendants(this.listBox).includes(document.activeElement)?document.activeElement?.getAttribute?.('data-node-id'):null;this.listSummary.textContent='Узлы по номерам · '+this.model.nodes.length;this.listBox.replaceChildren();
      const groups=this.view==='objects'?[['Объекты',this.model.nodes.filter(n=>n.kind==='object')],['Переходы',this.model.nodes.filter(n=>n.kind==='transition')]]:[['Леммы и определения',this.model.nodes]];let restoreFocus=null;
      for(const[title,nodes]of groups){if(!nodes.length)continue;const group=this.el('section',{class:'research-map-list-group'}),cards=this.el('div',{class:'research-map-card-grid'});group.append(this.el('h4',{},title+' · '+nodes.length),cards);
        for(const node of [...nodes].sort((a,b)=>a.number-b.number)){const role=endpointRole(this.context,node.id),button=this.button('',()=>this.select(node.id),{class:'research-map-node-card','aria-pressed':String(node.id===this.selection[this.view]),'data-node-id':node.id,'data-number':node.number,'data-kind':node.kind,'data-status':node.status,'data-endpoint-role':role,style:'--node-selected:'+node.appearance.tint}),text=this.el('span',{class:'research-map-node-text'});text.append(this.el('span',{class:'research-map-card-kind'},kindLabel(node)),this.el('strong',{},node.title));if(role)text.append(this.el('span',{class:'research-map-endpoint-label','data-endpoint-role':role},endpointLabel(role)));text.append(this.el('span',{class:node.kind==='object'?'research-map-card-status':'research-map-card-status research-map-badge','data-status':node.status},node.statusLabel),this.mscCaption(node.mscContext,false,node.appearance));button.append(this.numberBadge(node),text);cards.append(button);if(focused===node.id)restoreFocus=button;}this.listBox.append(group);
      }restoreFocus?.focus({preventScroll:true});
    }
    badge(node){return this.el('span',{class:'research-map-badge','data-status':node.status},node.statusLabel);}
    verifyTransition(id){const graph=this.run?.object_graph,value=list(graph?.transitions).find(item=>item.id===id);if(value&&this.context?.transition.value.id===id&&this.context.endpointsComplete&&!active.has(this.run?.status))this.onVerify?.(graph,value);}
    searchAnalogies(id){const graph=this.run?.object_graph,value=list(graph?.transitions).find(item=>item.id===id);if(value&&transitionRole(this.run,value)==='article'&&this.context?.transition.value.id===id&&this.context.endpointsComplete&&!active.has(this.run?.status))this.onSearchAnalogies?.(graph,value);}
    paintSelectionBar(){
      const node=this.model.nodes.find(n=>n.id===this.selection[this.view]),attempt=node?.kind==='transition'?priorAttempt(this.run,node.value,this.runs):null,role=node?.kind==='transition'?transitionRole(this.run,node.value):null,key=JSON.stringify([this.identity,this.view,node?.id,node?.number,node?.title,node?.status,node?.statusLabel,node?.mscContext,node?.appearance,this.context?.endpointsComplete,attempt,role,this.run?.status]);if(key===this.selectionBarKey)return;this.selectionBarKey=key;const focused=descendants(this.selectionBar).includes(document.activeElement)?{tag:document.activeElement.tagName,text:document.activeElement.textContent}:null;this.selectionBar.replaceChildren();
      if(!node){this.selectionBar.append(this.el('span',{},'Выберите карточку на карте или в списке.'));return;}
      const description=this.el('div',{class:'research-map-selection-text'});description.append(this.el('strong',{},node.title),this.badge(node),this.mscCaption(node.mscContext,true,node.appearance));this.selectionBar.append(this.numberBadge(node),description);
      if(node.kind==='transition'){
        if(role==='article'){const search=this.button('Найти аналоги в других областях',()=>this.searchAnalogies(node.value.id),{class:'research-map-verify'});search.disabled=!this.onSearchAnalogies||active.has(this.run?.status)||!this.context?.endpointsComplete;this.selectionBar.append(search);}
        else if(attempt){const open=this.button(attempt.label,()=>this.onOpenRun?.(attempt.runId),{class:'research-map-verify'});open.disabled=!this.onOpenRun;this.selectionBar.append(open);}
        else if(this.onVerify){const verify=this.button(role==='bridge'?'Проверить общую структуру в Lean':'Исследовать переход',()=>this.verifyTransition(node.value.id),{class:'research-map-verify'});verify.disabled=active.has(this.run?.status)||!this.context?.endpointsComplete;this.selectionBar.append(verify);}
      }
      if(focused)descendants(this.selectionBar).find(element=>element.tagName===focused.tag&&element.textContent===focused.text)?.focus?.({preventScroll:true});
    }
    paintFlow(){
      const context=this.context,attempt=context?priorAttempt(this.run,context.transition.value,this.runs):null,role=context?transitionRole(this.run,context.transition.value):null,key=JSON.stringify([this.identity,context,attempt,role]);if(key===this.flowKey)return;this.flowKey=key;
      const preserve=this.flowSelection===context?.transition.id,previous=descendants(this.flowPanel),opened=preserve&&previous.some(node=>node.tagName==='DETAILS'&&node.open),focused=preserve&&previous.includes(document.activeElement)?{tag:document.activeElement.tagName,text:document.activeElement.textContent}:null;this.flowSelection=context?.transition.id||null;
      this.flowPanel.replaceChildren();this.flowPanel.hidden=!context;if(!context)return;const transition=context.transition,value=transition.value;
      this.flowPanel.append(this.el('h4',{},'Объекты перехода №'+transition.number));const flow=this.el('div',{class:'research-map-flow-diagram'});
      const group=(title,endpoints,role)=>{const section=this.el('section',{class:'research-map-flow-group research-map-role-'+role});section.append(this.el('h5',{},title));const ul=this.el('ul');for(const endpoint of endpoints){const li=this.el('li',{'data-endpoint-id':endpoint.objectId,'data-endpoint-role':endpointRole(context,endpoint.id)||role});li.append(this.el('span',{},endpoint.missing?endpoint.title:'№'+endpoint.number+' — '+endpoint.title));if(!endpoint.missing&&endpointRole(context,endpoint.id)==='both')li.append(this.el('span',{class:'research-map-endpoint-label'},'Вход и выход перехода'));ul.append(li);}if(!endpoints.length)section.append(this.el('p',{},'Не указаны в сохранённой карте.'));else section.append(ul);return section;};
      const central=this.el('div',{class:'research-map-flow-transition'});central.append(this.el('strong',{},'Переход №'+transition.number));flow.append(group('Входные объекты',context.inputs,'input'),this.el('span',{class:'research-map-flow-arrow','aria-hidden':'true'},'→'),central,this.el('span',{class:'research-map-flow-arrow','aria-hidden':'true'},'→'),group('Выходные объекты',context.outputs,'output'));this.flowPanel.append(flow);
      this.flowPanel.append(this.el('p',{class:'research-map-flow-purpose'},role==='article'?'Исходный переход №'+transition.number+' и его условия станут отправной точкой поиска аналогов в трёх областях MSC.':'Проверяется утверждение перехода №'+transition.number+' при его условиях — целиком для указанного состава объектов.'));
      if(!context.endpointsComplete)this.flowPanel.append(this.el('p',{class:'research-map-flow-warning'},'Состав входов и выходов неполон: '+(context.missing.length?'в карте не найдены объекты '+context.missing.map(id=>'«'+(id||'пустой идентификатор')+'»').join(', ')+'.':'входные или выходные объекты не указаны.')+' Новое исследование недоступно до восстановления этих объектов.'));
      const unformalized=!value.agent_task||['candidate','literature_only'].includes(value.formulation_status);
      this.flowPanel.append(this.el('p',{class:'research-map-flow-action'},role==='article'?'Astra предложит структурный паттерн, исследует три направления MSC и сохранит кандидатов с источниками. Затем вы выберете общую структуру для отдельной Lean-проверки.':attempt?'Кнопка «'+attempt.label+'» открывает сохранённый запуск для этого перехода.':unformalized?'Astra попробует подготовить точную постановку выбранной связки; Lean проверит предложенное доказательство. Смысловое соответствие исходному утверждению оценивается отдельно.':'Кнопка запускает проверку точной Lean-цели этого перехода со всеми его обязательствами.'));
      const details=this.el('details');details.open=!!opened;details.append(this.el('summary',{},role==='article'?'Исходное утверждение и условия':unformalized?'Что предлагается формализовать и проверить':'Что проверяем'),this.prose(value.claim||'Исходное утверждение не сохранено.'));if(list(value.assumptions).length){details.append(this.el('h5',{},'Условия исходной постановки'));const conditions=this.el('ul');for(const condition of value.assumptions)conditions.append(this.prose(condition,'li'));details.append(conditions);}this.flowPanel.append(details);
      if(focused)descendants(this.flowPanel).find(node=>node.tagName===focused.tag&&node.textContent===focused.text)?.focus?.({preventScroll:true});
    }
    paintInspector(){
      const node=this.model.nodes.find(n=>n.id===this.selection[this.view]),summary=node?summaryFor(this.run,node.kind,node.value):null,attempt=node?.kind==='transition'?priorAttempt(this.run,node.value,this.runs):null,role=node?.kind==='transition'?transitionRole(this.run,node.value):null,selection=this.view+':'+(node?.id||''),key=JSON.stringify([this.identity,selection,node?.number,this.run?.status,node?.status,node?.title,node?.value,node?.mscContext,node?.appearance,summary,attempt,role,node?.goal?this.run?.result:null,node?.kind==='transition'?this.run?.object_graph?.sources:null,this.model.emptyReason]);if(key===this.inspectorKey)return;this.inspectorKey=key;
      const previous=descendants(this.inspector),preserve=this.inspectorSelection===selection,opened=preserve?new Set(previous.filter(n=>n.tagName==='DETAILS'&&n.open).map(n=>n.children[0]?.textContent)):new Set(),focused=preserve&&previous.includes(document.activeElement)?{tag:document.activeElement.tagName,text:document.activeElement.textContent}:null;this.inspectorSelection=selection;
      this.inspector.replaceChildren();if(!node){this.inspector.append(this.el('h4',{},'Выберите карточку'),this.el('p',{},this.model.emptyReason||'Нажмите карточку на карте или в списке.'));return;}
      const value=node.value;this.inspector.append(this.numberBadge(node),this.el('p',{class:'research-map-kind'},kindLabel(node)),this.el('h4',{},summary?.title||node.title),this.badge(node),this.mscPanel(node.mscContext,node.appearance));
      if(role==='article'){const direct=this.el('details');direct.append(this.el('summary',{},'Прямая проверка утверждения статьи'),this.el('p',{},'Это отдельная попытка формализовать исходное утверждение статьи. Поиск аналогов запускается основной кнопкой над картой.'));if(attempt){const open=this.button(attempt.label,()=>this.onOpenRun?.(attempt.runId));open.disabled=!this.onOpenRun;direct.append(open);}const verify=this.button('Проверить утверждение статьи',()=>this.verifyTransition(value.id));verify.disabled=!this.onVerify||active.has(this.run?.status)||!this.context?.endpointsComplete;direct.append(verify);this.inspector.append(direct);}
      else if(node.kind==='transition'&&attempt&&this.onVerify){const repeat=this.el('details');repeat.append(this.el('summary',{},'Повторное исследование'));const verify=this.button('Исследовать заново',()=>this.verifyTransition(value.id));verify.disabled=active.has(this.run?.status)||!this.context?.endpointsComplete;repeat.append(verify);this.inspector.append(repeat);}
      if(summary?.description)this.inspector.append(this.prose(summary.description));
      else this.inspector.append(this.el('p',{},node.kind==='object'?'Определение и параметры этого объекта сохранены в исходной постановке.':node.kind==='transition'?'Связь между входными и выходными объектами. Её условия и точный контракт доступны ниже.':'Этот узел входит в сохранённый граф зависимостей. Точный тип и отчёт Lean доступны ниже.'));
      const formulas=list(summary?.formulas),featured=formulas.some(f=>f.featured===true),construction=this.el('details');construction.append(this.el('summary',{},'Обозначения и построение'));let extra=0;
      for(const formula of formulas){if(!formula?.tex)continue;const card=this.el('div',{class:'research-map-formula'});if(formula.label)card.append(this.el('p',{},formula.label));const math=this.el('div');math.textContent=formula.tex;try{root.MathPresentation?.formula?.(math,formula.tex,{display:true});}catch{math.textContent=formula.tex;}card.append(math);if(featured&&formula.featured!==true){construction.append(card);extra++;}else this.inspector.append(card);}if(extra)this.inspector.append(construction);
      const conditions=list(summary?.assumptions).length?summary.assumptions:list(value.assumptions);if(conditions.length){this.inspector.append(this.el('h5',{},'Условия'));const ul=this.el('ul');for(const item of conditions.slice(0,3))ul.append(this.prose(brief(item,210),'li'));this.inspector.append(ul);if(conditions.length>3)this.inspector.append(this.detail('Все условия',conditions));}
      if(list(summary?.limitations).length){const d=this.el('details');d.append(this.el('summary',{},'Границы результата'));for(const item of summary.limitations)d.append(this.prose(item));this.inspector.append(d);}
      if(node.kind==='transition'){this.inspector.append(this.detail('Исходная формулировка и обязательства',{claim:value.claim,construction:value.construction,assumptions:value.assumptions,agent_task:value.agent_task,obligations:value.obligations}));if(value.semantic_review)this.inspector.append(this.detail('Смысловая рецензия',value.semantic_review));if(value.certificate)this.inspector.append(this.detail('Сертификат Lean',value.certificate));const sources=root.ObjectGraphModel?.relatedSources?.(this.run.object_graph,value)||[];if(sources.length)this.inspector.append(this.detail('Источники',sources));}
      else if(node.kind==='object')this.inspector.append(this.detail('Определение, параметры и ссылки',value));
      else{this.inspector.append(this.detail('Точный узел Lean',value));const report=value.verification||value.result?.verification||value.report?.verification;if(report)this.inspector.append(this.detail('Сохранённый отчёт Lean',report));if(node.goal&&this.run.result)this.inspector.append(this.detail('Итоговая проверка',this.run.result));}
      for(const element of descendants(this.inspector)){if(element.tagName==='DETAILS'&&opened.has(element.children[0]?.textContent))element.open=true;if(focused&&element.tagName===focused.tag&&element.textContent===focused.text)element.focus?.({preventScroll:true});}
    }
    inspectEdge(edge){this.inspectorKey='';this.inspector.replaceChildren(this.el('h4',{},edgeNames[edge.type]||'Сохранённая связь'),this.el('p',{},'Стрелка взята из графа. Она не является самостоятельным сертификатом доказательства.'),this.detail('Исходные сведения о ребре',edge.value));}
    destroy(){if(this.destroyed)return;this.destroyed=true;this.layout?.stop();this.observer?.disconnect();if(typeof root.removeEventListener==='function')root.removeEventListener('msc-atlas-ready',this.atlasReady);if(this.frame!==null&&root.cancelAnimationFrame)root.cancelAnimationFrame(this.frame);this.cy?.destroy();this.cy=null;this.canvas.onkeydown=null;this.root.remove();}
  }
  return {Workspace,buildModel,proofStatus,compiledTheoremEvidence,defaultView,cyElements,summaryFor,canvasLabel,labelMetrics,priorAttempt,kindLabel,shortStatus,numberModel,transitionContext,endpointRole,appearanceFor,sourceTransition,transitionRole};
});
