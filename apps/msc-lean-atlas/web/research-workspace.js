'use strict';

(function(root,factory){const api=factory(root);if(typeof module==='object'&&module.exports)module.exports=api;else root.ResearchWorkspaceView=api;})(typeof globalThis!=='undefined'?globalThis:this,root=>{
  const list=value=>Array.isArray(value)?value:[];
  const text=value=>typeof value==='string'?value.trim():'';
  const active=run=>['queued','running','cancelling'].includes(run?.status);
  const search=run=>['structure','discover'].includes(run?.purpose);
  const guided=()=>root.GuidedResearch||(typeof require==='function'?require('./guided-research.js'):null);
  const nonnegative=value=>Number.isFinite(Number(value))?Math.max(0,Number(value)):0;
  const stateNames={complete:'Готово',partial:'Частично',active:'Выполняется',stopped:'Остановлено',pending:'Не начато',review:'Нужно уточнение'};
  function sourceIdentity(run){
    const card=run?.source_card||run?.contract?.source_card,library=run?.contract?.source_library||run?.source_snapshot;
    const paper=list(run?.paper_manifest||run?.contract?.paper_manifest)[0];
    return {title:text(run?.source_title)||text(paper?.title)||text(library?.title)||text(library?.name)||text(card?.title)||'Исходный материал',
      detail:text(card?.selected_statement)||text(card?.statement)||text(library?.selected_declaration?.name)||text(run?.target)||text(paper?.versioned_id),
      key:text(card?.source_id)||text(library?.source_sha256)||text(paper?.versioned_id)||text(run?.source_graph_ref?.id)||text(run?.id)};
  }
  function lineage(run){
    const value=run?.source_lineage||run?.lineage||run?.revision_info||{};
    const parent=text(value.parent_run_id)||text(run?.parent_run_id)||text(run?.forked_from_run_id)||text(run?.parent_run);
    return {parent,root:text(value.root_run_id)||text(run?.root_run_id)||parent||text(run?.id),
      version:Number.isInteger(value.version)?value.version:Number.isInteger(run?.version)?run.version:Number.isInteger(run?.revision)?run.revision:null,
      reason:text(value.reason)||text(run?.revision_reason),changes:list(value.changes||run?.contract_changes)};
  }
  function elapsedSeconds(run){
    const live=run?.live_elapsed_seconds;
    return typeof live==='number'&&Number.isFinite(live)&&live>=0?live:nonnegative(run?.usage?.elapsed_seconds);
  }
  function elapsedLabel(seconds){const whole=Math.floor(nonnegative(seconds));return whole<60?whole+' с':Math.floor(whole/60)+' мин '+whole%60+' с';}
  function draftPrepared(run){
    if(run?.formal_contract||run?.object_contract||run?.formalization_review?.agent_task)return true;
    const repair=run?.draft_repair,report=run?.contract_verification;
    if(['checking','typed','stopped'].includes(repair?.status)&&Number.isInteger(repair.version)&&repair.version>=0)return true;
    return report?.kind==='lean_contract_preflight'&&report.proof_checked===false&&!!text(report.target)&&
      (list(report.checked_obligations).length>0||list(report.diagnostics).length>0);
  }
  function resourceUsage(run){
    const usage=run?.usage||{},budget=run?.budget||{};
    return {calls:nonnegative(usage.calls),callLimit:nonnegative(budget.max_calls),seconds:elapsedSeconds(run),
      timeLimit:nonnegative(budget.timeout_seconds),tokens:nonnegative(usage.total_tokens),
      backend:({'native':'AMR · Astra + Lean','goedel-adapted':'Goedel · адаптированный процесс'})[run?.proof_backend]||text(run?.proof_backend?.name)||text(run?.contract?.proof_backend?.name)||text(run?.proof_backend)||'AMR · Astra + Lean'};
  }
  function stageFor(phase){
    if(/final_semantic|final_review|publish|certif/.test(phase))return 5;
    if(/compose|composition|audit|verify/.test(phase))return 4;
    if(/plan|prove|critic|revise|investigate/.test(phase))return 3;
    if(/validate_contract|contract_review/.test(phase))return 2;
    if(/preflight|elaborat|repair_contract|library_context/.test(phase))return 1;
    return 0;
  }
  function stages(run){
    if(!run)return [];
    if(run.status==='draft')return (search(run)?['Разбор источника','Поиск направлений','Карта кандидатов']:['Постановка','Типы Lean','Проверка смысла','Доказательство','Сборка Lean','Итоговая рецензия']).map((title,i)=>({id:(search(run)?'search-':'proof-')+i,title,state:'pending',step:'source'}));
    if(search(run)){
      const phase=text(run.termination?.stage||run.active_stage||run.phase),index=/merge|publish/.test(phase)?2:/search|route|direction|candidate|rank/.test(phase)?1:0;
      const done=['complete','completed'].includes(run.status);
      if(guided()?.partialSearchInfo(run)){
        const routes=list(run.structure_routes),profile=!!run.structure_profile,allRoutes=routes.length>0&&routes.every(route=>route.status==='complete'),mapped=!!run.object_graph?.id&&list(run.object_graph.transitions).length>0;
        return [{id:'search-0',title:'Разбор источника',state:profile?'complete':'stopped',step:'connections'},
          {id:'search-1',title:'Поиск направлений',state:allRoutes?'complete':profile?'stopped':'pending',step:'connections'},
          {id:'search-2',title:'Карта кандидатов',state:mapped?'partial':index===2?'stopped':'pending',step:'connections'}];
      }
      return ['Разбор источника','Поиск направлений','Карта кандидатов'].map((title,i)=>({id:'search-'+i,title,state:done?'complete':i<index?'complete':i===index?(active(run)?'active':'stopped'):'pending',step:'connections'}));
    }
    const stop=run.termination||run.result?.termination,phase=text(run.outcome_summary?.stage||stop?.stage||(run.phase==='library_context'?run.phase:run.active_stage||run.phase));
    const preparingLibrary=phase==='library_context';
    const preflight=guided()?.contractPreflight(run),proof=guided()?.formalEvidence(run),review=run.contract_review;
    const final=guided()?.finalReview(run),formalized=draftPrepared(run),progress=guided()?.proofProgress(run);
    const proofNodes=list(run.nodes).filter(node=>!['def','definition','opaque','inductive','structure','constructor','recursor'].includes(node.kind));
    // The accepted preflight during library preparation checks the baseline
    // draft. Expanded imports still need their own check before freezing.
    const evidence=[formalized,!preparingLibrary&&preflight?.accepted===true,['aligned','reviewed_fixture'].includes(review?.status),
      proof===true||proofNodes.length>0&&proofNodes.every(node=>['proved','verified','complete'].includes(node.status)),proof===true,
      proof===true&&['aligned','reviewed_fixture'].includes(final?.status)];
    let index=stageFor(phase);
    if(phase==='semantic_review')index=proof?5:2;
    if(!active(run)&&!stop){const missing=evidence.findIndex(value=>!value);index=missing<0?5:missing;}
    const stoppedProof=!active(run)&&progress?.started&&!evidence[3];
    if(stoppedProof&&index>=3&&index<5)index=3;
    return ['Постановка',preparingLibrary?'Подбор библиотечных лемм и импортов':'Типы Lean','Проверка смысла','Доказательство','Сборка Lean','Итоговая рецензия'].map((title,i)=>({id:'proof-'+i,title,
      state:evidence[i]?'complete':i===3&&stoppedProof?(progress.proved>0?'partial':'stopped'):i===index?(active(run)?'active':stop?.code==='needs_review'?'review':'stopped'):'pending',step:i===5?'result':'lean'}));
  }
  function resultSummary(run){
    if(!run||active(run))return null;
    if(run.status==='draft')return {kind:'draft',achieved:'Новая версия постановки сохранена.',stopped:search(run)?'Поиск этой попытки ещё не запускался.':'Проверка этой версии ещё не запускалась.',next:search(run)?'Проверьте источник и отдельно продолжите поиск.':'Проверьте карточку источника и отдельно начните проверку.'};
    if(guided()?.partialSearchFinalizing(run))return {kind:'incomplete',achieved:'Результаты поиска ещё сохраняются.',stopped:'Поиск остановлен; итоговое число кандидатов пока недоступно.',next:'Обновите результаты после завершения сохранения.'};
    const preflight=guided()?.contractPreflight(run),proof=guided()?.formalEvidence(run),verdict=guided()?.verdict(run),stop=guided()?.terminationInfo(run);
    if(search(run))return {kind:verdict?.kind||'search',achieved:(guided()?.searchCandidateCount(run)??list(run.object_graph?.transitions).length)+' кандидатов сохранено',
      stopped:stop?.explanation||'Поиск завершён. Предложения требуют отдельной проверки.',next:'Выберите связь и изучите её условия перед запуском Lean.'};
    return {kind:verdict?.kind||'incomplete',
      achieved:proof?'Точная цель и обязательства проверены Lean.':preflight?.accepted?'Определения и тип цели приняты Lean.':draftPrepared(run)?'Черновик формальной постановки сохранён.':'Материалы и ход попытки сохранены.',
      stopped:stop?.explanation||(verdict?.kind==='proved'?'Смысловая рецензия согласована с проверенным утверждением.':guided()?.finalReview(run)?.title||'Итог не установлен.'),
      next:stop?.code==='invalid_contract'?'Подготовьте новую версию постановки с учётом диагностики.':stop?.code==='needs_review'?'Уточните объём утверждения и условия перед новой версией.':proof?'Изучите точные условия, ограничения и артефакты результата.':'Изучите диагностику и выберите следующую попытку или другую связь.'};
  }
  function sourceCardFields(card){
    if(!card||typeof card!=='object')return [];
    const values=[['Входные объекты',card.input_objects||card.objects],['Выходные объекты',card.output_objects],['Предпосылки',card.assumptions],
      ['Преобразование',card.operations||card.operation||card.construction],['Ожидаемый вывод',card.conclusion||card.selected_statement||card.statement||card.claim],['Границы',card.scope||card.limitations]];
    return values.filter(([,value])=>value&&(!Array.isArray(value)||value.length)).map(([label,value])=>({label,values:list(value).length?value:[value]}));
  }
  function compareCards(before,after){
    const labels={title:'Название',input_objects:'Входные объекты',output_objects:'Выходные объекты',operations:'Преобразование',assumptions:'Условия',conclusion:'Вывод',formal_statement:'Тип Lean',scope:'Границы'};
    return Object.entries(labels).filter(([key])=>JSON.stringify(before?.[key]??null)!==JSON.stringify(after?.[key]??null)).map(([key,label])=>({key,label,before:before?.[key]??null,after:after?.[key]??null}));
  }
  function displayValue(value){return typeof value==='string'?value:typeof value==='object'?[value.title||value.name,value.definition||value.description].filter(Boolean).join(' — ')||JSON.stringify(value):String(value);}
  class Workspace{
    constructor({document,onStep,onOpenRun,onDetails,onCancel,onStart}={}){this.doc=document||root.document;this.onStep=onStep;this.onOpenRun=onOpenRun;this.onDetails=onDetails;this.onCancel=onCancel;this.onStart=onStart;}
    el(tag,className='',value){const node=this.doc.createElement(tag);if(className)node.className=className;if(value!==undefined)node.textContent=String(value);return node;}
    button(label,action,className=''){const button=this.el('button','workspace-button '+className,label);button.type='button';button.onclick=action;return button;}
    prose(value,className=''){const node=this.el('p',className);if(root.MathPresentation?.render)root.MathPresentation.render(node,displayValue(value));else node.textContent=displayValue(value);return node;}
    render(run,draft,{step}={}){
      this.run=run;const context=this.doc.getElementById('workspace-context'),timeline=this.doc.getElementById('workspace-timeline');
      if(!context||!timeline)return;
      context.hidden=!run&&!draft;timeline.hidden=!run;
      const key=JSON.stringify([step,run?.id,run?.status,run?.phase,run?.active_stage,run?.updated_at,run?.usage,run?.live_elapsed_seconds,run?.outcome_summary,run?.proof_progress,run?.source_card,run?.lineage,run?.contract_verification?.status,run?.partial_search,run?.partial_graph_ref,run?.object_graph?.id,run?.object_graph?.revision,draft?.id,draft?.revision]);
      if(key===this.key)return;this.key=key;
      const processKey=`${run?.id||''}:${step||''}`;
      const expanded=this.processKey===processKey&&this.processDetails?this.processDetails.open:step==='result'&&root.matchMedia?.('(min-width: 1280px)').matches===true;
      const notesExpanded=this.processRunId===run?.id&&this.processNotes?.open===true;this.processNotes=null;
      context.replaceChildren();timeline.replaceChildren();
      if(!run&&!draft)return;
      const source=sourceIdentity(run),line=lineage(run),heading=this.el('div','workspace-context-copy'),crumbs=this.el('div','workspace-breadcrumbs');
      crumbs.append(this.button('Источник',()=>this.onStep?.('source')),this.el('span','','/'),this.button(search(run)?'Поиск связей':'Выбранная связь',()=>this.onStep?.('connections')));
      heading.append(crumbs,this.el('strong','workspace-source-title',run?source.title:draft.title||'Сохранённая карта'));
      const meta=this.el('div','workspace-context-meta');meta.append(this.el('span','workspace-version',line.version?'Версия '+line.version:guided()?.versionCaption(run)||'Карта'));
      if(line.parent)meta.append(this.button('← Предыдущая попытка',()=>this.onOpenRun?.(line.parent)));
      if(run&&step!=='result'){const verdict=guided()?.verdict(run);const badge=this.el('span','workspace-status',verdict?.title||run.status);badge.dataset.kind=verdict?.kind||'unknown';meta.append(badge);}
      context.append(heading,meta);
      if(!run)return;
      const stageList=stages(run),resources=resourceUsage(run),process=this.el('details','workspace-process'),summary=this.el('summary','workspace-process-summary'),body=this.el('div','workspace-process-body');
      process.open=expanded;this.processDetails=process;this.processRunId=run.id;this.processKey=processKey;
      const current=stageList.find(stage=>['active','stopped','review','partial'].includes(stage.state));
      summary.append(this.el('strong','','Ход исследования'),this.el('span','workspace-process-caption',current?current.title+' · '+stateNames[current.state]:stageList.filter(stage=>stage.state==='complete').length+' из '+stageList.length+' стадий завершено'),this.el('span','workspace-process-time',elapsedLabel(resources.seconds)));
      process.append(summary,body);timeline.append(process);
      const title=this.el('div','workspace-timeline-heading');
      if(run.status==='draft'&&run.ready_to_start)title.append(this.button(search(run)?'Продолжить поиск':'Запустить проверку этой версии',()=>this.onStart?.(),'workspace-launch'));
      else if(active(run)){const stop=this.button(run.status==='cancelling'?'Останавливаем…':'Остановить и сохранить',()=>this.onCancel?.(),'workspace-stop');stop.disabled=run.status==='cancelling';title.append(stop);}else title.append(this.button('Журнал попытки',()=>this.onDetails?.('attempts')));
      if(active(run)||run.status==='draft'&&run.ready_to_start)timeline.append(title);else body.append(title);
      const ol=this.el('ol','workspace-stages');
      for(const [i,stage]of stageList.entries()){const row=this.el('li','workspace-stage');row.dataset.state=stage.state;const button=this.button('',()=>this.onStep?.(stage.step));button.setAttribute('aria-label',stage.title+' — '+stateNames[stage.state]);button.append(this.el('span','workspace-stage-symbol',stage.state==='complete'?'✓':String(i+1)),this.el('strong','',stage.title),this.el('small','',stateNames[stage.state]));row.append(button);ol.append(row);}
      body.append(ol);const usage=this.el('div','workspace-resources');
      const progress=guided()?.proofProgress(run);if(progress?.started&&progress.obligations_total!==null)body.append(this.prose('Доказано обязательств: '+(progress.proved??'—')+' из '+progress.obligations_total+'. '+(guided()?.formalEvidence(run)?'Полный контракт проверен.':'Полный контракт ещё не подтверждён.'),'workspace-muted'));
      usage.append(this.el('span','',resources.calls+' / '+resources.callLimit+' вызовов'),this.el('span','',elapsedLabel(resources.seconds)+' / '+Math.ceil(resources.timeLimit/60)+' мин'),this.el('span','',resources.tokens.toLocaleString('ru-RU')+' токенов'),this.el('span','workspace-backend',resources.backend));body.append(usage);
      if(line.reason||run.draft_repair){const notes=this.el('details','workspace-process-notes');notes.open=notesExpanded;this.processNotes=notes;notes.append(this.el('summary','','Постановка и история исправлений'));
        if(line.reason)notes.append(this.prose(line.reason,'workspace-muted'));
        if(run.draft_repair){const repair=run.draft_repair;notes.append(this.prose('Черновик постановки '+(repair.version||1)+' · '+(({checking:'проверяем запись в Lean',typed:'типы приняты',stopped:'исправление остановлено'})[repair.status]||'состояние сохранено')+(Number.isInteger(repair.repairs)?' · исправлений '+repair.repairs+' из '+(repair.max_repairs||2):''),'workspace-muted'));if(repair.reason)notes.append(this.prose(repair.reason,'workspace-muted'));}body.append(notes);
      }
    }
    result(run){const summary=resultSummary(run);if(!summary)return null;const box=this.el('section','workspace-result-summary');box.setAttribute('aria-label','Краткий итог исследования');
      for(const [label,key]of [['Что сохранено','achieved'],['Состояние проверки','stopped'],['Следующий шаг','next']]){const item=this.el('div','workspace-result-item');item.append(this.el('h3','',label),this.prose(summary[key]));box.append(item);}return box;}
    sourceCard(card){const fields=sourceCardFields(card);if(!fields.length)return null;const box=this.el('section','workspace-source-card');box.setAttribute('aria-label','Карточка источника');box.append(this.el('h3','','Карточка источника'));
      for(const field of fields){const row=this.el('div','workspace-source-field');row.append(this.el('h4','',field.label));for(const value of field.values){row.append(this.prose(value));if(value&&typeof value==='object')for(const condition of [...list(value.parameters),...list(value.assumptions)])row.append(this.prose(condition,'workspace-muted'));}box.append(row);}
      if(card.formal_statement){const exact=this.el('details','workspace-source-grounding');exact.append(this.el('summary','','Точная формулировка Lean'),this.el('pre','',card.formal_statement));box.append(exact);}
      const sources=new Map(list(card.sources).map(source=>[source.id,source])),grounding=this.el('details','workspace-source-grounding');grounding.append(this.el('summary','','Связь карточки с источником'));
      if(!list(card.grounding).length)grounding.append(this.prose('Ссылки на конкретные фрагменты для этой карточки ещё не размечены.','workspace-muted'));
      for(const item of list(card.grounding)){const row=this.el('div','workspace-grounding-row'),source=sources.get(item.source_ref);row.append(this.el('strong','',item.component||'Фрагмент'),this.el('span','workspace-grounding-origin',({source_excerpt:'Фрагмент источника',proposed_abstraction:'Предложенная абстракция',user_revision:'Уточнение пользователя'})[item.origin]||'Происхождение не размечено'));
        if(item.quote)row.append(this.el('blockquote','',item.quote));if(source?.locator)row.append(this.prose(source.locator,'workspace-muted'));if(source?.url){try{const url=new URL(source.url);if(['https:','http:'].includes(url.protocol)){const link=this.el('a','',source.title||'Открыть источник');link.href=url.href;link.target='_blank';link.rel='noopener noreferrer';row.append(link);}}catch{}}grounding.append(row);}
      box.append(grounding);return box;}
  }
  return {Workspace,sourceIdentity,lineage,elapsedSeconds,resourceUsage,stages,resultSummary,sourceCardFields,compareCards,stateNames};
});
