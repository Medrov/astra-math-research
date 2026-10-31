'use strict';

(function(root,factory){const api=factory();if(typeof module==='object'&&module.exports)module.exports=api;else root.GuidedResearch=api;})(typeof window==='undefined'?globalThis:window,()=>{
  const active=new Set(['queued','running','cancelling']);
  const finished=new Set(['complete','completed']);
  const array=v=>Array.isArray(v)?v:[];
  const isSearch=r=>['structure','discover'].includes(r?.purpose);
  const awaitingStructureMap=run=>run?.purpose==='structure'&&!array(run.object_graph?.objects).length&&!array(run.object_graph?.transitions).length;
  const localMap=typeof module==='object'&&module.exports?require('./research-map.js'):null,mapModel=()=>globalThis.ResearchMap||localMap;
  const localObjects=typeof module==='object'&&module.exports?require('./object-graph.js'):null,objectModel=()=>globalThis.ObjectGraphModel||localObjects;
  const terminationLabels={invalid_plan:['План отклонён до проверки Lean','План не прошёл проверку формата. Это не результат доказательства или опровержения.'],invalid_contract:['Формальная постановка отклонена','Контракт не прошёл проверку; математический результат не установлен.'],proof_not_produced:['Текст доказательства не получен','Исполнитель не подготовил допустимое доказательство. Это не означает, что утверждение ложно.'],model_response_invalid:['Ответ исполнителя не принят','Ответ не соответствует требуемому формату; математический результат не установлен.'],lean_unproved:['Lean не подтвердил доказательство','Предложенное доказательство не прошло проверку. Это не является опровержением утверждения.'],needs_review:['Нужно уточнить постановку','Для продолжения требуется уточнить математический объём или условия.'],cancelled:['Исследование остановлено','Работа остановлена; сохранены достигнутые результаты.'],budget_exhausted:['Достигнут лимит работы','Отведённые вызовы или время закончились. Это не вывод о невозможности доказательства.'],infrastructure:['Сбой сервиса или окружения','Запуск остановлен технической ошибкой. Математический результат по ней не определяется.'],internal_error:['Сбой выполнения','Запуск остановлен ошибкой приложения. Откройте диагностику завершения.']};
  terminationLabels.lean_timeout=['Проверка Lean остановлена по времени','Lean не завершил проверку за отведённое время. Это не опровержение утверждения.'];
  function hasLeanEvidence(run){
    const reports=[run?.result?.verification,run?.verification];
    for(const item of [...array(run?.nodes),...array(run?.attempts)])reports.push(item.verification,item.result?.verification,item.report?.verification,item.last_result?.verification,...array(item.attempts).map(attempt=>attempt.verification));
    if(reports.some(report=>report&&report.kind!=='lean_contract_preflight'&&(report.compilation_success===true||report.audit?.status==='passed'||array(report.diagnostics).some(diagnostic=>/\.lean$/i.test(diagnostic.file||'')&&Number.isInteger(diagnostic.exit_code)))))return true;
    return array(run?.artifacts).some(artifact=>{const path=typeof artifact==='string'?artifact:artifact.path||artifact.name||'';return !/(^|[\\/])contract-preflight([\\/]|$)/i.test(path)&&/\.lean\.(?:stdout|stderr)\.log$/i.test(path);});
  }
  function contractPreflight(run){
    const report=run?.contract_verification;if(!report||report.kind!=='lean_contract_preflight')return null;
    const transition=array(run?.object_graph?.transitions).find(item=>item.id===run.selected_transition_id),task=run?.formal_contract||transition?.agent_task||run?.contract?.agent_task;
    const matches=!task?.target||report.target===task.target,accepted=matches&&report.proof_checked===false&&report.well_typed===true&&report.status==='complete'&&report.audit?.status==='passed';
    const diagnostics=array(report.diagnostics),failed=diagnostics.find(item=>item.timeout||item.cancelled||Number.isInteger(item.exit_code)&&item.exit_code!==0),lines=String((failed?.stderr||'')+'\n'+(failed?.stdout||'')).split(/\r?\n/).map(line=>line.trim()).filter(Boolean),line=lines.find(line=>/error|unknown constant|failed|unsolved goals/i.test(line))||lines[0];
    const diagnostic=line?((failed.file&&!line.startsWith(failed.file+':')?failed.file+': ':'')+line).slice(0,600):String(report.error||report.termination?.message||'');
    const timeout=report.status==='timeout'||report.termination?.code==='lean_timeout',cancelled=report.status==='cancelled';
    const title=!matches?'Отчёт проверки относится к другой цели':accepted?'Lean принял определения и тип цели':timeout?'Проверка постановки остановлена по времени':cancelled?'Проверка постановки остановлена':failed&&Number.isInteger(failed.exit_code)&&failed.exit_code!==0?'Lean отклонил постановку':'Постановка не прошла предварительную проверку';
    const probes=new Set(array(report.checked_obligations).map(item=>item.declaration));
    const definitions=array(report.declarations).filter(item=>['def','definition','opaque','inductive','structure'].includes(item.kind)&&!probes.has(item.name)).map(item=>item.name).filter(Boolean);
    const log=diagnostics.map(item=>String(item.stdout||'')+'\n'+String(item.stderr||'')).join('\n'),issues=[];
    if(!accepted&&matches){
      if(/invalid field notation/.test(log))issues.push('В формальной записи использовано обращение к полю или функции, которое Lean не может разобрать.');
      if(/failed to synthesize\s+MeasurableSpace/.test(log))issues.push('Для одного из объектов Lean не смог определить измеримую структуру, необходимую для работы с мерой.');
      else if(/failed to synthesize/.test(log))issues.push('Для выбранных объектов Lean не нашёл одну из необходимых математических структур.');
      if(/unknown (?:identifier|constant)/i.test(log))issues.push('В постановке используется имя, которое не найдено в подключённых определениях или библиотеках.');
      if(/type mismatch/.test(log))issues.push('Типы некоторых выражений не совпадают; нужно уточнить запись объектов или преобразование между ними.');
    }
    return {report,accepted,title,diagnostic,issues,target:report.target,statement:matches?task?.statement:null,prelude:matches?task?.prelude:null,definitions,stage:report.termination?.stage||'lean_contract_preflight'};
  }
  function terminationInfo(run){
    if(!run||active.has(run.status)||isSearch(run)&&finished.has(run.status))return null;
    let value=run.termination||run.result?.termination;
    if(!terminationLabels[value?.code]){
      const error=String(run.error||run.result?.error||'');let code=null,stage='';
      if(run.status==='cancelled')code='cancelled';else if(run.status==='budget_exhausted')code='budget_exhausted';
      else if(run.requires_review===true||run.formalization_review?.status==='needs_review'||['needs_review','mismatch','uncertain'].includes(run.contract_review?.status)||run.status==='needs_review'){code='needs_review';stage=run.contract_review?'validate_contract':'formalize_transition';}
      else if(error.includes('Тип леммы не должен содержать команды Lean.')){code='invalid_plan';stage='plan';}
      else if(error.includes('Агент не вернул допустимый текст доказательства.')){code='proof_not_produced';stage='prove';}
      else if(run.result?.verification&&run.result.verification.success===false){code='lean_unproved';stage='verify';}
      if(!code)return null;value={code,stage,message:error||run.result?.reason||run.formalization_review?.reason||run.contract_review?.reason||''};
    }
    const preflight=contractPreflight(run);
    if(value.code==='invalid_contract'&&preflight&&value.stage==='lean_contract_preflight')return {...value,title:preflight.title,explanation:'Lean остановился при чтении определений и типа цели, до доказательства. '+(preflight.issues.length?preflight.issues.join(' '):preflight.diagnostic||value.message||'Подробности сохранены в диагностике Lean.')};
    if(value.code==='invalid_contract'&&preflight?.accepted&&['compose','lean_contract','final_composition'].includes(value.stage))return {...value,title:'Доказательство не прошло проверку на точную цель',explanation:'Lean ранее принял определения и тип цели. Последующая проверка доказательства на соответствие этому контракту не пройдена.'};
    if(value.code==='proof_not_produced'&&preflight?.accepted)return {...value,title:'Доказательство не получено',explanation:'Lean принял определения и тип цели. Доказательство не получено; принятие постановки не является доказательством.'};
    if(value.code==='invalid_plan'&&preflight?.accepted&&!hasLeanEvidence(run)&&!/^(?:replan|revise|revise_plan|plan_revision)$/.test(value.stage||''))return {...value,title:'План доказательства отклонён',explanation:'Lean принял определения и тип цели, но план доказательства не прошёл проверку формата. Доказательство не проверялось.'};
    if(value.code==='invalid_plan'&&(hasLeanEvidence(run)||/^(?:replan|revise|revise_plan|plan_revision)$/.test(value.stage||'')))return {...value,title:'Новый план доказательства отклонён',explanation:'Текущий вариант плана не прошёл проверку формата и не передавался в Lean.'+(hasLeanEvidence(run)?' Ранее выполненные проверки сохранены; их результаты рассматриваются отдельно.':'')};
    const[title,explanation]=terminationLabels[value.code];return {...value,title,explanation};
  }
  function finalReview(run){
    if(isSearch(run))return {status:'not_applicable',title:'Итоговая рецензия доказательства не применяется к поиску.',reason:'Поиск сохраняет предложения; доказательство проверяется отдельным запуском.'};
    const review=run?.final_semantic_review||run?.result?.semantic_review||(run?.result?.verification?run.semantic_review:null),status=review?.status;
    if(['aligned','reviewed_fixture','mismatch','uncertain'].includes(status))return {status,title:'Итоговая смысловая рецензия',reason:review.reason||review.summary||({aligned:'Соответствует постановке.',reviewed_fixture:'Смысл подготовленного примера проверен.',mismatch:'Обнаружено расхождение с постановкой.',uncertain:'Смысл требует дополнительной проверки.'})[status],limitations:array(review.limitations)};
    const termination=terminationInfo(run),reason=review?.reason||review?.note||termination?.title||'Запуск не дошёл до итоговой рецензии.';
    return {status:active.has(run?.status)?'pending':'not_performed',title:active.has(run?.status)?'Итоговая рецензия ещё не выполнена':'Итоговая рецензия не проводилась: '+reason,reason};
  }
  function formalEvidence(run){
    if(run?.purpose!=='prove')return false;
    const report=run?.result?.verification,target=run?.formal_contract?.target||array(run?.object_graph?.transitions).find(item=>item.id===run.selected_transition_id)?.agent_task?.target||run?.result?.fixture?.target;
    return !!target&&report?.target===target&&report.success===true&&report.compilation_success===true&&report.target_preserved===true&&report.obligations_passed===true&&report.audit?.status==='passed';
  }
  function verdict(run){
    if(!run)return {kind:'empty',title:'Выберите источник'};
    if(active.has(run.status))return {kind:'running',title:isSearch(run)?'Astra ищет связи':'Проверяем выбранную связь'};
    if(isSearch(run)&&finished.has(run.status))return {kind:'search',title:'Поиск завершён',count:array(run.object_graph?.transitions).length};
    const v=run.result?.verification,semantic=run.final_semantic_review||run.result?.semantic_review||run.semantic_review;
    const expectedTarget=run.formal_contract?.target||array(run.object_graph?.transitions).find(t=>t.id===run.selected_transition_id)?.agent_task?.target||run.result?.fixture?.target;
    const exact=finished.has(run.status)&&v?.success===true&&v.target_preserved===true&&v.obligations_passed===true&&v.audit?.status==='passed'&&(!expectedTarget||v.target===expectedTarget);
    if(exact&&['aligned','reviewed_fixture'].includes(semantic?.status)&&['proved','verified'].includes(run.result?.outcome||run.outcome))return {kind:'proved',title:'Связь проверена в Lean'};
    if(exact&&['aligned','reviewed_fixture'].includes(semantic?.status)&&(run.result?.outcome||run.outcome)==='refuted')return {kind:'refuted',title:'Lean подтвердил контрпример'};
    if(exact)return {kind:'formal_only',title:['pending','not_performed','not_established'].includes(semantic?.status)?'Lean-цель проверена · итоговая рецензия не выполнена':'Lean-цель проверена · смысл не подтверждён'};
    if(!finished.has(run.status)&&formalEvidence(run))return {kind:'formal_only',title:finalReview(run).status==='not_performed'?'Lean подтвердил формальную цель; итоговая рецензия не проведена':'Lean-цель проверена · запуск завершён не полностью'};
    if((run.result?.outcome||run.outcome)==='refuted')return {kind:'incomplete',title:'Опровержение не подтверждено отчётом Lean'};
    const termination=terminationInfo(run);if(termination)return {kind:'incomplete',title:termination.title,reasonCode:termination.code};
    const titles={failed:'Запуск завершился с ошибкой',cancelled:'Исследование остановлено',interrupted:'Исследование прервано',budget_exhausted:'Достигнут лимит работы'};
    return {kind:'incomplete',title:titles[run.status]||'Связь пока не подтверждена'};
  }
  function titleOf(run){return array(run?.object_graph?.transitions).find(t=>t.id===run.selected_transition_id)?.title||(run?.purpose==='structure'?(mapModel()?.sourceTransition(run)?'Аналоги: '+mapModel().sourceTransition(run).transition.title:'Поиск общей структуры'):run?.purpose==='discover'?'Поиск переходов в источнике':run?.title)||'Исследование';}
  function budget(calls,minutes){const c=Number(calls),m=Number(minutes);if(!Number.isInteger(c)||c<1||c>24||!Number.isFinite(m)||m<1||m>30)throw new Error('Укажите от 1 до 24 вызовов и от 1 до 30 минут.');return {max_calls:c,timeout_seconds:Math.round(m*60),max_parallel:2};}
  function matchExample(paper,examples){return array(examples).find(e=>e.versioned_id===paper?.versioned_id&&e.arxiv_id===paper?.arxiv_id)||null;}
  function theoremChoices(source){return array(source?.declarations).filter(d=>d.kind==='theorem'&&!/(?:^|\.)(?:eq_\d+|_proof_\d+|_match_\d+)$/.test(d.name));}
  function sourceReady(source){return source?.status==='ready'&&source.inspection?.status==='complete'&&source.inspection?.success===true;}
  function structurePayload(source,target,limits,question=''){
    if(!sourceReady(source)||!theoremChoices(source).some(t=>t.name===target))throw new Error('Выберите теорему из успешно проверенного источника.');
    return {purpose:'structure',mode:'multi',source_id:source.id,target,budget:limits,...(question.trim()?{question:question.trim()}:{})};
  }
  function transitionSearchPayload(graph,transition,limits,question=''){
    const selected=array(graph?.transitions).find(item=>item.id===transition?.id);
    if(!graph?.id||!Number.isInteger(graph.revision)||graph.revision<1||!selected)throw new Error('Откройте сохранённую версию карты и выберите исходный переход.');
    if(mapModel()?.transitionRole({object_graph:graph},selected)!=='article')throw new Error('Поиск аналогов запускается из исходного перехода статьи; кандидат общей структуры проверяется отдельно.');
    return {purpose:'structure',mode:'multi',graph_id:graph.id,graph_revision:graph.revision,transition_id:selected.id,budget:limits,...(question.trim()?{question:question.trim()}:{})};
  }
  function sourceNavigation(run){
    const origin=mapModel()?.sourceTransition(run),items=[];
    if(origin)items.push({kind:'article',label:'← Исходный переход статьи',ref:origin.graph_ref,transitionId:origin.transition.id});
    const ref=run?.source_graph_ref;if(ref?.id&&(!origin||ref.id!==origin.graph_ref.id||ref.revision!==origin.graph_ref.revision))items.push({kind:'parent',label:origin?'← Кандидаты поиска':'← Все переходы источника',ref,transitionId:run.source_transition_id||run.selected_transition_id});
    return items;
  }
  function versionCaption(run){
    const source=run?.purpose==='prove'?run.source_graph_ref:null,formal=run?.graph_ref;
    if(source?.id&&Number.isInteger(source.revision))return 'Версия кандидата '+source.revision+(formal?.id&&formal.id!==source.id?' · Формальный контракт '+formal.revision:'');
    return 'Версия постановки '+(formal?.revision||run?.contract?.version||1);
  }
  function refinementContext(graph,transitionId){
    if(!graph?.id||!Number.isInteger(graph.revision)||graph.revision<1)throw new Error('Для уточнения нужна сохранённая версия карты.');
    const transition=array(graph.transitions).find(item=>item.id===transitionId);
    if(!transition||transition.agent_task||!['candidate','literature_only'].includes(transition.formulation_status))throw new Error('Этот редактор уточняет переход, для которого ещё не подготовлена Lean-постановка.');
    const ids=[...new Set([...array(transition.source_ids),...array(transition.target_ids)])],byId=new Map(array(graph.objects).map(object=>[object.id,object]));
    if(ids.some(id=>!byId.has(id)))throw new Error('В карте отсутствует объект выбранного перехода. Сначала восстановите постановку.');
    const shared=new Set(array(graph.transitions).filter(item=>item.id!==transitionId).flatMap(item=>[...array(item.source_ids),...array(item.target_ids)]));
    return {transition,objects:ids.map(id=>({value:byId.get(id),editable:!shared.has(id)}))};
  }
  function refinementTarget(run){
    if(!run||run.purpose!=='prove'||active.has(run.status)||!run.selected_transition_id)return null;
    if(run.graph_ref&&(run.graph_ref.id!==run.object_graph?.id||run.graph_ref.revision!==run.object_graph?.revision))return null;
    try{return refinementContext(run.object_graph,run.selected_transition_id);}catch{return null;}
  }
  function refinementDraft(graph,transitionId,fields){
    const context=refinementContext(graph,transitionId),draft=JSON.parse(JSON.stringify(graph)),lineList=value=>Array.isArray(value)?value.map(String):String(value||'').split('\n').map(line=>line.trim()).filter(Boolean);
    const required=(value,label)=>{if(typeof value!=='string'||!value.trim())throw new Error('Заполните поле «'+label+'».');return value.trim();};
    const transition=objectModel().revisionDraft({transitions:[context.transition]}).transitions[0];
    transition.title=required(fields.title,'Название перехода');transition.claim=required(fields.claim,'Утверждение перехода');transition.construction=required(fields.construction,'Преобразование');transition.assumptions=lineList(fields.assumptions);
    draft.transitions[draft.transitions.findIndex(item=>item.id===transitionId)]=transition;
    const editable=new Set(context.objects.filter(item=>item.editable).map(item=>item.value.id));
    for(const edit of array(fields.objects)){
      if(!editable.has(edit.id))throw new Error('Общий объект нельзя изменять в редакторе одного перехода.');
      const object=draft.objects.find(item=>item.id===edit.id);object.title=required(edit.title,'Название объекта');object.definition=required(edit.definition,'Определение объекта');object.parameters=lineList(edit.parameters);object.assumptions=lineList(edit.assumptions);
    }
    const natural=value=>JSON.stringify({title:value.title,claim:value.claim,construction:value.construction,assumptions:value.assumptions});
    if(natural(transition)===natural(context.transition)&&JSON.stringify(draft.objects)===JSON.stringify(graph.objects))throw new Error('Постановка не изменилась. Уточните утверждение, условия или объекты перед сохранением.');
    return draft;
  }
  function retryPayload(run){
    if(!run||run.purpose!=='prove'||!['failed','cancelled','interrupted','budget_exhausted','timeout'].includes(run.status))throw new Error('Повторная проверка доступна для завершённой неудачной попытки.');
    const graph=run.object_graph,ref=run.graph_ref,transition=array(graph?.transitions).find(item=>item.id===run.selected_transition_id);
    if(!ref?.id||graph?.id!==ref.id||graph.revision!==ref.revision||!objectModel().formulation(transition).formalized)throw new Error('У попытки нет сохранённой точной Lean-постановки. Сначала уточните переход.');
    if(!['single','multi','pilot'].includes(run.mode)||!Number.isInteger(run.budget?.max_calls)||run.budget.max_calls<1||!Number.isFinite(run.budget?.timeout_seconds)||run.budget.timeout_seconds<=0)throw new Error('Режим или бюджет предыдущей попытки не сохранён.');
    const budget={max_calls:run.budget.max_calls,timeout_seconds:run.budget.timeout_seconds,...(run.budget.max_parallel!==undefined?{max_parallel:run.budget.max_parallel}:{})};
    return objectModel().verificationPayload(graph,transition,{mode:run.mode,budget,msc_codes:array(graph.msc_codes)});
  }
  function canRetry(run){try{retryPayload(run);return true;}catch{return false;}}
  function discoveryPayload(paper,section,limits,question=''){
    if(!paper?.versioned_id)throw new Error('Сначала загрузите статью.');
    if(section&&!array(paper.sections).some(s=>s.id===section))throw new Error('Раздел отсутствует в сохранённой версии статьи.');
    return {purpose:'discover',mode:'multi',paper_ids:[paper.versioned_id],section_ids:section?[section]:[],msc_codes:array(paper.msc_codes),budget:limits,
      title:'Переходы из '+paper.versioned_id,
      question:'Из сохранённой статьи «'+paper.title+'»'+(section?' (раздел '+section+')':'')+' выдели математические объекты и до шести конкретных переходов для последующей формализации в Lean. Для каждого укажи предпосылки, точный вывод и происхождение. Отдели утверждения статьи от новых гипотез. Области MSC уточни по содержанию. '+question.trim()};
  }
  function progressText(run){
    const p=run?.phase||'';
    if(run?.status==='cancelling')return 'Завершаем текущий шаг и сохраняем работу';
    if(run?.status==='queued')return 'Запуск поставлен в очередь';
    if(p==='lean_contract_preflight')return 'Lean проверяет определения и тип цели';
    if(/structure_profile/.test(p))return 'Определяем объекты, операции и общий механизм';
    if(/structure_search|route|direction/.test(p))return 'Ищем в трёх направлениях MSC';
    if(/structure_merge|structure_publish/.test(p))return 'Собираем связи и объяснения выбора областей';
    if(/retriev|search/.test(p))return 'Ищем подходящие определения и леммы';
    if(/formal|propos/.test(p))return 'Фиксируем условия и точную формальную цель';
    if(/semantic|critic/.test(p))return 'Сверяем математический смысл и постановку';
    if(/plan|revise/.test(p))return 'Строим граф необходимых лемм';
    if(/verify|audit|certif/.test(p))return 'Lean проверяет доказательство и зависимости';
    if(/prove/.test(p))return 'Доказываем леммы и исправляем ошибки Lean';
    return 'Astra выполняет исследование';
  }
  const stepNames={source:'Источник',connections:'Направления и связи',lean:'Проверка Lean',result:'Результат'};
  function stepNavigation(run,draft){
    const proof=run?.purpose==='prove',started=!!run||!!draft,terminal=!!run&&!active.has(run.status);
    return Object.entries(stepNames).map(([id,title])=>({id,title,available:id==='source'||id==='connections'&&started||id==='lean'&&proof||id==='result'&&terminal,
      reason:id==='connections'?'После запуска поиска':id==='lean'?'После выбора связи':id==='result'?'После завершения запуска':''}));
  }
  function defaultStep(run,draft){return !run?(draft?'connections':'source'):isSearch(run)?'connections':active.has(run.status)?'lean':'result';}
  function selectedStep(run,draft,requested){return stepNavigation(run,draft).some(s=>s.id===requested&&s.available)?requested:defaultStep(run,draft);}
  class Workspace{
    constructor(callbacks){
      this.cb=callbacks;this.kind='arxiv';this.source=null;this.paper=null;this.catalog=null;this.busy=false;this.token=0;this.runKey='';this.historyKey='';this.state=null;this.step=null;this.stepContext=null;
      this.$('guided-structure-slot').append(this.$('structure-results'));
      this.map=window.ResearchMap ? new window.ResearchMap.Workspace({container:this.$('guided-map'),onVerify:(graph,transition)=>this.verify(graph,transition),onSearchAnalogies:(graph,transition)=>this.searchAnalogies(graph,transition),onOpenRun:id=>this.openRun(id).catch(e=>this.cb.error(e.message)),onSelection:selection=>this.cb.mapSelection?.(selection)}) : null;
      this.history=window.ResearchHistory ? new window.ResearchHistory.Workspace({container:this.$('guided-history'),onOpen:id=>this.openRun(id),onError:message=>this.cb.error(message)}) : null;
      this.candidateChecks=window.CandidateChecks?new window.CandidateChecks.Workspace({container:this.$('guided-checks'),api:this.cb.api,onSelect:(graph,t)=>this.showMap('objects','transition:'+t.id),onVerify:(graph,t)=>this.verify(graph,t),onOpenRun:id=>this.openRun(id),onError:message=>this.cb.error(message)}):null;
      this.$('guided-history-open').onclick=()=>this.history?.show();
      this.$('guided-source-form').onsubmit=e=>{e.preventDefault();this.prepare();};
      this.$('guided-start').onclick=()=>this.start();
      this.$('guided-theorem').onchange=()=>this.renderTheorem();
      this.$('guided-section').onchange=()=>this.renderTheorem();
      for(const id of ['guided-file','guided-example'])this.$(id).onchange=()=>this.invalidateSource();
      this.$('guided-arxiv').oninput=()=>this.invalidateSource();
      for(const b of document.querySelectorAll('[data-guided-source]'))b.onclick=()=>this.setKind(b.dataset.guidedSource);
    }
    $(id){return document.getElementById(id);}
    urlStep(){return typeof location==='undefined'?null:new URL(location.href).searchParams.get('step');}
    restoreStep(){if(!this.state)return;this.step=selectedStep(this.state.run,this.state.draftGraph,this.urlStep());this.runKey='';this.render(this.state);}
    goStep(id,{scroll=true,remember=true}={}){
      if(!this.state||!stepNavigation(this.state.run,this.state.draftGraph).some(s=>s.id===id&&s.available))return;
      this.step=id;this.runKey='';
      if(remember&&typeof location!=='undefined'&&(this.state.run||this.state.draftGraph)){const url=new URL(location.href);url.searchParams.set('step',id);if(url.href!==location.href)history.pushState(null,'',url);}
      this.render(this.state);
      if(scroll){const nav=this.$('guided-steps');nav.scrollIntoView({behavior:'smooth',block:'start'});this.stepButtons?.[id]?.focus({preventScroll:true});}
    }
    renderSteps(run,draft){
      const steps=stepNavigation(run,draft),box=this.$('guided-steps');
      if(!this.stepButtons){this.stepButtons={};box.replaceChildren();for(const[ordinal,step]of steps.entries()){
        const li=this.el('li'),b=this.el('button',{type:'button'}),label=this.el('div',{},step.title),hint=this.el('small');b.onclick=()=>this.goStep(step.id);
        b.setAttribute('data-guided-step',step.id);b.setAttribute('aria-controls',({source:run||draft?'guided-saved-source':'guided-setup',connections:'guided-map',lean:'guided-lean',result:'guided-result'})[step.id]);
        b.append(this.el('span',{'aria-hidden':'true'},ordinal+1),label);label.append(hint);li.append(b);box.append(li);this.stepButtons[step.id]=b;b.hint=hint;
      }}
      for(const step of steps){const b=this.stepButtons[step.id];b.disabled=!step.available;b.hint.textContent=step.available?'':step.reason;b.hint.hidden=step.available;b.title=step.available?'Открыть: '+step.title:step.reason;if(step.id===this.step)b.setAttribute('aria-current','step');else b.removeAttribute('aria-current');}
      this.stepButtons.source.setAttribute('aria-controls',run||draft?'guided-saved-source':'guided-setup');
      const actions=this.$('guided-step-actions');actions.replaceChildren();actions.hidden=!run&&!draft;const available=steps.filter(s=>s.available),i=available.findIndex(s=>s.id===this.step);
      if(i>0)actions.append(this.button('← '+available[i-1].title,()=>this.goStep(available[i-1].id)));
      if(i<available.length-1)actions.append(this.button(available[i+1].title+' →',()=>this.goStep(available[i+1].id)));
    }
    renderSavedSource(run,draft){
      const box=this.$('guided-saved-source'),origin=mapModel()?.sourceTransition(run||(draft?{object_graph:draft}:null)),graph=run?.object_graph||draft,source=run?.contract?.source_library||run?.source_snapshot;
      const key=JSON.stringify([run?.id,draft?.id,draft?.revision,origin,source,run?.paper_manifest]);if(key===this.sourcePanelKey)return;this.sourcePanelKey=key;box.replaceChildren();
      box.append(this.el('p',{class:'eyebrow'},'1 · Источник'),this.el('h2',{},'Отправная точка исследования'),this.prose('Сохранённый источник этого запуска. Просмотр этапов не изменяет постановку и не запускает исследование повторно.','p','guided-note'));
      const papers=array(run?.paper_manifest||run?.contract?.paper_manifest);
      for(const paper of papers){box.append(this.el('h3',{},paper.title||paper.versioned_id),this.el('span',{class:'guided-badge'},'arXiv '+paper.versioned_id));const link=paper.source_urls?.abstract;try{if(link&&['http:','https:'].includes(new URL(link).protocol)){const p=this.el('p');p.append(this.el('a',{href:link,target:'_blank',rel:'noopener noreferrer'},'Открыть сохранённую версию статьи ↗'));box.append(p);}}catch{} }
      if(origin){box.append(this.el('h3',{},origin.transition.title),this.prose(origin.transition.claim));if(origin.transition.construction)box.append(this.prose(origin.transition.construction));for(const condition of array(origin.transition.assumptions))box.append(this.prose(condition,'p','guided-note'));
        const objects=this.el('div',{class:'guided-source-objects'});for(const object of array(origin.objects)){const item=this.el('details');item.append(this.el('summary',{},object.title||object.id),this.prose(object.definition));objects.append(item);}box.append(objects);
      }else if(source){box.append(this.el('h3',{},source.title||source.name||'Исходная теорема Lean'));const declaration=source.selected_declaration;if(declaration)box.append(this.details(declaration.name,declaration.type));if(source.source_sha256)box.append(this.details('Зафиксированный исходник',source.content||source.source_sha256));
      }else if(!papers.length){box.append(this.el('h3',{},run?.title||graph?.title||'Исследовательский вопрос'),this.prose(run?.claim||run?.contract?.question||graph?.question||'Материалы доступны в источниках исследования.'));}
      if(!source&&!origin&&run?.target)box.append(this.details('Выбранная теорема',run.target));
      const sources=array(origin?.sources||graph?.sources).filter(s=>s.url);if(sources.length){const refs=this.el('details',{class:'guided-details'});refs.append(this.el('summary',{},'Разделы и ссылки источника'));for(const source of sources){try{if(['http:','https:'].includes(new URL(source.url).protocol)){const p=this.el('p');p.append(this.el('a',{href:source.url,target:'_blank',rel:'noopener noreferrer'},source.title||source.locator||source.url));refs.append(p);}}catch{}}box.append(refs);}
    }
    renderLeanStage(run){
      const box=this.$('guided-lean');box.replaceChildren();if(!run||run.purpose!=='prove')return;
      box.append(this.el('p',{class:'eyebrow'},'3 · Проверка Lean'),this.el('h2',{},'Постановка и ход проверки'));
      const transition=array(run.object_graph?.transitions).find(t=>t.id===run.selected_transition_id),task=run.formal_contract||transition?.agent_task||run.contract?.agent_task;
      if(transition?.title)box.append(this.el('h3',{},transition.title));
      const panel=this.contractPanel(run);if(panel)box.append(panel);else if(task?.statement)box.append(this.details('Точный тип цели Lean',task.statement));
      if(!active.has(run.status)){const stop=terminationInfo(run);box.append(this.prose(stop?stop.title+'. '+stop.explanation:verdict(run).title));}
      if(!array(run.nodes).length&&!array(run.result?.nodes).length)box.append(this.prose('Граф лемм пока не построен. Здесь появятся леммы и их проверки, когда запуск дойдёт до доказательства.','p','guided-note'));
      box.append(this.button('Доказательство и отчёт Lean',()=>this.cb.details('result')));
    }
    el(tag,attrs={},text){const n=document.createElement(tag);for(const[k,v]of Object.entries(attrs))n.setAttribute(k,String(v));if(text!==undefined)n.textContent=String(text);return n;}
    prose(text,tag='p',className=''){const n=this.el(tag,{class:className});if(window.MathPresentation)window.MathPresentation.render(n,String(text||''));else n.textContent=String(text||'');return n;}
    button(text,fn,primary=false){const b=this.el('button',{type:'button',class:'button '+(primary?'primary':'secondary')},text);b.onclick=fn;return b;}
    details(title,text){const n=this.el('details',{class:'guided-details'});n.append(this.el('summary',{},title),this.el('pre',{},typeof text==='string'?text:JSON.stringify(text,null,2)));return n;}
    notice(text,kind=''){const n=this.$('guided-source-status');n.textContent=text;n.dataset.state=kind;}
    setBusy(value,message=''){this.busy=value;for(const id of ['guided-load','guided-load-lean','guided-load-example','guided-theorem','guided-section','guided-file','guided-example','guided-arxiv'])this.$(id).disabled=value;for(const b of document.querySelectorAll('[data-guided-source]'))b.disabled=value;if(message)this.notice(message,value?'running':'');this.updateStart();}
    invalidateSource(){if(this.busy)return;this.source=null;this.paper=null;this.token++;this.$('guided-selection').hidden=true;this.$('guided-source-preview').replaceChildren();this.$('guided-theorem-preview').replaceChildren();this.notice('');this.updateStart();}
    setKind(kind){if(this.busy)return;this.kind=kind;this.source=null;this.paper=null;this.token++;for(const b of document.querySelectorAll('[data-guided-source]'))b.setAttribute('aria-pressed',String(b.dataset.guidedSource===kind));for(const k of ['arxiv','lean','example'])this.$('guided-'+k+'-fields').hidden=k!==kind;this.$('guided-selection').hidden=true;this.$('guided-source-preview').replaceChildren();this.notice('');this.updateStart();this.ensureCatalog().catch(()=>{});}
    async ensureCatalog(){
      if(this.catalog)return this.catalog;if(this.catalogPromise)return this.catalogPromise;
      this.catalogPromise=this.cb.api('/api/structure/sources').then(data=>{this.catalog=data;const s=this.$('guided-example');s.replaceChildren();for(const e of array(data.examples))s.append(this.el('option',{value:e.id},e.title||e.id));if(!s.options.length)s.append(this.el('option',{value:''},'Подготовленные примеры недоступны'));return data;}).catch(e=>{this.notice('Не удалось загрузить список источников: '+e.message,'error');throw e;}).finally(()=>{this.catalogPromise=null;});return this.catalogPromise;
    }
    async prepare(){
      if(this.busy)return;const token=++this.token;this.source=null;this.paper=null;this.$('guided-selection').hidden=true;this.$('guided-source-preview').replaceChildren();this.setBusy(true,'Готовим источник…');
      try{
        const catalog=await this.ensureCatalog();if(token!==this.token)return;
        if(this.kind==='arxiv'){
          const reference=this.$('guided-arxiv').value.trim();if(!reference)throw new Error('Вставьте ссылку или идентификатор arXiv.');
          this.notice('Загружаем и фиксируем версию статьи…','running');const data=await this.cb.api('/api/arxiv/import',{reference});if(token!==this.token)return;this.paper=data.paper||data;this.renderPaper(matchExample(this.paper,catalog.examples));
        }else if(this.kind==='example'){
          const example=array(catalog.examples).find(e=>e.id===this.$('guided-example').value);if(!example)throw new Error('Выберите подготовленный пример.');await this.prepareExample(example,token);
        }else{
          const file=this.$('guided-file').files?.[0];if(!file||!file.name.toLowerCase().endsWith('.lean'))throw new Error('Выберите один файл .lean.');if(file.size>250000)throw new Error('Размер файла должен быть не больше 250 000 байт.');
          this.notice('Lean проверяет исходник и аксиомы. Это может занять около минуты…','running');const data=await this.cb.api('/api/structure/sources',{name:file.name,content:await file.text()});if(token!==this.token)return;this.acceptSource(data.source);
        }
      }catch(e){if(token===this.token)this.notice(e.message,'error');}
      finally{if(token===this.token)this.setBusy(false);}
    }
    async prepareExample(example,token){
      this.notice('Открываем подготовленную формализацию и проверяем её доступность…','running');
      const saved=array(this.catalog?.sources).find(s=>s.status==='ready'&&s.source_sha256===example.source_sha256);
      const data= saved ? await this.cb.api('/api/structure/sources/'+encodeURIComponent(saved.id)) : await this.cb.api('/api/structure/sources',{example_id:example.id});
      if(token!==this.token)return;this.acceptSource(data.source,example.recommended_target,example.scope_note);
    }
    async usePrepared(example){if(this.busy)return;const token=++this.token;this.setBusy(true);try{await this.prepareExample(example,token);}catch(e){if(token===this.token)this.notice(e.message,'error');}finally{if(token===this.token)this.setBusy(false);}}
    renderPaper(example){
      const p=this.paper,box=this.$('guided-source-preview');box.replaceChildren();box.append(this.el('span',{class:'guided-badge'},'arXiv '+p.versioned_id),this.el('h3',{},p.title),this.prose(array(p.authors).join(' · '),'p','guided-note'));
      if(array(p.msc_codes).length)box.append(this.prose('Метки статьи: MSC '+p.msc_codes.join(', ')+'. Направления исследования уточняются по содержанию.','p','guided-note'));
      if(example){const card=this.el('div',{class:'guided-prepared'});card.append(this.el('strong',{},'Для этой статьи есть проверенная отправная точка'),this.prose(example.scope_note||'Подготовленная формализация отдельного шага статьи.'),this.button('Использовать проверенную теорему',()=>this.usePrepared(example),true));box.append(card);}
      const note=example?'Можно использовать подготовленный Lean-шаг выше или сначала выделить другие переходы из статьи.':'Сначала Astra выделит переходы статьи. Затем выберите переход, найдите аналоги в трёх областях MSC и проверьте выбранную общую структуру в Lean.';
      box.append(this.prose(note,'p','guided-note'));
      const sel=this.$('guided-section');sel.replaceChildren(this.el('option',{value:''},'Вся доступная статья'));for(const s of array(p.sections).filter(s=>s.id!=='document'))sel.append(this.el('option',{value:s.id},s.title||s.heading||s.id));
      this.$('guided-selection').hidden=false;this.$('guided-theorem-field').hidden=true;this.$('guided-section-field').hidden=false;this.$('guided-theorem-preview').replaceChildren();this.notice('Источник сохранён. Следующий запуск будет искать проверяемые переходы.','ready');this.updateStart();
    }
    acceptSource(source,recommended='',scope=''){
      if(!sourceReady(source))throw new Error(source?.inspection?.error||'Исходник не прошёл Lean. Поиск по нему пока недоступен.');this.source=source;
      const box=this.$('guided-source-preview');box.replaceChildren(this.el('span',{class:'guided-badge good'},'Lean-источник проверен'),this.el('h3',{},source.title||source.name));if(scope)box.append(this.prose(scope));
      box.append(this.prose('Astra сама выберет три направления MSC по структуре выбранной теоремы.','p','guided-note'));
      const choices=theoremChoices(source),picker=this.$('guided-theorem');picker.replaceChildren(this.el('option',{value:''},'Выберите исходную теорему…'));for(const d of choices)picker.append(this.el('option',{value:d.name},(window.MathPresentation?.sourceSummary(source,d.name)?.title||d.name.split('.').pop())+(d.name===recommended?' · рекомендуемая отправная точка':'')));
      if(choices.some(d=>d.name===recommended))picker.value=recommended;else if(choices.length===1)picker.value=choices[0].name;
      this.$('guided-selection').hidden=false;this.$('guided-theorem-field').hidden=false;this.$('guided-section-field').hidden=true;this.notice(choices.length?'Источник готов. Выберите теорему и начните поиск.':'Файл проверен, но исходных теорем для поиска не найдено.',choices.length?'ready':'error');this.renderTheorem();
    }
    renderSummary(box,summary){
      if(!summary)return;if(summary.title)box.append(this.el('h3',{},summary.title));if(summary.description)box.append(this.prose(summary.description));
      const formulas=array(summary.formulas),featured=formulas.filter(f=>f.featured),main=featured.length?featured:formulas;
      const add=(parent,item)=>{const f=this.el('div',{class:'guided-formula'});if(item.label)f.append(this.el('span',{class:'guided-note'},item.label));const math=this.el('div');window.MathPresentation?.formula(math,item.tex,{display:true});f.append(math);parent.append(f);};
      for(const item of main)add(box,item);
      if(featured.length&&featured.length<formulas.length){const more=this.el('details',{class:'guided-details'});more.append(this.el('summary',{},'Обозначения и построение'));for(const item of formulas.filter(f=>!f.featured))add(more,item);box.append(more);}
      if(array(summary.assumptions).length){const conditions=this.el('div',{class:'guided-assumptions'}),ul=this.el('ul');conditions.append(this.el('h4',{},'Условия'));for(const item of summary.assumptions)ul.append(this.prose(item,'li'));conditions.append(ul);box.append(conditions);}
    }
    renderTheorem(){const box=this.$('guided-theorem-preview');box.replaceChildren();const target=this.$('guided-theorem').value,d=theoremChoices(this.source).find(x=>x.name===target);if(d){this.renderSummary(box,window.MathPresentation?.sourceSummary(this.source,target));box.append(this.details('Точная формулировка Lean',d.type),this.details('Аксиомы и происхождение',{axioms:d.axioms||[],source_sha256:this.source.source_sha256,provenance:this.source.provenance}));}this.updateStart();}
    updateStart(){const b=this.$('guided-start');b.disabled=this.busy||this.state?.submitting||(!this.source&&!this.paper)||(this.source&&!theoremChoices(this.source).some(d=>d.name===this.$('guided-theorem').value));b.textContent=this.source?'Найти связи в трёх областях':'Найти переходы в статье';}
    limits(){return budget(this.$('guided-calls').value,this.$('guided-minutes').value);}
    async start(){if(this.busy)return;this.setBusy(true);try{const limits=this.limits(),question=this.$('guided-question').value;
      const payload=this.source?structurePayload(this.source,this.$('guided-theorem').value,limits,question):discoveryPayload(this.paper,this.$('guided-section').value,limits,question);
      if(this.source)this.cb.setSource(this.source,payload.target);await this.cb.start(payload);this.$('guided-current').scrollIntoView({behavior:'smooth',block:'start'});
    }catch(e){this.notice(e.message,'error');}finally{this.setBusy(false);}}
    async verify(graph,transition){if(this.busy)return;this.setBusy(true);try{await this.cb.verify(graph,transition,this.limits());this.$('guided-current').scrollIntoView({behavior:'smooth',block:'start'});}catch(e){this.cb.error(e.message);}finally{this.setBusy(false);}}
    async searchAnalogies(graph,transition){if(this.busy)return;this.setBusy(true);try{if(active.has(this.state?.run?.status))throw new Error('Дождитесь завершения текущего запуска или остановите его.');const payload=transitionSearchPayload(graph,transition,this.limits());await this.cb.start(payload);this.$('guided-current').scrollIntoView({behavior:'smooth',block:'start'});}catch(e){this.cb.error(e.message);}finally{this.setBusy(false);}}
    async retry(run){if(this.busy)return;this.setBusy(true);try{if(active.has(this.state?.run?.status))throw new Error('Дождитесь завершения текущего запуска или остановите его.');await this.cb.start(retryPayload(run));this.$('guided-current').scrollIntoView({behavior:'smooth',block:'start'});}catch(error){this.cb.error(error.message);}finally{this.setBusy(false);}}
    contractPanel(run){
      const preflight=contractPreflight(run);if(!preflight)return null;
      const box=this.el('section',{class:'guided-candidate','aria-label':'Постановка в Lean','data-contract-preflight':preflight.accepted?'accepted':'not_accepted'});box.append(this.el('h3',{},'Постановка в Lean'),this.el('p',{},preflight.title+'.'),this.prose('На этом этапе проверяются определения и корректность типа цели. Он не доказывает утверждение и не выдаёт сертификат доказательства.','p','guided-note'));
      if(!preflight.accepted){box.append(this.el('p',{},'Стадия: проверка постановки в Lean, до доказательства.'));if(preflight.issues.length){const ul=this.el('ul');for(const issue of preflight.issues)ul.append(this.el('li',{},issue));box.append(ul);}else box.append(this.el('p',{},preflight.diagnostic||'Причина указана в полном отчёте ниже.'));
        if(preflight.report.termination?.code==='invalid_contract')box.append(this.prose('Следующий шаг — исправить формальную постановку в новой версии или выбрать другую связь. Повтор с теми же определениями не исправляет ошибку записи.','p','guided-note'));
      }
      if(preflight.target)box.append(this.el('p',{},'Цель: '+preflight.target));
      if(preflight.definitions.length)box.append(this.el('p',{},'Определения: '+preflight.definitions.slice(0,6).join(', ')+(preflight.definitions.length>6?' и ещё '+(preflight.definitions.length-6):'')));
      if(preflight.statement)box.append(this.details('Точный тип цели',preflight.statement));if(preflight.prelude)box.append(this.details('Определения постановки',preflight.prelude));box.append(this.details('Диагностика Lean и полный отчёт проверки постановки',preflight.report));return box;
    }
    openRefinement(run){
      const context=refinementTarget(run);if(!context||this.refinement?.saving)return;this.closeRefinement();
      const dialog=this.el('dialog',{class:'research-materials',id:'guided-refinement','aria-labelledby':'guided-refinement-title'}),body=this.el('div',{class:'guided-research'}),heading=this.el('div',{class:'research-materials-heading'}),form=this.el('form'),message=this.el('p',{role:'alert','aria-live':'polite'}),fields={objects:[]},trigger=document.activeElement;
      const close=this.button('Отмена',()=>this.closeRefinement());heading.append(this.el('h2',{id:'guided-refinement-title'},'Уточнить постановку'),close);body.append(heading,this.prose('Сохраняется новая версия карты. Прежняя постановка и попытка останутся в истории. Уточняется только выбранный переход и его собственные объекты; источник статьи и остальные переходы сохраняются. Сертификат не переносится: после сохранения нужна отдельная проверка.'));
      if(run.result?.reason)body.append(this.prose(run.result.reason,'p','guided-note'));
      let index=0;const field=(parent,label,value,rows=4)=>{const id='guided-refine-field-'+(++index),input=this.el('textarea',{id,rows});input.value=Array.isArray(value)?value.join('\n'):String(value||'');parent.append(this.el('label',{for:id},label),input);return input;};
      form.append(this.el('h3',{},context.transition.title));for(const[key,label,rows]of [['title','Название перехода',2],['claim','Утверждение перехода',8],['assumptions','Условия перехода · по одному на строку',5],['construction','Преобразование',5]])fields[key]=field(form,label,context.transition[key],rows);
      for(const item of context.objects){const value=item.value;if(!item.editable){const shared=this.el('details',{class:'guided-details'});shared.append(this.el('summary',{},value.title+' · общий исходный контекст'),this.prose('Этот объект используется другими переходами и здесь доступен только для чтения.'),this.prose(value.definition));for(const line of [...array(value.parameters),...array(value.assumptions)])shared.append(this.prose(line));form.append(shared);continue;}const section=this.el('fieldset');section.append(this.el('legend',{},value.title));const inputs={id:value.id};for(const[key,label,rows]of [['title','Название объекта',2],['definition','Определение объекта',6],['parameters','Параметры · по одному на строку',4],['assumptions','Условия объекта · по одному на строку',4]])inputs[key]=field(section,label,value[key],rows);fields.objects.push(inputs);form.append(section);}
      const actions=this.el('div',{class:'guided-inline-actions'}),save=this.el('button',{type:'submit',class:'button primary'},'Сохранить новую версию');actions.append(save);form.append(message,actions);form.onsubmit=event=>{event.preventDefault();this.saveRefinement();};body.append(form);dialog.append(body);this.$('guided-research').append(dialog);this.refinement={dialog,graph:run.object_graph,transitionId:context.transition.id,fields,message,save,close,trigger,saving:false};dialog.oncancel=event=>{event.preventDefault();this.closeRefinement();};dialog.showModal();fields.title.focus();
    }
    closeRefinement(){const edit=this.refinement;if(!edit||edit.saving)return;this.refinement=null;edit.dialog.close();edit.dialog.remove();edit.trigger?.focus?.({preventScroll:true});}
    async saveRefinement(){
      const edit=this.refinement;if(!edit||edit.saving)return;
      try{const values={objects:edit.fields.objects.map(item=>({id:item.id,...Object.fromEntries(['title','definition','parameters','assumptions'].map(key=>[key,item[key].value]))}))};for(const key of ['title','claim','assumptions','construction'])values[key]=edit.fields[key].value;const draft=refinementDraft(edit.graph,edit.transitionId,values);edit.saving=true;edit.save.disabled=true;edit.close.disabled=true;edit.message.textContent='Сохраняем новую версию…';
        const response=await this.cb.api('/api/objects/graphs/'+encodeURIComponent(edit.graph.id)+'/revisions',{graph:draft,expected_revision:edit.graph.revision}),graph=response.graph||response;
        edit.saving=false;this.closeRefinement();this.cb.onRevision?.(graph,edit.transitionId);
      }catch(error){edit.message.textContent=error.message;}finally{edit.saving=false;edit.save.disabled=false;edit.close.disabled=false;}
    }
    async openRun(id){if(this.state?.run?.id===id){if(this.state.run.purpose){this.goStep(active.has(this.state.run.status)?defaultStep(this.state.run):'result');return;}const result=this.$('guided-result');(result.hidden?this.$('guided-current'):result).scrollIntoView({behavior:'smooth',block:'start'});return;}const loaded=await this.cb.load(id);if(loaded===false)throw new Error('Не удалось открыть сохранённое исследование.');this.$('guided-current').scrollIntoView({behavior:'smooth',block:'start'});}
    reset(){this.token++;this.busy=false;this.source=null;this.paper=null;this.runKey='';this.step=null;this.stepContext=null;this.$('guided-selection').hidden=true;this.$('guided-source-preview').replaceChildren();this.$('guided-theorem-preview').replaceChildren();this.notice('');this.setBusy(false);this.$('research-advanced').open=false;this.$('guided-setup').hidden=false;this.$('guided-setup').scrollIntoView({behavior:'smooth',block:'start'});this.ensureCatalog().catch(()=>{});}
    showMap(view='objects',selection){
      if(!this.map)return this.cb.details(view);
      if(this.state)this.goStep(view==='proof'?'lean':'connections',{scroll:false});
      this.map.setView(view);
      if(selection)this.map.select(selection);
      this.$('guided-map').scrollIntoView({behavior:'smooth',block:'start'});
    }
    render(state){
      this.state=state;const run=state.run,draft=state.draftGraph,context=run?'run:'+run.id:draft?'graph:'+draft.id+':'+draft.revision:'new';
      if(context!==this.stepContext){this.stepContext=context;this.step=selectedStep(run,draft,this.urlStep());}else this.step=selectedStep(run,draft,this.step);
      this.$('research-panel').classList.toggle('has-open-research',!!run||!!draft);this.$('guided-setup').hidden=!!run||!!draft;
      this.$('structure-results').hidden=run?.purpose!=='structure';const structureSlot=this.$('guided-structure-slot');structureSlot.hidden=run?.purpose!=='structure'||this.step!=='connections';if(this.structureRunId!==run?.id){this.structureRunId=run?.id;structureSlot.open=awaitingStructureMap(run);}this.updateStart();this.renderHistory(state.runs);this.renderSteps(run,draft);
      const key=JSON.stringify([this.step,run?.id,run?.status,run?.updated_at,draft?.id,draft?.revision,state.submitting,awaitingStructureMap(run),array(state.runs).map(r=>[r.id,r.status,r.updated_at])]);if(key===this.runKey)return;this.runKey=key;
      this.renderCurrent(run,draft);this.renderProgress(run);this.renderCandidates(run,draft);this.renderResult(run);this.renderSavedSource(run,draft);this.renderLeanStage(run);
      const graph=run?.object_graph||draft,checksReady=!!this.candidateChecks&&array(graph?.transitions).some(t=>mapModel()?.transitionRole(run||{object_graph:graph},t)==='bridge');
      const directions=this.$('guided-directions');directions.replaceChildren();directions.hidden=this.step!=='connections'||checksReady;
      if(!directions.hidden){directions.append(this.el('h2',{},'Направления и связи'),this.prose(run?.purpose==='prove'?'Карта, на которой выбрана проверяемая связь. Можно рассмотреть другие переходы, а затем вернуться к этой проверке через верхние этапы.':'Выберите переход на карте, чтобы исследовать его связи.','p','guided-note'));const codes=array((run?.object_graph||draft)?.msc_codes);if(codes.length)directions.append(this.prose('Области текущей карты · MSC '+codes.join(' · '),'p','guided-note'));}
      this.$('guided-checks').hidden=this.step!=='connections'||!checksReady;
      if(this.step==='connections'&&checksReady)this.candidateChecks.render(run,draft,state.runs);else this.candidateChecks?.suspend?.();
      this.$('guided-saved-source').hidden=this.step!=='source'||!run&&!draft;
      this.$('guided-lean').hidden=this.step!=='lean';
      this.$('guided-progress').hidden=!active.has(run?.status)||!['lean','connections'].includes(this.step);
      this.$('guided-result').hidden=this.step!=='result';
      this.$('guided-candidates').hidden=this.step!=='connections'||this.$('guided-candidates').hidden;
      const mapRun=awaitingStructureMap(run)?null:run||(draft?{purpose:'discover',object_graph:draft}:null);
      const proofAvailable=array(run?.nodes).length||array(run?.result?.nodes).length;
      this.$('guided-map').hidden=!mapRun||!(this.step==='connections'||this.step==='lean'&&proofAvailable);
      if(mapRun&&!this.$('guided-map').hidden)this.map?.render(mapRun,{runs:state.runs,view:this.step==='lean'?'proof':'objects',proofTransitionId:this.step==='lean'?run?.selected_transition_id:undefined});
    }
    renderCurrent(run,draft){const box=this.$('guided-current');box.hidden=!run&&!draft;box.replaceChildren();if(box.hidden)return;const v=verdict(run);box.append(this.el('p',{class:'eyebrow'},run?(isSearch(run)?'Направления и связи':'Выбранный переход'):'Сохранённая постановка'),this.el('h2',{},run?titleOf(run):draft.title));
      const sourceTitle=array(run?.paper_manifest).map(p=>p.title).filter(Boolean).join(' · ');if(sourceTitle)box.append(this.prose(sourceTitle,'p','guided-note'));
      if(run){const row=this.el('div',{class:'guided-run-meta'});row.append(this.el('span',{class:'guided-badge '+(v.kind==='proved'?'good':'')},v.title),this.el('span',{},isSearch(run)&&v.kind==='search'?v.count+' переходов на карте':versionCaption(run)));box.append(row);}
      const actions=this.el('div',{class:'guided-inline-actions'});if(run)actions.append(this.button('Журнал работы',()=>this.cb.details('attempts')));if(actions.children.length)box.append(actions);
    }
    renderProgress(run){const box=this.$('guided-progress');box.hidden=!run||!active.has(run.status);box.replaceChildren();if(box.hidden)return;const head=this.el('div',{class:'guided-progress-heading'});head.append(this.el('span',{class:'guided-spinner','aria-hidden':'true'}),this.el('h3',{},progressText(run)));box.append(head);
      const obligations=array(run.formal_contract?.required_obligations),nodes=array(run.nodes),done=obligations.filter(o=>nodes.some(n=>(n.id===o.target||n.target===o.target)&&['proved','verified'].includes(n.status))).length;if(obligations.length)box.append(this.prose('Проверено обязательств: '+done+' из '+obligations.length+'. Итог появится после полной сборки и смысловой проверки.'));
      const recent=array(run.events).slice(-1)[0];if(recent?.message)box.append(this.prose(recent.message,'p','guided-note'));const preflight=this.contractPanel(run);if(preflight)box.append(preflight);box.append(this.prose('Можно оставить эту страницу: запуск сохраняется на локальном сервере. Процент готовности заранее неизвестен.','p','guided-note'));
      const stop=this.button(run.status==='cancelling'?'Останавливаем…':'Остановить и сохранить',()=>this.cb.action('cancel'));stop.disabled=run.status==='cancelling';box.append(stop);
    }
    renderCandidates(run,draft){const box=this.$('guided-candidates'),graph=run?.object_graph||draft;box.replaceChildren();box.hidden=!!this.map||!(draft||run?.purpose==='discover')||!graph;if(box.hidden)return;box.append(this.el('h3',{},'Выберите исходный переход'));for(const t of array(graph.transitions)){const card=this.el('article',{class:'guided-candidate'}),role=mapModel()?.transitionRole(run||{object_graph:graph},t);const status=window.ObjectGraphModel.presentation(t);card.append(this.el('span',{class:'guided-badge '+(status.status==='proved'?'good':'')},status.label),this.el('h4',{},t.title),this.prose(t.claim||t.description||''));card.append(this.button(role==='article'?'Найти аналоги в других областях':role==='bridge'?'Проверить общую структуру в Lean':'Исследовать переход',()=>role==='article'?this.searchAnalogies(graph,t):this.verify(graph,t),true));box.append(card);}}
    renderResult(run){const box=this.$('guided-result');box.replaceChildren();box.hidden=!run||active.has(run.status);if(box.hidden)return;
      if(isSearch(run)){box.append(this.el('p',{class:'eyebrow'},'4 · Результат поиска'),this.el('h2',{},verdict(run).title),this.prose('На карте сохранено переходов: '+array(run.object_graph?.transitions).length+'. Найденные предложения проверяются в Lean отдельным запуском.'));if(run.error)box.append(this.prose(run.error));box.append(this.button('Открыть направления и связи',()=>this.goStep('connections')));return;}
      const v=verdict(run),proof=run.result?.verification,sem=finalReview(run),termination=terminationInfo(run),summary=window.MathPresentation?.runSummary(run),transition=array(run.object_graph?.transitions).find(t=>t.id===run.selected_transition_id);
      box.dataset.verdict=v.kind;box.append(this.el('p',{class:'eyebrow'},'Что получилось'),this.el('h2',{},v.title));
      const preflight=this.contractPanel(run),scopeReview=termination?.code==='needs_review'&&termination.stage==='formalize_transition'&&run.formalization_review?.status==='needs_review';if(preflight)box.append(preflight);
      if(scopeReview){const review=this.el('section',{class:'guided-candidate'});review.append(this.el('h3',{},'Почему остановилась проверка'),this.prose(run.formalization_review.reason||termination.message));if(!preflight&&!hasLeanEvidence(run))review.append(this.prose('До проверки Lean не дошли: точная постановка ещё не подготовлена. Доказательство не получено.','p','guided-note'));const limitations=array(run.formalization_review.limitations);if(limitations.length){const details=this.el('details',{class:'guided-details'});details.append(this.el('summary',{},'Что нужно уточнить для продолжения'));for(const line of limitations)details.append(this.prose(line));review.append(details);}box.append(review);}
      if(mapModel()?.sourceTransition(run))box.append(this.prose('Это проверка предложенной общей структуры. Её применимость к исходному переходу статьи отдельно не подтверждена.','p','guided-note'));
      if(summary)this.renderSummary(box,summary);else{
        if(v.kind==='proved')box.append(this.prose('Lean проверил точную формальную цель и все обязательства. Аудит аксиом пройден.'));
        if(transition?.claim||run.claim){const original=this.el('details',{class:'guided-details'});original.append(this.el('summary',{},'Исходная формулировка кандидата'),this.prose(transition?.claim||run.claim));box.append(original);}
      }
      if(!['proved','formal_only'].includes(v.kind)&&!scopeReview&&!(preflight&&termination?.stage==='lean_contract_preflight'))box.append(this.prose(termination?.explanation||run.error||run.result?.error||run.result?.reason||'Сохранены попытки и диагностика. Отсутствие доказательства в этом запуске не доказывает невозможность связи.'));
      if(v.kind==='formal_only'&&termination)box.append(this.prose(termination.title+'. '+termination.explanation));
      if(termination||run.error||run.result?.error||run.result?.reason)box.append(this.details('Диагностика завершения',{termination:run.termination||run.result?.termination||termination,error:run.error||run.result?.error,reason:run.result?.reason||run.formalization_review?.reason}));
      if(refinementTarget(run))box.append(this.button('Уточнить постановку',()=>this.openRefinement(run),true));
      const checks=array(proof?.obligations);if(checks.length){box.append(this.el('h3',{},'Обязательства доказательства'));const ul=this.el('ol',{class:'guided-obligations'});for(const item of checks){const row=this.el('li');const ok=item.ok===true||item.passed===true||item.success===true;row.append(this.el('span',{class:'guided-check '+(ok?'good':'')},ok?'✓':'○'),this.el('div',{},item.title||array(run.formal_contract?.required_obligations).find(o=>o.target===item.target)?.title||item.target||item.id));row.append(this.details('Точный тип Lean',item.expected_statement||item.statement||array(run.formal_contract?.required_obligations).find(o=>o.target===item.target)?.statement||item.actual_statement||item));ul.append(row);}box.append(ul);}
      if(run.contract_review){const d=this.el('details',{class:'guided-details'});d.append(this.el('summary',{},'Рецензия постановки до доказательства'),this.prose(run.contract_review.reason||run.contract_review.status));for(const line of array(run.contract_review.limitations))d.append(this.prose(line));box.append(d);}
      if(sem.status==='not_performed')box.append(this.prose(scopeReview?'Итоговая смысловая рецензия не проводилась: доказательство не получено.':sem.title,'p','guided-note'));else{const d=this.el('details',{class:'guided-details'});d.append(this.el('summary',{},'Итоговая смысловая рецензия и границы результата'),this.prose(sem.reason));for(const line of array(sem.limitations))d.append(this.prose(line));box.append(d);}
      if(summary?.limitations?.length)for(const line of summary.limitations)box.append(this.prose(line,'p','guided-note'));
      if(proof)box.append(this.prose('Lean проверяет точную формальную цель. Смысловая рецензия и оценка научной новизны — отдельные задачи.','p','guided-note'));
      const actions=this.el('div',{class:'guided-inline-actions'});if(array(run.object_graph?.transitions).some(t=>t.id!==run.selected_transition_id))actions.append(this.button('Выбрать другую связь',()=>this.goStep('connections'),true));actions.append(this.button('Доказательство и отчёт Lean',()=>this.cb.details('result')));const artifacts=array(run.artifacts),final=artifacts.find(a=>/composition[\\/].*Candidate\.lean$/.test(a.path||a));if(final){const path=String(final.path||final).replaceAll('\\','/');if(!path.startsWith('/')&&!path.split('/').includes('..'))actions.append(this.el('a',{class:'button secondary',href:'/api/research/runs/'+encodeURIComponent(run.id)+'/artifacts/'+path.split('/').map(encodeURIComponent).join('/'),target:'_blank',rel:'noopener noreferrer'},'Открыть Lean-файл'));}if(canRetry(run)){box.append(this.prose('Повторная проверка создаст новый запуск с той же версией постановки и прежним бюджетом: '+run.budget.max_calls+' вызовов / '+Math.round(run.budget.timeout_seconds/60)+' мин. Текущая попытка останется в истории.','p','guided-note'));actions.append(this.button('Повторить проверку',()=>this.retry(run),true));}box.append(actions);
    }
    renderHistory(runs){const items=array(runs);this.$('guided-history-count').textContent=items.length?'· '+items.length:'';this.history?.render(items,this.state?.run?.id||null);}
  }
  return {Workspace,stepNavigation,defaultStep,selectedStep,verdict,terminationInfo,hasLeanEvidence,contractPreflight,finalReview,formalEvidence,retryPayload,canRetry,titleOf,versionCaption,budget,matchExample,theoremChoices,sourceReady,structurePayload,transitionSearchPayload,sourceNavigation,refinementContext,refinementTarget,refinementDraft,discoveryPayload,progressText,awaitingStructureMap};
});
