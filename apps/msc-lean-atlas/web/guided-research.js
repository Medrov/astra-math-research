'use strict';

(function(root,factory){const api=factory();if(typeof module==='object'&&module.exports)module.exports=api;else root.GuidedResearch=api;})(typeof window==='undefined'?globalThis:window,()=>{
  const active=new Set(['queued','running','cancelling']);
  const finished=new Set(['complete','completed']);
  const array=v=>Array.isArray(v)?v:[];
  const showcases=[
    {
      id:'fibonacci_composition_bridge',title:'Фибоначчи → квадратичная форма',label:'Условный алгебраический мост',
      summary:'Как композиция нормы на ℚ² связывает два полиномиальных равенства.',
      saved:'Сохранённое доказательство · 4 обязательства',button:'Проверить 4 обязательства',
      source:'A Pair of Diophantine Equations Involving the Fibonacci Numbers · §2',url:'https://arxiv.org/html/2409.02933v1#S2',
      steps:[
        ['Источник и поиск','В сохранённом исследовании выбран переход quartic_step. Поиск аналогов привёл к композиции квадратичной формы; MSC 15A63 — предложенное соответствие, а не метаданные статьи.'],
        ['Объекты и переход','На парах рациональных чисел заданы μ((u,v),(s,t)) = (us − vt, ut + vs) и N(u,v) = u² + v². Закон N(μ(x,y)) = N(x)N(y) применяется к парам (b,a) и (b,c).'],
        ['Что доказано','Lean проверил структуру, подстановку, условный перенос и нормализацию. При c = a + b и (b² − ac)² = 1 получены (b² + a²)(b² + c²) = 1 + b²(a + c)² и 2b⁴ − b²a² + a²c² = 1 + b²c².'],
        ['Границы','Последовательность Фибоначчи и выполнение этих предпосылок для её членов отдельно не формализованы. Применение к статье и научная новизна не подтверждены.'],
      ],
      replay:'Кнопка заново проверит сохранённое доказательство против всех четырёх точных обязательств и выполнит аудит аксиом. Это повтор готового результата без Astra.'
    },
    {
      id:'arxiv_2610_38474_graph_subtraction',title:'Полиномиальный граф → ось',label:'Пример Ивана Дорофеева',
      summary:'Шаг §9.1 статьи Фролова–Дорофеева: два обратных преобразования выпрямляют полиномиальный граф.',
      saved:'Сохранённое доказательство · 3 равенства',button:'Проверить полиномиальный шаг',
      source:'Frolov–Dorofeev · On the motivic approach to the Abhyankar rectifiability problem and concrete rectifications · §9.1',url:'https://arxiv.org/html/2610.38474v1#S9.SS1',
      steps:[
        ['Источник и подготовка','Из статьи выделен заключительный шаг §9.1. Astra получила доказательство после ошибок Lean и пересмотра графа лемм, имея доступ к подготовленной постановке. Это не слепое переоткрытие.'],
        ['Объекты и переход','Для коммутативного кольца K с единицей и b,w ∈ K[t] преобразование S(x,y,z) = (y, x − b(y), z − w(y)) имеет обратное S⁻¹(T,X,Z) = (X + b(T), T, Z + w(T)).'],
        ['Что доказано','Обе композиции преобразований равны тождественной подстановке. Образ графа (b(t), t, w(t)) равен (t, 0, 0). Подготовленный источник содержит три теоремы: subtract_restore, restore_subtract и graph_to_axis. Для нового поиска предлагается первая из них.'],
        ['Границы','Проверен только заключительный полиномиальный шаг. Вся Lemma 9.1, полные выпрямления узлов и мотивная часть статьи сюда не входят.'],
      ],
      replay:'Кнопка заново скомпилирует подготовленный источник Arxiv261038474.lean и проверит его аксиомы. Историческое доказательство Astra сохранено отдельно в Proof.lean. Этот локальный повтор не воспроизводит прежний поиск; новый поиск по атласу запускается отдельно.'
    }
  ];
  const isSearch=r=>['structure','discover'].includes(r?.purpose);
  const stoppedSearch=new Set(['cancelled','budget_exhausted','failed','interrupted']);
  const partialSearchFinalizing=run=>run?.purpose==='structure'&&stoppedSearch.has(run.status)&&run.partial_search?.status==='unavailable'&&array(run.partial_search.issues).some(issue=>issue?.code==='active_run');
  const awaitingStructureMap=run=>run?.purpose==='structure'&&!array(run.object_graph?.objects).length&&!array(run.object_graph?.transitions).length;
  function partialSearchInfo(run){
    const partial=run?.partial_search;if(run?.purpose!=='structure'||!stoppedSearch.has(run.status)||run.ready_to_start||partialSearchFinalizing(run)||!partial||!['available','materialized','unavailable'].includes(partial.status))return null;
    const count=Number.isInteger(partial.candidate_count)&&partial.candidate_count>=0?partial.candidate_count:0,completed=new Set(array(partial.completed_route_ids)),pending=new Set(array(partial.pending_route_ids));
    return {status:partial.status,count,completed:completed.size,pending:pending.size,total:new Set([...completed,...pending]).size,snapshot:typeof partial.snapshot_sha256==='string'?partial.snapshot_sha256:'',issues:array(partial.issues)};
  }
  function searchCandidateCount(run){return run?.object_graph?array(run.object_graph.transitions).length:partialSearchInfo(run)?.count||0;}
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
    if(!run||active.has(run.status))return null;
    const outcome=run.outcome_summary;if(outcome?.title&&outcome.category&&!['proved','refuted','candidates_found','no_supported_candidates','pending'].includes(outcome.category))return {code:outcome.category,stage:outcome.stage||'',title:outcome.title,explanation:outcome.reason||'',technical_failure:outcome.technical_failure===true};
    if(isSearch(run)&&finished.has(run.status))return null;
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
    if(value.code==='invalid_contract'&&preflight?.accepted&&proofProgress(run).started)return {...value,title:'Проверка доказательства остановлена',explanation:'Постановка прошла проверку типов. Доказательные попытки выполнялись; остановка на последующей проверке не означает отклонение исходной постановки. '+(value.message||'')};
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
  function proofProgress(run){
    const value=run?.proof_progress,valid=n=>Number.isInteger(n)&&n>=0;
    if(value&&typeof value.started==='boolean')return {...value,obligations_total:valid(value.obligations_total)?value.obligations_total:null,proved:valid(value.proved)?value.proved:null,failed:valid(value.failed)?value.failed:null,pending:valid(value.pending)?value.pending:null};
    const obligations=array(run?.formal_contract?.required_obligations),nodes=array(run?.nodes),proved=obligations.filter(o=>nodes.some(n=>(n.id===o.target||n.target===o.target)&&['proved','verified'].includes(n.status))).length,failed=obligations.filter(o=>nodes.some(n=>(n.id===o.target||n.target===o.target)&&['failed','rejected'].includes(n.status))).length;
    const started=array(run?.attempts).some(a=>a.role==='prove')||array(run?.events).some(e=>/^(?:prove|prove_node|proof_attempt)$/.test(e.phase||''))||nodes.some(n=>['proved','verified','failed','proving'].includes(n.status));
    return {started,obligations_total:obligations.length||null,proved:obligations.length?proved:null,failed:obligations.length?failed:null,pending:obligations.length?Math.max(0,obligations.length-proved-failed):null,active_stage:run?.active_stage};
  }
  function verdict(run){
    if(!run)return {kind:'empty',title:'Выберите источник'};
    if(run.status==='draft'&&run.ready_to_start)return {kind:'draft',title:'Новая версия готова к запуску'};
    if(active.has(run.status))return {kind:'running',title:isSearch(run)?'Astra ищет связи':'Проверяем выбранную связь'};
    if(isSearch(run)&&finished.has(run.status))return {kind:'search',title:run.outcome_summary?.title||'Поиск завершён',count:searchCandidateCount(run)};
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
    return {purpose:'structure',search_scope:'atlas',mode:'multi',source_id:source.id,target,budget:limits,...(question.trim()?{question:question.trim()}:{})};
  }
  function transitionSearchPayload(graph,transition,limits,question=''){
    const selected=array(graph?.transitions).find(item=>item.id===transition?.id);
    if(!graph?.id||!Number.isInteger(graph.revision)||graph.revision<1||!selected)throw new Error('Откройте сохранённую версию карты и выберите исходный переход.');
    if(mapModel()?.transitionRole({object_graph:graph},selected)!=='article')throw new Error('Поиск аналогов запускается из исходного перехода статьи; кандидат общей структуры проверяется отдельно.');
    return {purpose:'structure',search_scope:'atlas',mode:'multi',graph_id:graph.id,graph_revision:graph.revision,transition_id:selected.id,budget:limits,...(question.trim()?{question:question.trim()}:{})};
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
    if(!run||run.purpose!=='prove'||['invalid_contract','needs_review'].includes(run.termination?.code||run.result?.termination?.code)||!['failed','cancelled','interrupted','budget_exhausted','timeout'].includes(run.status))throw new Error('Повторная проверка доступна для завершённой неудачной попытки.');
    const graph=run.object_graph,ref=run.graph_ref,transition=array(graph?.transitions).find(item=>item.id===run.selected_transition_id);
    if(!ref?.id||graph?.id!==ref.id||graph.revision!==ref.revision||!objectModel().formulation(transition).formalized)throw new Error('У попытки нет сохранённой точной Lean-постановки. Сначала уточните переход.');
    if(!['single','multi','pilot'].includes(run.mode)||!Number.isInteger(run.budget?.max_calls)||run.budget.max_calls<1||!Number.isFinite(run.budget?.timeout_seconds)||run.budget.timeout_seconds<=0)throw new Error('Режим или бюджет предыдущей попытки не сохранён.');
    const budget={max_calls:run.budget.max_calls,timeout_seconds:run.budget.timeout_seconds,...(run.budget.max_parallel!==undefined?{max_parallel:run.budget.max_parallel}:{})};
    return {...objectModel().verificationPayload(graph,transition,{mode:run.mode,budget,msc_codes:array(graph.msc_codes)}),...(run.proof_backend?{proof_backend:run.proof_backend}:{})};
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
    if(run?.purpose==='structure'&&(run.search_scope==='atlas'||run.contract?.search_scope==='atlas')&&!run.atlas_snapshot_sha256&&!run.atlas_summary?.snapshot_sha256)return 'Подготавливаем первичный обзор атласа';
    if(p==='library_context')return 'Подбор библиотечных лемм и импортов';
    if(/atlas_screen/.test(p))return 'Обзор кодов всего атласа';
    if(/atlas/.test(p))return 'Поиск источников и связей по очереди атласа';
    if(p==='lean_contract_preflight')return 'Lean проверяет определения и тип цели';
    if(/structure_profile/.test(p))return 'Определяем объекты, операции и общий механизм';
    if(/structure_search|route|direction/.test(p))return 'Ищем в обоснованных направлениях MSC';
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
  function defaultStep(run,draft){if(run?.status==='draft')return 'source';return !run?(draft?'connections':'source'):isSearch(run)?'connections':active.has(run.status)?'lean':'result';}
  function selectedStep(run,draft,requested){return stepNavigation(run,draft).some(s=>s.id===requested&&s.available)?requested:defaultStep(run,draft);}
  class Workspace{
    constructor(callbacks){
      this.cb=callbacks;this.backend='native';this.kind='arxiv';this.source=null;this.paper=null;this.catalog=null;this.busy=false;this.token=0;this.runKey='';this.historyKey='';this.state=null;this.step=null;this.stepContext=null;this.connectionView='list';
      this.workspace=window.ResearchWorkspaceView?new window.ResearchWorkspaceView.Workspace({document,onStep:id=>this.goStep(id),onOpenRun:id=>this.openRun(id).catch(error=>this.cb.error(error.message)),onDetails:tab=>this.cb.details(tab),onCancel:()=>this.cb.action('cancel'),onStart:()=>this.cb.action('resume')}):null;
      this.atlas=window.AtlasSearch&&this.$('guided-atlas')?new window.AtlasSearch.Workspace({container:this.$('guided-atlas'),document,api:this.cb.api,onContinue:(run,data)=>this.openAtlasContinuation(run,data),onOpenRun:id=>this.openRun(id).catch(error=>this.cb.error(error.message))}):null;
      this.$('guided-structure-slot').append(this.$('structure-results'));
      this.map=window.ResearchMap ? new window.ResearchMap.Workspace({container:this.$('guided-map'),onVerify:(graph,transition)=>this.verify(graph,transition),onSearchAnalogies:(graph,transition)=>this.searchAnalogies(graph,transition),onOpenRun:id=>this.openRun(id).catch(e=>this.cb.error(e.message)),onSelection:selection=>{if(selection.kind==='transition'){this.candidateChecks?.select?.(selection.value.id);this.sourcePanelKey='';if(this.state)this.renderSavedSource(this.state.run,this.state.draftGraph);}this.cb.mapSelection?.(selection);}}) : null;
      this.history=window.ResearchHistory ? new window.ResearchHistory.Workspace({container:this.$('guided-history'),onOpen:id=>this.openRun(id),onError:message=>this.cb.error(message)}) : null;
      this.candidateChecks=window.CandidateChecks?new window.CandidateChecks.Workspace({container:this.$('guided-checks'),api:this.cb.api,onSelect:(graph,t)=>this.showMap('objects','transition:'+t.id),onVerify:(graph,t)=>this.verify(graph,t),onOpenRun:id=>this.openRun(id),onError:message=>this.cb.error(message)}):null;
      this.$('guided-history-open').onclick=()=>this.history?.show();
      const backend=this.$('workspace-backend');if(backend){backend.onchange=()=>{this.backend=backend.value;const selected=this.backends?.find(item=>item.id===this.backend);this.$('workspace-backend-description').textContent=selected?.description||'';};this.ensureBackends();}
      const mechanisms=this.$('workspace-mechanisms');if(mechanisms)mechanisms.ontoggle=()=>{if(mechanisms.open)this.loadMechanisms();};
      this.$('guided-source-form').onsubmit=e=>{e.preventDefault();this.prepare();};
      this.$('guided-start').onclick=()=>this.start();
      this.$('guided-theorem').onchange=()=>this.renderTheorem();
      this.$('guided-section').onchange=()=>this.renderTheorem();
      for(const id of ['guided-file','guided-example'])this.$(id).onchange=()=>this.invalidateSource();
      this.$('guided-arxiv').oninput=()=>this.invalidateSource();
      for(const b of document.querySelectorAll('[data-guided-source]'))b.onclick=()=>this.setKind(b.dataset.guidedSource);
      for(const id of ['guided-calls','guided-minutes'])this.$(id).oninput=this.$(id).onchange=()=>this.renderBudgetSummary();
      this.renderBudgetSummary();
      this.renderShowcases();
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
      const key=JSON.stringify([run?.id,draft?.id,draft?.revision,origin,source,run?.paper_manifest,run?.source_card,run?.source_cards,this.map?.focus]);if(key===this.sourcePanelKey)return;this.sourcePanelKey=key;box.replaceChildren();
      box.append(this.el('p',{class:'eyebrow'},'1 · Источник'),this.el('h2',{},'Отправная точка исследования'),this.prose('Сохранённый источник этого запуска. Просмотр этапов не изменяет постановку и не запускает исследование повторно.','p','guided-note'));
      const sourceCard=this.workspace?.sourceCard(run?.source_card||array(run?.source_cards).find(item=>item.transition_id===this.map?.focus)||run?.contract?.source_card);if(sourceCard)box.append(sourceCard);
      const papers=array(run?.paper_manifest||run?.contract?.paper_manifest);
      for(const paper of papers){box.append(this.el('h3',{},paper.title||paper.versioned_id),this.el('span',{class:'guided-badge'},'arXiv '+paper.versioned_id));const link=paper.source_urls?.abstract;try{if(link&&['http:','https:'].includes(new URL(link).protocol)){const p=this.el('p');p.append(this.el('a',{href:link,target:'_blank',rel:'noopener noreferrer'},'Открыть сохранённую версию статьи ↗'));box.append(p);}}catch{} }
      if(origin){box.append(this.el('h3',{},origin.transition.title),this.prose(origin.transition.claim));if(origin.transition.construction)box.append(this.prose(origin.transition.construction));for(const condition of array(origin.transition.assumptions))box.append(this.prose(condition,'p','guided-note'));
        const objects=this.el('div',{class:'guided-source-objects'});for(const object of array(origin.objects)){const item=this.el('details');item.append(this.el('summary',{},object.title||object.id),this.prose(object.definition));objects.append(item);}box.append(objects);
      }else if(source){box.append(this.el('h3',{},source.title||source.name||'Исходная теорема Lean'));const declaration=source.selected_declaration;if(declaration)box.append(this.details(declaration.name,declaration.type));if(source.source_sha256)box.append(this.details('Зафиксированный исходник',source.content||source.source_sha256));
      }else if(!papers.length){box.append(this.el('h3',{},run?.title||graph?.title||'Исследовательский вопрос'),this.prose(run?.claim||run?.contract?.question||graph?.question||'Материалы доступны в источниках исследования.'));}
      if(run?.source_card?.editable&&run.status!=='draft'&&!active.has(run.status))box.append(this.button('Подготовить новую версию',()=>this.openRevision(run)));
      if(run?.source_lineage?.parent_run_id)box.append(this.button('Сравнить с предыдущей версией',()=>this.compareRevision(run)));
      if(run?.status==='draft'&&run.ready_to_start)box.append(this.prose('Карточка новой версии сохранена. Начните проверку отдельной кнопкой в блоке хода исследования.','p','guided-note'));
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
    setBusy(value,message=''){this.busy=value;for(const id of ['guided-load','guided-load-lean','guided-load-example','guided-theorem','guided-section','guided-file','guided-example','guided-arxiv'])this.$(id).disabled=value;for(const b of document.querySelectorAll('[data-guided-source]'))b.disabled=value;for(const b of this.showcaseButtons||[])b.disabled=value;if(message)this.notice(message,value?'running':'');this.updateStart();}
    renderShowcases(){
      const box=this.$('guided-showcases');if(!box)return;box.replaceChildren();this.showcaseButtons=[];
      const heading=this.el('div',{class:'guided-showcases-heading'});heading.append(this.el('h2',{id:'guided-showcases-title'},'Готовые разборы'),this.prose('Два сохранённых результата с объяснением шагов и границ. Раскройте разбор или повторите проверку Lean без вызовов модели.','p','guided-note'));box.append(heading);
      const cards=this.el('div',{class:'guided-showcase-grid'});
      for(const item of showcases){
        const card=this.el('article',{class:'guided-showcase-card','aria-labelledby':'showcase-'+item.id});
        card.append(this.el('p',{class:'eyebrow'},item.label),this.el('h3',{id:'showcase-'+item.id},item.title),this.prose(item.summary),this.el('p',{class:'guided-showcase-saved'},item.saved));
        const details=this.el('details',{class:'guided-showcase-details'});details.append(this.el('summary',{},'Как получен результат'));
        const source=this.el('p',{class:'guided-showcase-source'});source.append(this.el('a',{href:item.url,target:'_blank',rel:'noopener noreferrer'},item.source+' ↗'));details.append(source);
        for(const[title,text]of item.steps){const step=this.el('section');step.append(this.el('h4',{},title),this.prose(text));details.append(step);}details.append(this.prose(item.replay,'p','guided-note'));card.append(details);
        const status=this.el('p',{class:'guided-showcase-status',role:'status','aria-live':'polite'});status.hidden=true;
        const button=this.button(item.button,()=>this.openShowcase(item.id,status));this.showcaseButtons.push(button);card.append(button,status);cards.append(card);
      }
      box.append(cards);
    }
    async openShowcase(id,status){
      if(this.busy)return;const item=showcases.find(s=>s.id===id);if(!item)return;
      this.setKind('example');const token=++this.token;this.setBusy(true,'Готовим новый локальный повтор…');status.hidden=false;status.textContent='Проверяем сохранённый Lean-источник…';
      try{
        const catalog=await this.ensureCatalog();if(token!==this.token)return;const example=array(catalog.examples).find(e=>e.id===id);if(!example)throw new Error('Этот готовый пример недоступен в текущем каталоге.');
        this.$('guided-example').value=id;await this.prepareExample(example,token,{fresh:true});if(token!==this.token)return;
        const demo=this.source?.demo_verification,verified=example.verification_kind==='exact_demo_contract'?demo?.verified===true&&demo?.fresh_local_check===true:this.source?.inspection?.success===true&&this.source?.inspection?.audit?.status==='passed';
        status.textContent=verified?(demo?'Новый локальный повтор: 4/4 обязательства проверены.':'Новый локальный повтор: источник скомпилирован, аудит аксиом пройден.'):'Полная локальная проверка не подтверждена. Подробности — в результате над карточками.';
        const preview=this.$('guided-source-preview');preview.setAttribute('tabindex','-1');preview.scrollIntoView({behavior:'smooth',block:'start'});preview.focus({preventScroll:true});
      }catch(e){if(token===this.token){status.textContent='Проверка не завершена: '+e.message;this.notice(e.message,'error');}}
      finally{if(token===this.token)this.setBusy(false);}
    }
    invalidateSource(){if(this.busy)return;this.source=null;this.paper=null;this.token++;this.$('guided-selection').hidden=true;this.$('guided-source-preview').replaceChildren();this.$('guided-theorem-preview').replaceChildren();this.notice('');this.updateStart();}
    setKind(kind){if(this.busy)return;this.kind=kind;this.source=null;this.paper=null;this.token++;for(const b of document.querySelectorAll('[data-guided-source]'))b.setAttribute('aria-pressed',String(b.dataset.guidedSource===kind));for(const k of ['arxiv','lean','example'])this.$('guided-'+k+'-fields').hidden=k!==kind;this.$('guided-selection').hidden=true;this.$('guided-source-preview').replaceChildren();this.notice('');this.updateStart();this.ensureCatalog().catch(()=>{});}
    async ensureBackends(){
      const select=this.$('workspace-backend');if(!select)return;
      try{const result=await this.cb.api('/api/research/backends');this.backends=array(result.backends);select.replaceChildren();
        for(const backend of this.backends){const option=this.el('option',{value:backend.id},backend.title+(backend.available?'':' · недоступен'));option.disabled=!backend.available;select.append(option);}
        this.backend=this.backends.some(item=>item.id===this.backend&&item.available)?this.backend:result.default||'native';select.value=this.backend;select.onchange();
      }catch{this.$('workspace-backend-description').textContent='Список процессов проверки пока недоступен. Выбран стандартный процесс; доступность проверяется при запуске.';}
    }
    async loadMechanisms(){
      if(this.mechanismsLoaded||this.mechanismsLoading)return;this.mechanismsLoading=true;const box=this.$('workspace-mechanism-list');box.replaceChildren(this.prose('Загружаем библиотеку…','p','guided-note'));
      try{const response=await this.cb.api('/api/research/mechanisms');box.replaceChildren();for(const item of array(response.mechanisms)){
        const card=this.el('article',{class:'workspace-mechanism-card'});card.append(this.el('h3',{},item.title||item.id),this.el('p',{class:'guided-note'},item.status==='needs_recheck'?'Окружение изменилось · нужна перепроверка':'Проверен сохранённый контракт'),this.el('pre',{class:'workspace-mechanism-type'},item.formal_contract?.statement||item.description||''),this.button('Изучить механизм',()=>this.openMechanism(item.id)));box.append(card);}
        if(!box.children.length)box.append(this.prose('Проверенные механизмы пока не добавлены.','p','guided-note'));this.mechanismsLoaded=true;
      }catch(error){box.replaceChildren(this.prose('Не удалось открыть библиотеку: '+error.message),this.button('Повторить загрузку',()=>this.loadMechanisms()));}finally{this.mechanismsLoading=false;}
    }
    async openMechanism(id){
      const box=this.$('workspace-mechanism-detail'),token=this.mechanismToken=(this.mechanismToken||0)+1;box.replaceChildren(this.prose('Открываем описание…'));
      try{const response=await this.cb.api('/api/research/mechanisms/'+encodeURIComponent(id));if(token!==this.mechanismToken)return;
        const item=response.mechanism||response,contract=item.formal_contract||{},origin=item.provenance||{},review=item.semantic_review||{},verification=item.verification||{},library=item.source_library;
        const backend=origin.proof_backend||item.proof_backend,backendLabel=({'native':'SHAIM / native · Astra + Lean','goedel-adapted':'Goedel · адаптированный процесс'})[backend]||backend||'не сохранён';
        box.replaceChildren(this.el('h3',{},item.title||origin.title||id));
        box.append(this.el('p',{class:'guided-note'},item.status==='needs_recheck'?'Окружение изменилось. Сохранённая проверка требует повторения.':'Сохранённый контракт проверен; это не сертификат нового применения.'),this.el('p',{},'Процесс доказательства: '+backendLabel));
        box.append(this.el('h4',{},'Точный формальный контракт'),this.el('p',{},'Цель: '+(contract.target||'не сохранена')),this.el('pre',{class:'workspace-mechanism-type'},contract.statement||'Точный тип не сохранён.'));
        box.append(this.details('Импорты и определения',array(contract.imports).map(name=>'import '+name).join('\n')+'\n\n'+(contract.prelude||'')));
        box.append(this.el('h4',{},'Все обязательства · '+array(contract.required_obligations).length));
        for(const obligation of array(contract.required_obligations)){const section=this.el('section',{class:'workspace-mechanism-obligation'}),checked=array(verification.obligations).find(value=>value.id===obligation.id&&value.target===obligation.target);
          section.append(this.el('h5',{},obligation.title||obligation.id||obligation.target),this.el('p',{},'Цель: '+(obligation.target||'не сохранена')+' · ожидаемый исход: '+(obligation.expected_outcome||'не сохранён')),this.el('pre',{class:'workspace-mechanism-type'},obligation.statement||'Тип не сохранён.'),this.el('p',{class:'guided-note'},checked?.ok===true?'Подтверждено в сохранённом отчёте Lean.':'Нет подтверждения этого обязательства в отчёте.'));box.append(section);}
        box.append(this.el('h4',{},'Условия применения'));
        if(array(origin.assumptions).length){const ul=this.el('ul');for(const value of origin.assumptions)ul.append(this.prose(value,'li'));box.append(ul);}else box.append(this.el('p',{class:'guided-note'},'Отдельные условия в карточке не перечислены. Предпосылки и кванторы сохранены в точных типах выше.'));
        box.append(this.el('h4',{},'Происхождение и источники'));
        if(origin.claim)box.append(this.el('h5',{},'Исходная формулировка до проверки'),this.prose(origin.claim));if(origin.run_id)box.append(this.button('Открыть исходное исследование',()=>this.openRun(origin.run_id)));
        for(const source of array(origin.sources)){const row=this.el('section',{class:'workspace-mechanism-source'});row.append(this.el('p',{},source.title||source.source||source.id||'Источник'));if(source.locator)row.append(this.el('p',{class:'guided-note'},source.locator));
          try{if(source.url&&['http:','https:'].includes(new URL(source.url).protocol))row.append(this.el('a',{href:source.url,target:'_blank',rel:'noopener noreferrer'},'Открыть источник ↗'));}catch{}box.append(row);}
        box.append(this.details('Происхождение, версии и хеши',origin));
        if(library)box.append(this.details('Закреплённый Lean-источник',library.content||library.source||library));
        box.append(this.details('Полный Lean-исходник доказательства',item.proof_source||'Исходник не сохранён.'));
        box.append(this.el('h4',{},'Смысловая рецензия'),this.el('p',{},'Статус: '+(review.status||'не сохранён')),this.prose(review.reason||review.summary||'Заключение не сохранено.'));
        for(const limitation of array(review.limitations))box.append(this.prose(limitation,'p','guided-note'));
        box.append(this.el('p',{class:'guided-note'},'Смысловая рецензия — отдельная оценка соответствия; она не удостоверяет научную новизну.'),this.details('Отчёт независимой проверки Lean',verification));
        const application=({source_usage_checked:'Использование закреплённого Lean-источника проверено.',formal_statement_only:'Подтверждена только самостоятельная формальная постановка.',not_verified:'Применимость к исходной статье не подтверждена.'})[item.source_application_status]||'Применимость к исходному материалу не установлена.';
        box.append(this.el('h4',{},'Границы повторного использования'),this.el('p',{},'Область проверки: '+(item.verification_scope||'не сохранена')+'. '+application),this.el('p',{class:'guided-note'},'Применение этого механизма к новой задаче требует отдельной постановки и нового доказательства. Сохранённые условия нельзя переносить автоматически.'));
        box.append(this.details('Окружение и контрольные хеши',{environment_fingerprint:item.environment_fingerprint,proof_sha256:item.proof_sha256,contract_sha256:item.contract_sha256,verification_sha256:item.verification_sha256}));
        box.tabIndex=-1;box.focus({preventScroll:true});box.scrollIntoView({behavior:'smooth',block:'nearest'});
      }catch(error){if(token===this.mechanismToken)box.replaceChildren(this.prose(error.message));}
    }
    async compareRevision(run){
      const parent=run?.source_lineage?.parent_run_id;if(!parent)return;
      const opener=document.activeElement,dialog=this.el('dialog',{class:'workspace-revision-dialog','aria-labelledby':'workspace-comparison-title'}),box=this.el('div',{class:'workspace-revision-form'}),status=this.prose('Загружаем предыдущую карточку…');
      box.append(this.el('h2',{id:'workspace-comparison-title'},'Изменения постановки'),status,this.button('Закрыть',()=>dialog.close()));dialog.append(box);document.body.append(dialog);dialog.onclose=()=>{dialog.remove();opener?.focus?.({preventScroll:true});};dialog.showModal();
      try{const response=await this.cb.api('/api/research/runs/'+encodeURIComponent(parent)),previous=response.run||response;if(!dialog.open)return;
        const changes=window.ResearchWorkspaceView.compareCards(previous.source_card,run.source_card);status.textContent=changes.length?'Изменённые поля сохранённых карточек. Эквивалентность формулировок этим сравнением не устанавливается.':'Поля карточек совпадают. Техническая формализация и её проверка выполняются отдельно.';
        for(const change of changes){const row=this.el('section',{class:'workspace-version-diff'});row.append(this.el('h3',{},change.label),this.details('Предыдущая версия',change.before),this.details('Эта версия',change.after));box.append(row);}
        if(run.source_lineage.reason)box.append(this.prose('Причина новой версии: '+run.source_lineage.reason));
      }catch(error){status.textContent='Не удалось загрузить предыдущую версию: '+error.message;}
    }
    openAtlasContinuation(run,data){
      if(this.continueDialog||active.has(run?.status)||run?.status==='draft'||!data?.snapshot_sha256)return;
      this.continuationRequests??=new Map();const requestId=run.id+':'+data.snapshot_sha256,request=this.continuationRequests.get(requestId)||{key:globalThis.crypto?.randomUUID?.()||'atlas-'+Date.now().toString(36)+'-'+Math.random().toString(36).slice(2)};this.continuationRequests.set(requestId,request);
      const opener=document.activeElement,dialog=this.el('dialog',{class:'workspace-revision-dialog','aria-labelledby':'atlas-continue-title'}),form=this.el('form',{class:'workspace-revision-form'});
      form.append(this.el('h2',{id:'atlas-continue-title'},'Продолжить поиск по атласу'),this.prose('Сохранённая попытка останется неизменной. Будет создан новый черновик с очередью продолжения; запустите его отдельно после просмотра.'));
      const fields=this.el('div',{class:'atlas-continuation-budget'}),field=(caption,id,min,max,value)=>{const label=this.el('label',{for:id},caption),input=this.el('input',{id,type:'number',min,max,required:'required'});input.value=String(value);label.append(input);fields.append(label);return input;};
      const calls=field('Лимит вызовов','atlas-continue-calls',1,24,Math.min(24,Math.max(1,run.budget?.max_calls||8))),minutes=field('Лимит времени, минут','atlas-continue-minutes',1,30,Math.min(30,Math.max(1,Math.ceil((run.budget?.timeout_seconds||600)/60))));form.append(fields);
      const summary=data.summary||run.atlas_summary||{},hasPending=summary.local_queries_complete!==true||summary.deep_pending!==0,hasFailed=summary.deep_failed>0,retry=this.el('input',{type:'checkbox'});retry.checked=false;if(hasFailed){const label=this.el('label',{class:'workspace-preserve-option'});label.append(retry,this.el('span',{},'Повторить направления с технической ошибкой'));form.append(label,this.prose('Повтор ошибочных направлений требует отдельного выбора и расходует новый бюджет.','p','guided-note'));}
      const status=this.el('p',{role:'status'}),actions=this.el('div',{class:'guided-inline-actions'}),save=this.el('button',{type:'submit',class:'button primary'},'Сохранить черновик продолжения'),close=this.button('Отмена',()=>dialog.close());actions.append(save,close);form.append(status,actions);dialog.append(form);document.body.append(dialog);this.continueDialog=dialog;
      let saving=false;save.disabled=!hasPending&&!request.body;retry.onchange=()=>{save.disabled=!hasPending&&!retry.checked;};if(request.body){calls.value=String(request.body.budget.max_calls);minutes.value=String(request.body.budget.timeout_seconds/60);retry.checked=request.body.retry_failed===true;calls.disabled=minutes.disabled=retry.disabled=true;status.textContent='Повторяем сохранённый запрос с тем же бюджетом и ключом.';}
      dialog.oncancel=event=>{if(saving)event.preventDefault();};dialog.onclose=()=>{this.continueDialog=null;dialog.remove();opener?.focus?.({preventScroll:true});};
      form.onsubmit=async event=>{event.preventDefault();if(saving||!request.body&&!hasPending&&!(hasFailed&&retry.checked))return;try{if(!request.body){const limits=budget(calls.value,minutes.value);request.body={budget:{max_calls:limits.max_calls,timeout_seconds:limits.timeout_seconds},idempotency_key:request.key,expected_snapshot_sha256:data.snapshot_sha256,...(hasFailed&&retry.checked?{retry_failed:true}:{})};}saving=true;save.disabled=close.disabled=calls.disabled=minutes.disabled=retry.disabled=true;status.textContent='Сохраняем черновик…';const response=await this.cb.api('/api/research/runs/'+encodeURIComponent(run.id)+'/atlas-continue',request.body),created=response.run||response;if(!created.id||created.status!=='draft')throw new Error('Сервис не вернул ожидаемый черновик продолжения.');this.continuationRequests.delete(requestId);saving=false;dialog.close();if(!this.state?.run||this.state.run.id===run.id)await this.openRun(created.id);}catch(error){status.textContent=error.message;}finally{saving=false;save.disabled=close.disabled=false;}};
      dialog.showModal();calls.focus();
    }
    openRevision(run){
      if(this.revisionDialog||active.has(run?.status)||!run?.source_card?.editable)return;
      const opener=document.activeElement,dialog=this.el('dialog',{class:'workspace-revision-dialog','aria-labelledby':'workspace-revision-title'}),form=this.el('form',{class:'workspace-revision-form'});
      form.append(this.el('h2',{id:'workspace-revision-title'},'Новая версия исследования'),this.prose('Исходная попытка останется в истории. После сохранения вы увидите карточку новой версии и сможете отдельно запустить проверку.'));
      const field=(label,value,rows=3)=>{const l=this.el('label',{},label),input=this.el('textarea',{rows});input.value=value||'';l.append(input);form.append(l);return input;};
      const reason=field('Что нужно исправить и почему','');reason.required=true;
      const options=run.revision_options||{},preserveLabel=this.el('label',{class:'workspace-preserve-option'}),preserve=this.el('input',{type:'checkbox'}),preserveNote=this.el('p',{class:'guided-note'});preserve.checked=options.can_preserve_formalization===true&&options.default_preserve_formalization===true;preserve.disabled=options.can_preserve_formalization!==true;preserveLabel.append(preserve,this.el('span',{},'Сохранить принятую постановку'));form.append(preserveLabel,preserveNote);let preservePreference=preserve.checked;preserve.onchange=()=>{preservePreference=preserve.checked;};
      const backendLabel=this.el('label',{for:'workspace-revision-backend'},'Процесс доказательства'),backend=this.el('select',{id:'workspace-revision-backend','aria-describedby':'workspace-revision-backend-description'}),backendDescription=this.el('p',{id:'workspace-revision-backend-description',class:'guided-note'},'Загружаем доступные процессы…');backend.disabled=true;form.append(backendLabel,backend,backendDescription);
      const details=this.el('details',{class:'guided-details'});details.append(this.el('summary',{},'Уточнить математическую постановку · необязательно'));
      const titleLabel=this.el('label',{},'Название'),title=this.el('input',{type:'text'});title.value=run.source_card.title||titleOf(run);titleLabel.append(title);
      const claimLabel=this.el('label',{},'Утверждение'),claim=this.el('textarea',{rows:4});claim.value=run.source_card.conclusion||run.claim||'';claimLabel.append(claim);
      const assumptionsLabel=this.el('label',{},'Условия · каждое с новой строки'),assumptions=this.el('textarea',{rows:4});assumptions.value=array(run.source_card.assumptions).join('\n');assumptionsLabel.append(assumptions);
      details.append(titleLabel,claimLabel,assumptionsLabel);form.append(details);
      const mathematicalEdits=()=>claim.value.trim()!==(run.source_card.conclusion||run.claim||'')||JSON.stringify(assumptions.value.split('\n').map(v=>v.trim()).filter(Boolean))!==JSON.stringify(array(run.source_card.assumptions));
      const syncPreserve=()=>{const changed=mathematicalEdits();preserve.disabled=changed||options.can_preserve_formalization!==true;preserve.checked=!preserve.disabled&&preservePreference;preserveNote.textContent=changed?'Изменены утверждение или условия: потребуется новая формализация.':options.reason||'Принятая постановка для этой попытки не подтверждена сервером; новая версия пройдёт формализацию.';};claim.oninput=assumptions.oninput=syncPreserve;syncPreserve();
      const status=this.el('p',{class:'workspace-revision-status',role:'status'}),actions=this.el('div',{class:'guided-inline-actions'}),save=this.el('button',{type:'submit',class:'button primary'},'Сохранить новую версию'),close=this.button('Отмена',()=>dialog.close());actions.append(save,close);form.append(status,actions);dialog.append(form);document.body.append(dialog);this.revisionDialog=dialog;
      let saving=false;save.disabled=true;dialog.oncancel=event=>{if(saving)event.preventDefault();};dialog.onclose=()=>{this.revisionDialog=null;dialog.remove();opener?.focus?.({preventScroll:true});};
      const fillBackends=items=>{backend.replaceChildren();for(const item of items){const option=this.el('option',{value:item.id},item.title+(item.available?'':' · недоступен'));option.disabled=!item.available;backend.append(option);}
        const preferred=run.proof_backend||'native',selected=items.find(item=>item.id===preferred&&item.available)||items.find(item=>item.available);backend.value=selected?.id||'';backend.disabled=!selected;save.disabled=!selected;
        backend.onchange=()=>{backendDescription.textContent=items.find(item=>item.id===backend.value)?.description||'Нет доступного процесса доказательства.';};backend.onchange();};
      if(this.backends?.length)fillBackends(this.backends);else this.cb.api('/api/research/backends').then(response=>{this.backends=array(response.backends);fillBackends(this.backends);}).catch(()=>{backendDescription.textContent='Не удалось получить доступные процессы. Закройте диалог и повторите загрузку.';});
      form.onsubmit=async event=>{event.preventDefault();if(saving||!reason.value.trim()||backend.disabled||!backend.value)return;saving=true;save.disabled=close.disabled=backend.disabled=true;status.textContent='Сохраняем новую версию…';
        try{const payload={reason:reason.value.trim(),proof_backend:backend.value,preserve_formalization:options.can_preserve_formalization===true&&preserve.checked&&!mathematicalEdits()};const corrections={};
          if(title.value.trim()!==(run.source_card.title||titleOf(run)))corrections.title=title.value.trim();
          if(claim.value.trim()!==(run.source_card.conclusion||run.claim||''))corrections.claim=claim.value.trim();
          const values=assumptions.value.split('\n').map(value=>value.trim()).filter(Boolean);if(JSON.stringify(values)!==JSON.stringify(array(run.source_card.assumptions)))corrections.assumptions=values;
          if(Object.keys(corrections).length)payload.corrections=corrections;
          const response=await this.cb.api('/api/research/runs/'+encodeURIComponent(run.id)+'/revise',payload);if(!response.run?.id)throw new Error('Сервис не вернул сохранённую версию.');
          saving=false;dialog.close();await this.openRun(response.run.id);
        }catch(error){status.textContent=error.message;}finally{saving=false;save.disabled=close.disabled=backend.disabled=false;}
      };dialog.showModal();reason.focus();
    }
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
    async prepareExample(example,token,{fresh=false}={}){
      const exactDemo=example.verification_kind==='exact_demo_contract';
      this.notice(exactDemo?'Lean заново проверяет четыре обязательства готовой демонстрации. Вызовов модели нет…':fresh?'Lean заново компилирует подготовленный источник и проверяет аксиомы. Вызовов модели нет…':'Открываем подготовленную формализацию и проверяем её доступность…','running');
      const saved=!fresh&&!exactDemo&&array(this.catalog?.sources).find(s=>s.status==='ready'&&s.source_sha256===example.source_sha256);
      const data= saved ? await this.cb.api('/api/structure/sources/'+encodeURIComponent(saved.id)) : await this.cb.api('/api/structure/sources',{example_id:example.id});
      if(token!==this.token)return;this.acceptSource(data.source,example.recommended_target,example.scope_note);
      if(fresh&&!exactDemo){const panel=this.el('section',{class:'guided-demo-verification','aria-label':'Новая локальная проверка источника'});panel.append(this.el('h4',{},'Новая локальная проверка источника'),this.prose('Подготовленный источник Arxiv261038474.lean скомпилирован заново. Это проверка исходной теоремы, а не повтор исторического поиска или сертификат всей статьи.'),this.details('Отчёт компиляции и аудита аксиом',data.source.inspection));this.$('guided-source-preview').append(panel);}
    }
    async usePrepared(example){if(this.busy)return;const token=++this.token;this.setBusy(true);try{await this.prepareExample(example,token);}catch(e){if(token===this.token)this.notice(e.message,'error');}finally{if(token===this.token)this.setBusy(false);}}
    renderPaperMSC(paper){
      const box=this.el('section',{class:'guided-source-msc','aria-label':'MSC статьи'}),codes=[...new Set(array(paper.msc_codes).filter(code=>typeof code==='string'&&code.trim()).map(code=>code.trim()))];
      const reported=paper.msc_status==='source_reported'&&codes.length>0,notFound=paper.msc_status==='not_found_in_retained_html'&&!codes.length;
      box.dataset.mscStatus=reported?'source_reported':notFound?'not_found_in_retained_html':'unknown';
      box.append(this.el('p',{class:'guided-note'},reported?'MSC статьи: '+codes.join(', '):notFound?'MSC не найдены в сохранённом HTML':'MSC источника пока не определены'));
      if(reported)box.append(this.el('p',{class:'guided-note'},'Рубрики указаны в источнике. Направления исследования уточняются отдельно.'));
      const evidence=array(paper.msc_evidence);
      if(evidence.length){const details=this.el('details',{class:'guided-details'});details.append(this.el('summary',{},'Подтверждение MSC в источнике'));
        const technical=this.el('details',{class:'guided-details'});technical.append(this.el('summary',{},'Технические сведения об извлечении'));
        for(const item of evidence){if(!item||typeof item!=='object')continue;const row=this.el('section');
          if(array(item.codes).length)row.append(this.el('p',{},'MSC: '+item.codes.join(', ')));
          if(item.source_document)row.append(this.el('p',{},'Документ: '+({article_html:'HTML статьи',abstract_html:'Страница статьи arXiv'}[item.source_document]||item.source_document)));
          if(item.locator)row.append(this.el('p',{},'Фрагмент: '+item.locator));
          if(item.quote)row.append(this.el('blockquote',{},item.quote));
          if(item.source_sha256)technical.append(this.el('p',{},String(item.source_document||'Источник')+' · SHA-256: '+item.source_sha256));
          details.append(row);
        }
        if(paper.msc_extraction_version!==undefined&&paper.msc_extraction_version!==null)technical.append(this.el('p',{},'Версия извлечения: '+paper.msc_extraction_version));
        if(technical.children.length>1)details.append(technical);
        box.append(details);
      }
      return box;
    }
    readySource(label,title,checked=false){
      const box=this.el('section',{class:'guided-ready-source','aria-label':'Подготовленный источник'}),heading=this.el('div',{class:'guided-ready-heading'});
      heading.append(this.el('span',{class:'guided-badge'+(checked?' good':'')},label),this.el('h3',{},title));box.append(heading);this.$('guided-source-preview').replaceChildren(box);return box;
    }
    renderPaper(example){
      const p=this.paper,box=this.readySource('arXiv '+p.versioned_id,p.title);if(array(p.authors).length)box.append(this.prose(p.authors.join(' · '),'p','guided-ready-meta guided-note'));
      box.append(this.renderPaperMSC(p));
      if(example){const card=this.el('div',{class:'guided-prepared'});card.append(this.el('strong',{},'Для этой статьи есть проверенная отправная точка'),this.prose(example.scope_note||'Подготовленная формализация отдельного шага статьи.'),this.button('Использовать проверенную теорему',()=>this.usePrepared(example),true));box.append(card);}
      const note=example?'Можно использовать подготовленный Lean-шаг выше или сначала выделить другие переходы из статьи.':'Сначала Astra выделит переходы статьи. Затем выберите переход, найдите аналоги в других областях MSC и проверьте выбранную общую структуру в Lean.';
      box.append(this.prose(note,'p','guided-note'));
      const sel=this.$('guided-section');sel.replaceChildren(this.el('option',{value:''},'Вся доступная статья'));for(const s of array(p.sections).filter(s=>s.id!=='document'))sel.append(this.el('option',{value:s.id},s.title||s.heading||s.id));
      this.$('guided-selection').hidden=false;this.$('guided-theorem-field').hidden=true;this.$('guided-section-field').hidden=false;this.$('guided-theorem-preview').replaceChildren();this.notice('Источник сохранён. Следующий запуск будет искать проверяемые переходы.','ready');this.updateStart();
    }
    acceptSource(source,recommended='',scope=''){
      if(!sourceReady(source))throw new Error(source?.inspection?.error||'Исходник не прошёл Lean. Поиск по нему пока недоступен.');this.source=source;
      const box=this.readySource('Lean-источник проверен',source.title||source.name,true);if(scope)box.append(this.prose(scope,'p','guided-ready-scope'));
      if(source.demo_verification)this.renderDemoVerification(box,source.demo_verification);
      box.append(this.prose('Astra сама выберет направления MSC по структуре выбранной теоремы.','p','guided-ready-meta guided-note'));
      const choices=theoremChoices(source),picker=this.$('guided-theorem');picker.replaceChildren(this.el('option',{value:''},'Выберите исходную теорему…'));for(const d of choices)picker.append(this.el('option',{value:d.name},(window.MathPresentation?.sourceSummary(source,d.name)?.title||d.name.split('.').pop())+(d.name===recommended?' · рекомендуемая отправная точка':'')));
      if(choices.some(d=>d.name===recommended))picker.value=recommended;else if(choices.length===1)picker.value=choices[0].name;
      this.$('guided-selection').hidden=false;this.$('guided-theorem-field').hidden=false;this.$('guided-section-field').hidden=true;this.notice(choices.length?'Источник готов. Выберите теорему и начните поиск.':'Файл проверен, но исходных теорем для поиска не найдено.',choices.length?'ready':'error');this.renderTheorem();
    }
    renderDemoVerification(box,demo){
      const checked=demo.verified===true&&demo.fresh_local_check===true,section=this.el('section',{class:'guided-demo-verification','aria-label':'Проверка готовой демонстрации'});
      section.append(this.el('h4',{},'Условный мост композиции нормы'),this.el('p',{class:'guided-badge '+(checked?'good':'')},checked?'Локальная проверка: 4/4 обязательства':'Полная проверка демонстрации не подтверждена'),this.prose('Готовое доказательство проверяется повторно, без модели. Это не новое открытие.','p','guided-note'));
      section.append(this.prose('Применение к исходной статье отдельно не проверено.','p','guided-ready-scope'),this.prose('MSC 15A63 — содержательное предположение, не метаданные статьи.','p','guided-ready-scope'));
      const goals=array(demo.formal_contract?.required_obligations);if(goals.length){const details=this.el('details',{class:'guided-details guided-demo-obligations'}),list=this.el('ol',{class:'guided-obligations'});details.append(this.el('summary',{},'Обязательства демонстрации · '+goals.length));for(const goal of goals){const row=this.el('li');row.append(this.el('span',{class:'guided-check '+(checked?'good':'')},checked?'✓':'○'),this.el('span',{},goal.title||goal.target),this.details('Точный тип Lean',goal.statement||''));list.append(row);}details.append(list);section.append(details);}
      section.append(this.details('Результат локальной проверки',{...demo.verification,source_application_status:demo.source_application_status,msc:demo.msc,fresh_local_check:demo.fresh_local_check,model_calls:demo.model_calls}));box.append(section);
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
    updateStart(){const b=this.$('guided-start');b.disabled=this.busy||this.state?.submitting||(!this.source&&!this.paper)||(this.source&&!theoremChoices(this.source).some(d=>d.name===this.$('guided-theorem').value));b.textContent=this.source?'Искать по всему атласу':'Найти переходы в статье';this.renderBudgetSummary();}
    renderBudgetSummary(){
      const summary=this.$('guided-budget-summary');if(!summary)return;
      try{const limits=this.limits(),minutes=Math.floor(limits.timeout_seconds/60),seconds=limits.timeout_seconds%60;summary.textContent='Лимит каждого запуска: до '+limits.max_calls+' вызовов Astra · до '+minutes+' мин'+(seconds?' '+seconds+' с':'')+'. Поиск и проверка связи запускаются отдельно.';summary.dataset.state='ready';}
      catch(error){summary.textContent=error.message;summary.dataset.state='error';}
    }
    limits(){return budget(this.$('guided-calls').value,this.$('guided-minutes').value);}
    async start(){if(this.busy)return;this.setBusy(true);try{const limits=this.limits(),question=this.$('guided-question').value;
      const payload=this.source?structurePayload(this.source,this.$('guided-theorem').value,limits,question):discoveryPayload(this.paper,this.$('guided-section').value,limits,question);
      payload.proof_backend=this.backend;if(this.source)this.cb.setSource(this.source,payload.target);await this.cb.start(payload);this.$('guided-current').scrollIntoView({behavior:'smooth',block:'start'});
    }catch(e){this.notice(e.message,'error');}finally{this.setBusy(false);}}
    async verify(graph,transition){if(this.busy)return;this.setBusy(true);try{await this.cb.verify(graph,transition,this.limits(),this.backend);this.$('guided-current').scrollIntoView({behavior:'smooth',block:'start'});}catch(e){this.cb.error(e.message);}finally{this.setBusy(false);}}
    async searchAnalogies(graph,transition,limits={max_calls:8,timeout_seconds:600}){
      if(this.busy||this.searchDialog)return;
      let base;try{if(active.has(this.state?.run?.status))throw new Error('Дождитесь завершения текущего запуска или остановите его.');base=transitionSearchPayload(graph,transition,limits);}catch(error){this.cb.error(error.message);return;}
      const opener=document.activeElement,dialog=this.el('dialog',{class:'workspace-revision-dialog','aria-labelledby':'atlas-search-title'}),form=this.el('form',{class:'workspace-revision-form'});
      form.append(this.el('h2',{id:'atlas-search-title'},'Поиск по всему атласу'),this.prose(transition.title+' · версия карты '+graph.revision),this.prose('Обзор всех кодов MSC и углублённый поиск используют общий ограниченный бюджет. Проверка найденной связи в Lean запускается отдельно.'));
      const fields=this.el('div',{class:'atlas-continuation-budget'}),field=(caption,id,max,value)=>{const label=this.el('label',{for:id},caption),input=this.el('input',{id,type:'number',min:1,max,required:'required'});input.value=String(value);label.append(input);fields.append(label);return input;};
      const calls=field('Лимит вызовов Astra','atlas-search-calls',24,limits.max_calls),minutes=field('Лимит времени, минут','atlas-search-minutes',30,limits.timeout_seconds/60);form.append(fields);
      const status=this.el('p',{role:'status'}),actions=this.el('div',{class:'guided-inline-actions'}),start=this.el('button',{type:'submit',class:'button primary'},'Начать поиск'),close=this.button('Отмена',()=>dialog.close());actions.append(start,close);form.append(status,actions);dialog.append(form);document.body.append(dialog);this.searchDialog=dialog;
      let saving=false;dialog.oncancel=event=>{if(saving)event.preventDefault();};dialog.onclose=()=>{this.searchDialog=null;dialog.remove();opener?.focus?.({preventScroll:true});};
      form.onsubmit=async event=>{event.preventDefault();if(saving)return;try{if(active.has(this.state?.run?.status))throw new Error('Дождитесь завершения текущего запуска или остановите его.');const chosen=budget(calls.value,minutes.value);saving=true;start.disabled=close.disabled=calls.disabled=minutes.disabled=true;status.textContent='Создаём поиск…';this.setBusy(true);await this.cb.start({...base,budget:chosen,proof_backend:this.backend});saving=false;dialog.close();this.$('guided-current').scrollIntoView({behavior:'smooth',block:'start'});}catch(error){status.textContent=error.message;}finally{saving=false;start.disabled=close.disabled=calls.disabled=minutes.disabled=false;this.setBusy(false);}};
      dialog.showModal();calls.focus();
    }
    async retry(run){if(this.busy)return;this.setBusy(true);try{if(active.has(this.state?.run?.status))throw new Error('Дождитесь завершения текущего запуска или остановите его.');await this.cb.start(retryPayload(run));this.$('guided-current').scrollIntoView({behavior:'smooth',block:'start'});}catch(error){this.cb.error(error.message);}finally{this.setBusy(false);}}
    contractPanel(run){
      const preflight=contractPreflight(run);if(!preflight)return null;
      const box=this.el('section',{class:'guided-candidate','aria-label':'Постановка в Lean','data-contract-preflight':preflight.accepted?'accepted':'not_accepted'});box.append(this.el('h3',{},'Постановка в Lean'),this.el('p',{},preflight.title+'.'),this.prose('На этом этапе проверяются определения и корректность типа цели. Он не доказывает утверждение и не выдаёт сертификат доказательства.','p','guided-note'));
      if(run.phase==='library_context'&&preflight.accepted)box.append(this.prose('Этот отчёт относится к базовому черновику. Подбор библиотечных лемм и импортов ещё не завершён; изменённые импорты требуют повторной проверки типов до фиксации постановки.','p','guided-note'));
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
    reset(){this.token++;this.busy=false;this.source=null;this.paper=null;this.runKey='';this.step=null;this.stepContext=null;this.$('guided-selection').hidden=true;this.$('guided-source-preview').replaceChildren();this.$('guided-theorem-preview').replaceChildren();this.notice('');this.setBusy(false);this.renderShowcases();this.$('research-advanced').open=false;this.$('guided-setup').hidden=false;this.$('guided-setup').scrollIntoView({behavior:'smooth',block:'start'});this.ensureCatalog().catch(()=>{});}
    showMap(view='objects',selection){
      if(!this.map)return this.cb.details(view);
      if(view==='objects'){this.connectionView='map';this.runKey='';}
      if(this.state)this.goStep(view==='proof'?'lean':'connections',{scroll:false});
      this.map.setView(view);
      if(selection)this.map.select(selection);
      this.$('guided-map').scrollIntoView({behavior:'smooth',block:'start'});
    }
    setConnectionView(view){
      if(!['list','map'].includes(view)||!this.state)return;
      this.connectionView=view;this.runKey='';this.render(this.state);
      if(view==='map'&&this.candidateChecks?.selectedId)this.map?.select?.('transition:'+this.candidateChecks.selectedId);
    }
    renderConnectionViews(visible){
      const box=this.$('guided-connection-views');if(!box)return;box.hidden=!visible;if(!visible)return;
      box.setAttribute('role','group');box.setAttribute('aria-label','Представление найденных связей');
      if(!this.connectionViewButtons){this.connectionViewButtons={};box.replaceChildren();for(const[view,label,controls]of [['list','Список связей','guided-checks'],['map','Карта','guided-map']]){const button=this.button(label,()=>this.setConnectionView(view));button.setAttribute('aria-controls',controls);box.append(button);this.connectionViewButtons[view]=button;}}
      for(const[view,button]of Object.entries(this.connectionViewButtons))button.setAttribute('aria-pressed',String(this.connectionView===view));
    }
    partialPanel(run){
      if(partialSearchFinalizing(run)){const box=this.el('section',{class:'guided-candidate','aria-label':'Сохранение результата поиска'});box.append(this.prose('Сохраняем результаты поиска. Итоговое число кандидатов станет доступно после завершения сохранения.','p','guided-note'));const refresh=this.button('Обновить результаты поиска',async()=>{refresh.disabled=true;try{await(this.cb.refresh?this.cb.refresh():this.cb.load(run.id));}catch(error){box.append(this.prose(error.message));}finally{refresh.disabled=false;}});box.append(refresh);return box;}
      const info=partialSearchInfo(run);if(!info)return null;const box=this.el('section',{class:'guided-candidate','aria-label':'Частичный результат поиска'});
      box.append(this.el('p',{},'Поиск остановлен. '+(run.contract?.atlas_seed?'В этой попытке сохранено ':'Сохранено ')+info.count+' кандидатов из '+info.completed+' завершённых направлений.'),this.el('p',{class:'guided-note'},'Завершено направлений: '+info.completed+' / '+info.total+'. Остальные направления не завершены; предложенные связи ещё не проверены в Lean.'));
      const reason=run.termination?.message||run.error;if(reason)box.append(this.prose(reason,'p','guided-note'));
      if(info.status==='materialized')box.append(this.el('p',{},'Частичная карта доступна. Выберите найденную связь для отдельной проверки.'));
      else if(info.status==='available'&&info.count>0&&/^[a-f0-9]{64}$/i.test(info.snapshot)){
        const pending=this.partialRequest?.runId===run.id&&this.partialRequest?.snapshot===info.snapshot&&this.partialRequest.pending,button=this.button(pending?'Открываем найденные связи…':'Открыть найденные связи',()=>this.openPartial(run),true);button.disabled=!!pending;box.append(button);
      }else box.append(this.el('p',{},'Карта сохранённых предложений пока недоступна. Можно изучить источники и журнал работы.'));
      for(const issue of info.issues)box.append(this.prose(typeof issue==='string'?issue:issue.message||issue.reason||JSON.stringify(issue),'p','guided-note'));
      if(this.partialRequest?.runId===run.id&&this.partialRequest.error)box.append(this.el('p',{role:'alert'},this.partialRequest.error));return box;
    }
    async openPartial(run){
      const info=partialSearchInfo(run),current=()=>this.state?.run?.id===run.id&&this.state.run.partial_search?.snapshot_sha256===info?.snapshot;
      if(!info||info.status!=='available'||!info.count||!/^[a-f0-9]{64}$/i.test(info.snapshot)||!current()||this.partialRequest?.runId===run.id&&this.partialRequest.pending)return;
      const request=this.partialRequest={runId:run.id,snapshot:info.snapshot,pending:true,error:''};this.runKey='';this.render(this.state);
      try{
        await this.cb.api('/api/research/runs/'+encodeURIComponent(run.id)+'/partial-candidates',{snapshot_sha256:info.snapshot});
        if(current()&&await this.cb.load(run.id)===false)throw new Error('Не удалось открыть сохранённые связи. Повторите просмотр запуска.');
      }catch(error){if(current()&&this.partialRequest===request)request.error='Не удалось открыть найденные связи: '+error.message;}
      finally{request.pending=false;if(current()&&this.partialRequest===request){this.runKey='';this.render(this.state);}}
    }
    render(state){
      this.state=state;const run=state.run,draft=state.draftGraph,context=run?'run:'+run.id:draft?'graph:'+draft.id+':'+draft.revision:'new';
      if(context!==this.stepContext){this.stepContext=context;this.connectionView='list';this.step=selectedStep(run,draft,this.urlStep());if(run?.proof_backend){this.backend=run.proof_backend;const selector=this.$('workspace-backend');if(selector)selector.value=this.backend;}}else this.step=selectedStep(run,draft,this.step);
      this.$('research-panel').classList.toggle('has-open-research',!!run||!!draft);this.$('research-panel').dataset.workspaceStep=this.step;if(this.$('workspace-mechanisms'))this.$('workspace-mechanisms').hidden=!!run||!!draft;if(this.$('guided-showcases'))this.$('guided-showcases').hidden=!!run||!!draft;this.$('guided-setup').hidden=!!run||!!draft;
      this.$('structure-results').hidden=run?.purpose!=='structure';const structureSlot=this.$('guided-structure-slot');structureSlot.hidden=run?.purpose!=='structure'||this.step!=='connections';if(this.structureRunId!==run?.id){this.structureRunId=run?.id;structureSlot.open=awaitingStructureMap(run);}this.updateStart();this.renderHistory(state.runs);this.renderSteps(run,draft);
      // The clock has its own snapshot key and can change during one model call
      // while this parent's content key (including updated_at) stays unchanged.
      this.workspace?.render(run,draft,{step:this.step});
      this.atlas?.render(run,{visible:['connections','result'].includes(this.step)});
      const key=JSON.stringify([this.step,this.connectionView,run?.id,run?.status,run?.phase,run?.active_stage,run?.updated_at,run?.atlas_snapshot_sha256,run?.atlas_summary,run?.outcome_summary,run?.proof_progress,run?.partial_search,run?.partial_graph_ref,run?.object_graph?.id,run?.object_graph?.revision,draft?.id,draft?.revision,state.submitting,awaitingStructureMap(run),array(state.runs).map(r=>[r.id,r.status,r.updated_at])]);if(key===this.runKey)return;this.runKey=key;
      this.renderCurrent(run,draft);this.renderProgress(run);this.renderCandidates(run,draft);this.renderResult(run);this.renderSavedSource(run,draft);this.renderLeanStage(run);
      const graph=run?.object_graph||draft,checksReady=!!this.candidateChecks&&array(graph?.transitions).some(t=>mapModel()?.transitionRole(run||{object_graph:graph},t)==='bridge');
      const directions=this.$('guided-directions');directions.replaceChildren();directions.hidden=this.step!=='connections'||checksReady;
      if(!directions.hidden){directions.append(this.el('h2',{},'Направления и связи'),this.prose(run?.purpose==='prove'?'Карта, на которой выбрана проверяемая связь. Можно рассмотреть другие переходы, а затем вернуться к этой проверке через верхние этапы.':'Выберите переход на карте, чтобы исследовать его связи.','p','guided-note'));const codes=array((run?.object_graph||draft)?.msc_codes);if(codes.length)directions.append(this.prose('Области текущей карты · MSC '+codes.join(' · '),'p','guided-note'));}
      this.renderConnectionViews(this.step==='connections'&&checksReady);
      this.$('guided-checks').hidden=this.step!=='connections'||!checksReady||this.connectionView!=='list';
      if(this.step==='connections'&&checksReady)this.candidateChecks.render(run,draft,state.runs);else this.candidateChecks?.suspend?.();
      this.$('guided-saved-source').hidden=this.step!=='source'||!run&&!draft;
      this.$('guided-lean').hidden=this.step!=='lean';
      this.$('guided-progress').hidden=!active.has(run?.status)||!['lean','connections'].includes(this.step);
      this.$('guided-result').hidden=this.step!=='result';
      this.$('guided-candidates').hidden=this.step!=='connections'||this.$('guided-candidates').hidden;
      const mapRun=awaitingStructureMap(run)?null:run||(draft?{purpose:'discover',object_graph:draft}:null);
      const proofAvailable=array(run?.nodes).length||array(run?.result?.nodes).length;
      this.$('guided-map').hidden=!mapRun||!(this.step==='connections'&&(!checksReady||this.connectionView==='map')||this.step==='lean'&&proofAvailable);
      if(mapRun&&!this.$('guided-map').hidden)this.map?.render(mapRun,{runs:state.runs,view:this.step==='lean'?'proof':'objects',proofTransitionId:this.step==='lean'?run?.selected_transition_id:undefined});
    }
    renderCurrent(run,draft){const box=this.$('guided-current');box.hidden=!run&&!draft;box.replaceChildren();box.dataset.anchorOnly='false';if(box.hidden)return;if(['result','connections'].includes(this.step)){const partial=this.partialPanel(run);if(partial)box.append(partial);else box.dataset.anchorOnly='true';return;}const v=verdict(run);box.append(this.el('p',{class:'eyebrow'},run?(isSearch(run)?'Направления и связи':'Выбранный переход'):'Сохранённая постановка'),this.el('h2',{},run?titleOf(run):draft.title));
      const partial=this.partialPanel(run);if(partial)box.append(partial);
      const sourceTitle=array(run?.paper_manifest).map(p=>p.title).filter(Boolean).join(' · ');if(sourceTitle)box.append(this.prose(sourceTitle,'p','guided-note'));
      if(run){const row=this.el('div',{class:'guided-run-meta'});row.append(this.el('span',{class:'guided-badge '+(v.kind==='proved'?'good':'')},v.title),this.el('span',{},isSearch(run)&&v.kind==='search'?v.count+' переходов на карте':versionCaption(run)));box.append(row);}
      const actions=this.el('div',{class:'guided-inline-actions'});if(run)actions.append(this.button('Журнал работы',()=>this.cb.details('attempts')));if(actions.children.length)box.append(actions);
    }
    renderProgress(run){const box=this.$('guided-progress');box.hidden=!run||!active.has(run.status);box.replaceChildren();if(box.hidden)return;const head=this.el('div',{class:'guided-progress-heading'});head.append(this.el('span',{class:'guided-spinner','aria-hidden':'true'}),this.el('h3',{},progressText(run)));box.append(head);
      if(isSearch(run)){const summary=run.atlas_summary||{},counts=[['considered_codes','Кодов учтено при обзоре'],['query_count','Поисковых запросов выполнено'],['deep_completed','Углублённых направлений завершено'],['candidates_found','Кандидатов найдено']].filter(([key])=>Number.isInteger(summary[key])&&summary[key]>=0).map(([key,title])=>title+': '+summary[key]);if(counts.length)box.append(this.prose(counts.join(' · ')));box.append(this.prose('Поиск предлагает связи. Проверка выбранного кандидата в Lean запускается отдельно.','p','guided-note'));}
      else{const progress=proofProgress(run);if(progress.obligations_total>0)box.append(this.prose('Проверено обязательств: '+(progress.proved??'—')+' из '+progress.obligations_total+'. Итог появится после полной сборки и смысловой проверки.'));else box.append(this.prose(!progress.started||/formalize_transition|preflight|repair_contract|library_context|validate_contract/.test(run.phase||'')?'Готовим точную постановку; обязательства появятся после её принятия.':'Состав обязательств пока недоступен; ход проверки сохранён в журнале.','p','guided-note'));const preflight=this.contractPanel(run);if(preflight)box.append(preflight);}
      const recent=array(run.events).slice(-1)[0];if(recent?.message)box.append(this.prose(isSearch(run)&&/^Astra выполняет задачу: [a-z_]+\.?$/.test(recent.message)?progressText(run):recent.message,'p','guided-note'));box.append(this.prose('Можно оставить эту страницу: запуск сохраняется на локальном сервере. Процент готовности заранее неизвестен.','p','guided-note'));
      const stop=this.button(run.status==='cancelling'?'Останавливаем…':'Остановить и сохранить',()=>this.cb.action('cancel'));stop.disabled=run.status==='cancelling';box.append(stop);
    }
    renderCandidates(run,draft){const box=this.$('guided-candidates'),graph=run?.object_graph||draft;box.replaceChildren();box.hidden=!!this.map||!(draft||run?.purpose==='discover')||!graph;if(box.hidden)return;box.append(this.el('h3',{},'Выберите исходный переход'));for(const t of array(graph.transitions)){const card=this.el('article',{class:'guided-candidate'}),role=mapModel()?.transitionRole(run||{object_graph:graph},t);const status=window.ObjectGraphModel.presentation(t);card.append(this.el('span',{class:'guided-badge '+(status.status==='proved'?'good':'')},status.label),this.el('h4',{},t.title),this.prose(t.claim||t.description||''));card.append(this.button(role==='article'?'Искать по всему атласу':role==='bridge'?'Проверить общую структуру в Lean':'Исследовать переход',()=>role==='article'?this.searchAnalogies(graph,t):this.verify(graph,t),true));box.append(card);}}
    renderResult(run){
      const box=this.$('guided-result');box.replaceChildren();box.hidden=!run||active.has(run.status);if(box.hidden)return;
      const v=verdict(run),heading=this.el('header',{class:'guided-result-heading'}),status=this.el('div',{class:'guided-result-verdict'});
      box.dataset.verdict=v.kind;heading.append(this.el('p',{class:'eyebrow'},isSearch(run)?'Результат поиска':'Результат исследования'),this.el('h2',{},titleOf(run)));
      status.append(this.el('strong',{},v.title));heading.append(status);box.append(heading);
      if(isSearch(run)){
        if(run.status==='draft'){box.append(this.prose('Поиск этой попытки ещё не запускался. Начните его отдельной кнопкой в блоке хода исследования.'));return;}
        if(partialSearchFinalizing(run)){box.append(this.prose('Сохраняем результаты поиска. Итоговое число кандидатов пока недоступно.'));return;}
        const count=searchCandidateCount(run);box.append(this.prose((partialSearchInfo(run)?'Частичный результат: сохранено кандидатов: ':'На карте сохранено переходов: ')+count+'. Найденные предложения проверяются в Lean отдельным запуском.'));
        if(run.error)box.append(this.details('Диагностика завершения',run.error));
        box.append(this.button('Открыть направления и связи',()=>this.goStep('connections'),true));return;
      }
      const proof=run.result?.verification,sem=finalReview(run),termination=terminationInfo(run),summary=window.MathPresentation?.runSummary(run),transition=array(run.object_graph?.transitions).find(t=>t.id===run.selected_transition_id);
      const task=run.formal_contract||transition?.agent_task||run.contract?.agent_task,required=array(task?.required_obligations),checks=array(proof?.obligations),progress=proofProgress(run),preflight=this.contractPanel(run);
      const scopeReview=termination?.code==='needs_review'&&termination.stage==='formalize_transition'&&run.formalization_review?.status==='needs_review';
      const sameTarget=!task?.target||proof?.target===task.target,passed=item=>sameTarget&&(item?.ok===true||item?.passed===true||item?.success===true);
      const goals=required.length?required.map(goal=>({...goal,check:checks.find(item=>item.id===goal.id&&item.target===goal.target)})):checks.map(item=>({...item,check:item}));
      const count=checks.length&&sameTarget?goals.filter(goal=>passed(goal.check)).length:progress.proved,total=goals.length||progress.obligations_total;
      if(Number.isInteger(total)&&total>0)status.append(this.el('span',{class:'guided-result-count'},'Обязательства: '+(Number.isInteger(count)?count:'—')+'/'+total));
      if(progress.started&&!formalEvidence(run))box.append(this.prose('Доказательные попытки выполнялись. Частичные результаты не являются доказательством полного контракта.','p','guided-note'));

      const revise=run.source_card?.editable&&run.status!=='draft',refine=refinementTarget(run),retry=canRetry(run),alternatives=array(run.object_graph?.transitions).some(t=>t.id!==run.selected_transition_id);
      const needsFormulation=['invalid_contract','needs_review'].includes(termination?.code)&&!formalEvidence(run);
      let primary='proof';if(!['proved','refuted'].includes(v.kind))primary=needsFormulation&&refine?'refine':needsFormulation&&revise?'revise':retry?'retry':refine?'refine':revise?'revise':alternatives?'other':'proof';
      const actions=this.el('div',{class:'guided-inline-actions guided-result-actions'}),buttons=[];
      const add=(id,label,action)=>buttons.push({id,button:this.button(label,action,id===primary)});
      add('proof','Доказательство и отчёт Lean',()=>this.cb.details('result'));
      if(revise)add('revise','Создать исправленную версию',()=>this.openRevision(run));
      if(refine)add('refine','Уточнить постановку',()=>this.openRefinement(run));
      if(alternatives)add('other','Выбрать другую связь',()=>this.goStep('connections'));
      if(retry)add('retry','Повторить проверку',()=>this.retry(run));
      buttons.sort((a,b)=>Number(b.id===primary)-Number(a.id===primary));for(const item of buttons)actions.append(item.button);
      const artifacts=array(run.artifacts),final=artifacts.find(a=>/composition[\\/].*Candidate\.lean$/.test(a.path||a));
      if(final){const path=String(final.path||final).replaceAll('\\','/');if(!path.startsWith('/')&&!path.split('/').includes('..'))actions.append(this.el('a',{class:'button secondary',href:'/api/research/runs/'+encodeURIComponent(run.id)+'/artifacts/'+path.split('/').map(encodeURIComponent).join('/'),target:'_blank',rel:'noopener noreferrer'},'Открыть Lean-файл'));}
      box.append(actions);
      const application=run.source_application_status||run.final_semantic_review?.source_application_status||run.result?.semantic_review?.source_application_status;
      if(application==='not_verified'||mapModel()?.sourceTransition(run))box.append(this.prose('Это отдельный условный мост общей структуры. Его применимость к исходному переходу статьи отдельно не подтверждена.','p','guided-result-scope'));
      if(retry)box.append(this.prose('Повторная проверка создаст новый запуск с той же версией постановки и прежним бюджетом: '+run.budget.max_calls+' вызовов / '+Math.round(run.budget.timeout_seconds/60)+' мин. Текущая попытка останется в истории.','p','guided-note'));

      if(scopeReview){const review=this.el('section',{class:'guided-result-section'});review.append(this.el('h3',{},'Почему остановилась проверка'),this.prose(run.formalization_review.reason||termination.message));if(!preflight&&!hasLeanEvidence(run))review.append(this.prose('До проверки Lean не дошли: точная постановка ещё не подготовлена. Доказательство не получено.','p','guided-note'));box.append(review);}
      if(summary)this.renderSummary(box,summary);
      else if(v.kind==='proved')box.append(this.prose('Lean проверил точную формальную цель и все обязательства. Аудит аксиом пройден.'));
      if(!['proved','formal_only'].includes(v.kind)&&!scopeReview)box.append(this.prose(termination?.explanation||run.error||run.result?.error||run.result?.reason||'Сохранены попытки и диагностика. Отсутствие доказательства в этом запуске не доказывает невозможность связи.'));
      if(v.kind==='formal_only'&&termination)box.append(this.prose(termination.title+'. '+termination.explanation));
      if(task?.statement)box.append(this.details('Точная формальная цель',task.statement));
      if(goals.length){const section=this.el('section',{class:'guided-result-section guided-result-obligations'});section.append(this.el('h3',{},'Обязательства доказательства'));const ul=this.el('ol',{class:'guided-obligations'});for(const goal of goals){const row=this.el('li'),ok=passed(goal.check);row.append(this.el('span',{class:'guided-check '+(ok?'good':'')},ok?'✓':'○'),this.el('div',{},goal.title||goal.target||goal.id),this.details('Точный тип Lean',goal.statement||goal.expected_statement||goal.actual_statement||goal.check||goal));ul.append(row);}section.append(ul);box.append(section);}

      const boundaries=this.el('section',{class:'guided-result-section guided-result-boundaries'});boundaries.append(this.el('h3',{},scopeReview?'Что нужно уточнить для продолжения':'Условия и границы применения'));
      const disclosure=(title,values,reason,note)=>{const d=this.el('details',{class:'guided-details'});d.append(this.el('summary',{},title));if(note)d.append(this.prose(note,'p','guided-note'));if(reason)d.append(this.prose(reason));if(values.length){const list=this.el('ul');for(const value of values)list.append(this.prose(value,'li'));d.append(list);}boundaries.append(d);};
      const conditions=[...new Set([...array(run.source_card?.assumptions),...array(transition?.assumptions)])];
      if(conditions.length)disclosure('Условия исходной карточки',conditions,null,'Это условия литературной карточки и выбранного кандидата. Точные предпосылки проверенной цели указаны в типе Lean выше.');
      if(array(sem.limitations).length)disclosure('Ограничения итоговой рецензии',sem.limitations);
      if(array(summary?.limitations).length)disclosure('Границы математического представления',summary.limitations);
      const scope=run.source_card?.scope,sourceLimits=typeof scope==='string'&&scope?[scope]:array(scope);if(sourceLimits.length)disclosure('Границы исходной карточки',sourceLimits,null,'Сохранённое описание исходной постановки, а не итог проверки Lean.');
      if(run.contract_review)disclosure('Рецензия постановки до доказательства',array(run.contract_review.limitations),run.contract_review.reason||run.contract_review.status,'Историческая рецензия перед доказательством. Она не описывает текущий итог Lean.');
      if(run.formalization_review)disclosure('Исходная формализация',array(run.formalization_review.limitations),run.formalization_review.reason||run.formalization_review.status,'Сохранённое состояние этапа формализации до доказательства.');
      if(boundaries.children.length===1)boundaries.append(this.prose('Проверка относится только к точной сохранённой постановке. Дополнительные условия и границы не размечены; новое применение не подтверждается автоматически.'));
      if(sem.status==='not_performed')boundaries.append(this.prose(scopeReview?'Итоговая смысловая рецензия не проводилась: доказательство не получено.':sem.title,'p','guided-note'));
      if(proof)boundaries.append(this.prose('Lean проверяет точную формальную цель. Смысловая рецензия и оценка научной новизны — отдельные задачи.','p','guided-note'));box.append(boundaries);
      if(sem.status!=='not_performed'){const d=this.el('details',{class:'guided-details'});d.append(this.el('summary',{},'Итоговая смысловая рецензия и границы результата'),this.prose(sem.reason));box.append(d);}

      const technical=this.el('details',{class:'guided-details guided-result-technical'});technical.append(this.el('summary',{},'Постановка и технические подробности'));
      if(preflight)technical.append(preflight);
      const outcomeSummary=this.workspace?.result(run);if(outcomeSummary)technical.append(outcomeSummary);
      if(!summary&&(transition?.claim||run.claim)){const original=this.el('details',{class:'guided-details'});original.append(this.el('summary',{},'Исходная формулировка кандидата'),this.prose(transition?.claim||run.claim));technical.append(original);}
      if(termination||run.error||run.result?.error||run.result?.reason)technical.append(this.details('Диагностика завершения',{termination:run.termination||run.result?.termination||termination,error:run.error||run.result?.error,reason:run.result?.reason||run.formalization_review?.reason}));
      if(technical.children.length>1)box.append(technical);
    }
    renderHistory(runs){const items=array(runs);this.$('guided-history-count').textContent=items.length?'· '+items.length:'';this.history?.render(items,this.state?.run?.id||null);}
  }
  return {Workspace,stepNavigation,defaultStep,selectedStep,verdict,terminationInfo,hasLeanEvidence,contractPreflight,finalReview,formalEvidence,proofProgress,retryPayload,canRetry,titleOf,versionCaption,budget,matchExample,theoremChoices,sourceReady,structurePayload,transitionSearchPayload,sourceNavigation,refinementContext,refinementTarget,refinementDraft,discoveryPayload,progressText,awaitingStructureMap,partialSearchInfo,partialSearchFinalizing,searchCandidateCount};
});
