'use strict';

(function(root,factory){const api=factory(root);if(typeof module==='object'&&module.exports)module.exports=api;else root.CandidateChecks=api;})(typeof window==='undefined'?globalThis:window,root=>{
  const list=value=>Array.isArray(value)?value:[],active=new Set(['queued','running','cancelling']);
  const local=typeof module==='object'&&module.exports?require('./object-graph.js'):null;
  const objects=()=>root.ObjectGraphModel||local;
  const localMSC=typeof module==='object'&&module.exports?require('./msc-context.js'):null;
  const exact=(ref,graph)=>!!graph?.id&&ref?.id===graph.id&&ref.revision===graph.revision;
  const identity=graph=>graph?.id+':'+graph?.revision;
  const completed=value=>['complete','completed'].includes(value);
  const errorText=error=>error?.message||String(error);

  function attemptsFor(graph,transition,runs=[]){
    return list(runs).filter(run=>run?.id&&run.purpose==='prove'&&run.selected_transition_id===transition.id&&(exact(run.graph_ref,graph)||exact(run.source_graph_ref,graph)))
      .map((run,index)=>({run,index,derived:!exact(run.graph_ref,graph),time:Date.parse(run.finished_at||run.updated_at||run.created_at)||0}))
      .sort((a,b)=>b.time-a.time||a.index-b.index);
  }
  function certificateValid(graph,transition){
    const c=transition.certificate,r=c?.result?.verification;
    const environment=graph.active_environment_fingerprint||graph.environment_fingerprint;
    const environmentMatches=(!environment||c?.environment_fingerprint===environment&&r?.environment_fingerprint===environment)&&(!c?.environment_fingerprint||!r?.environment_fingerprint||c.environment_fingerprint===r.environment_fingerprint);
    return !!(environmentMatches&&c&&c.graph_id===graph.id&&c.revision===graph.revision&&c.transition_id===transition.id&&c.semantic_hash&&c.semantic_hash===transition.semantic_hash&&transition.agent_task?.target&&r?.target===transition.agent_task.target&&r.success===true&&r.compilation_success===true&&r.target_preserved===true&&r.obligations_passed===true&&r.audit?.status==='passed'&&!list(c.validation_errors).length);
  }
  function candidateRows(run,draft,runs=[],preview=null,batch=null){
    const graph=run?.object_graph||draft;if(!graph)return [];
    const history=[...list(runs)];if(run?.purpose==='prove'&&!history.some(item=>item.id===run.id))history.push(run);
    return list(graph.transitions).map(transition=>{
      const certificate=certificateValid(graph,transition),presented=objects()?.presentation({...transition,certificate:certificate?transition.certificate:null})||{status:'hypothesis',label:'Кандидат'};
      const attempts=attemptsFor(graph,transition,history),attempt=attempts[0],check=exact(preview?.graph_ref,graph)?list(preview.candidates).find(item=>item.transition_id===transition.id):null;
      let status=presented.status,label=presented.label;
      if(!certificate&&attempt){status=active.has(attempt.run.status)?'checking':'incomplete';label=attempt.derived?(active.has(attempt.run.status)?'Проверяется производная постановка':'Есть попытка производной постановки'):active.has(attempt.run.status)?'Идёт проверка':completed(attempt.run.status)&&['proved','refuted'].includes(attempt.run.outcome)?'Есть результат проверки':'Проверка не завершена';}
      if(!certificate&&check){label=({proposed:presented.label,invalid_contract:'Нужна исправленная постановка',needs_review:'Нужно уточнение',not_proved:'Проверка не завершена',verified:'Есть подтверждённый результат',historical_exact_evidence:'Есть результат точной постановки',ineligible:'Проверка пока недоступна'})[check.status]||label;if(['active','checking','running','queued'].includes(check.status)){status='checking';label='Идёт проверка';}}
      const termination=check?.termination||attempt?.run?.termination||attempt?.run?.result?.termination;
      // A failed derived formulation is not a rejection of the original
      // candidate. The server preview decides eligibility for this exact scope.
      const needsContract=check?['invalid_contract','needs_review'].includes(check.status):!!(transition.agent_task&&attempt&&!attempt.derived&&(['invalid_contract','needs_review'].includes(termination?.code)||attempt.run.requires_review===true));
      const needsReview=needsContract&&(check?check.status==='needs_review':termination?.code==='needs_review'||attempt?.run.requires_review===true);
      if(needsContract&&!certificate)label=needsReview?'Нужно уточнить объём задачи':'Нужна исправленная постановка';
      const correctionExplanation=needsReview?(termination?.stage==='formalize_transition'?'Сначала нужно уточнить условия или математический объём; Lean ещё не проверил этот кандидат.':'Сначала нужно уточнить условия или математический объём. Откройте причину, чтобы увидеть, что требует пересмотра.'):'Перед новой попыткой нужно исправить точную постановку. Ошибка формализации не означает, что математическая связь не существует.';
      const context=(root.MSCContext||localMSC)?.forNode(run||{object_graph:graph},{kind:'transition',value:transition},code=>root.MSCAtlas?.lookup?.(code));
      const last=transition.last_result,recordId=last?.graph_id===graph.id&&last.revision===graph.revision&&last.transition_id===transition.id?last.run_id:null;
      const batchItem=exact(batch?.graph_ref,graph)&&active.has(batch.status)?list(batch.items).find(item=>item.transition_id===transition.id&&['queued','running'].includes(item.status)):null;
      if(batchItem){status='checking';label=batchItem.status==='queued'?'В очереди проверки':batch.cancel_requested?'Останавливаем проверку':'Идёт проверка';}
      const hasFailure=!batchItem&&(needsContract||!!(termination?.code&&!['complete','completed','success'].includes(termination.code)));
      return {graph,transition,status,label,certificate,attempt,check,termination,needsContract,needsReview,correctionExplanation,hasFailure,batchItem,msc:context,eligible:!batchItem&&check?.eligible===true&&!needsContract&&!certificate,runId:batchItem?batchItem.run_id:check?.run_id||attempt?.run.id||(certificate?transition.certificate.run_id:null)||recordId};
    });
  }
  function perItemBudget(calls=16,minutes=30){
    const max_calls=Number(calls),timeout_seconds=Number(minutes)*60;
    if(!Number.isInteger(max_calls)||max_calls<1||max_calls>24||!Number.isInteger(timeout_seconds)||timeout_seconds<60||timeout_seconds>1800)throw new Error('Укажите от 1 до 24 вызовов и от 1 до 30 минут на одну связь.');
    return {max_calls,timeout_seconds,max_parallel:2};
  }
  function previewPayload(graph,budget){
    if(!graph?.id||!Number.isInteger(graph.revision))throw new Error('Нужна сохранённая версия карты.');
    return {graph_id:graph.id,graph_revision:graph.revision,transition_ids:list(graph.transitions).map(t=>t.id),mode:'multi',budget};
  }
  function batchPayload(graph,preview,budget,key){
    if(!exact(preview?.graph_ref,graph)||!preview.graph_sha256)throw new Error('Обновите список доступных связей перед запуском.');
    const transition_ids=list(preview.candidates).filter(item=>item.eligible===true).map(item=>item.transition_id),ids=new Set(list(graph.transitions).map(t=>t.id));
    if(!transition_ids.length||transition_ids.some(id=>!ids.has(id))||new Set(transition_ids).size!==transition_ids.length)throw new Error('В этой версии карты нет доступных связей для пакета.');
    if(!key)throw new Error('Не задан ключ запуска пакета.');
    return {...previewPayload(graph,budget),transition_ids,graph_sha256:preview.graph_sha256,idempotency_key:key};
  }
  const batchLabels={queued:'В очереди',running:'Проверяется',cancelling:'Останавливаем',complete:'Завершено',completed:'Завершено',failed:'Не завершено',skipped:'Пропущено',cancelled:'Остановлено',interrupted:'Прервано',budget_exhausted:'Лимит исчерпан'};
  function batchItemLabel(item){if(item.termination?.code==='needs_review')return 'Нужно уточнить постановку';if(item.termination?.code==='invalid_contract')return 'Постановка не принята';if(completed(item.status))return ['proved','refuted'].includes(item.outcome)?'Есть результат проверки':'Вывод не установлен';return batchLabels[item.status]||item.status;}
  let serial=0;
  class Workspace{
    constructor({container,api,onSelect,onVerify,onOpenRun,onError}={}){
      if(!container?.ownerDocument||typeof api!=='function')throw new TypeError('CandidateChecks requires a container and api.');
      this.doc=container.ownerDocument;this.api=api;this.onSelect=onSelect;this.onVerify=onVerify;this.onOpenRun=onOpenRun;this.onError=onError;this.rows=[];this.epoch=0;this.pending=false;this.destroyed=false;this.reviewOpen=false;this.budget=perItemBudget();this.itemBusy=new Set();this.uid='candidate-checks-'+(++serial);
      this.root=this.el('section','candidate-checks');this.root.setAttribute('aria-label','Проверки найденных связей');container.append(this.root);
      this.heading=this.el('h2','','Кандидаты и проверки');this.summary=this.el('p','candidate-checks-summary');this.summary.setAttribute('role','status');
      this.intro=this.el('p','candidate-checks-intro','Из источника выделены объекты и переходы. Для выбранного перехода модель предложила другие области MSC и возможные аналогии. Это кандидаты, а не уже доказанные связи.');
      this.cards=this.el('div','candidate-checks-list');this.error=this.el('p','candidate-checks-error');this.error.setAttribute('role','alert');this.error.hidden=true;
      this.reviewButton=this.button('Проверить все доступные связи',()=>this.openReview(),true);this.review=this.el('section','candidate-checks-review');this.review.hidden=true;this.review.setAttribute('aria-label','Подтверждение пакетной проверки');
      this.batchBox=this.el('section','candidate-checks-batch');this.batchBox.hidden=true;this.batchBox.setAttribute('aria-label','Ход пакетной проверки');
      this.root.append(this.heading,this.intro,this.summary,this.cards,this.error,this.reviewButton,this.review,this.batchBox);
      this.atlasReady=()=>{if(!this.destroyed){this.cardsKey='';this.paint();}};root.addEventListener?.('msc-atlas-ready',this.atlasReady);
    }
    el(tag,className='',text){const n=this.doc.createElement(tag);if(className)n.className=className;if(text!==undefined)n.textContent=String(text);return n;}
    prose(text,tag='p',className=''){const n=this.el(tag,className);if(root.MathPresentation?.render)root.MathPresentation.render(n,String(text||''));else n.textContent=String(text||'');return n;}
    button(text,fn,primary=false){const b=this.el('button','button '+(primary?'primary':'secondary'),text);b.type='button';b.onclick=()=>Promise.resolve().then(fn).catch(error=>this.fail(error));return b;}
    fail(error){if(this.destroyed)return;this.error.textContent=errorText(error);this.error.hidden=false;this.onError?.(errorText(error));}
    clearError(){this.error.hidden=true;this.error.textContent='';}
    render(run,draft,runs=[]){
      if(this.destroyed)return;const resumed=this.suspended;this.suspended=false;this.run=run||null;this.graph=run?.object_graph||draft||null;this.runs=list(runs);const context=identity(this.graph);
      this.root.hidden=!this.graph?.id||!list(this.graph.transitions).length;if(this.root.hidden){this.suspend();return;}
      if(context!==this.context){this.context=context;this.epoch++;this.preview=null;this.reviewOpen=false;this.review.hidden=true;this.batch=null;this.requestPayload=null;this.pending=false;this.cardsKey='';this.previewKey='';this.clearError();clearTimeout(this.timer);this.loadBatches(this.epoch);}
      else if(resumed){this.loadBatches(this.epoch);this.previewKey='';}
      this.paint();
      const key=JSON.stringify([context,list(this.graph.transitions).map(t=>[t.id,t.status,t.semantic_hash,t.certificate?.publication_id]),this.runs.map(r=>[r.id,r.status,r.termination?.code])]);
      if(key!==this.previewKey){this.previewKey=key;this.refreshPreview(false).catch(error=>this.fail(error));}
    }
    paint(){
      if(this.destroyed||!this.graph)return;this.rows=candidateRows(this.run,this.run?null:this.graph,this.runs,this.preview,this.batch);
      const done=this.rows.filter(row=>row.certificate&&['proved','refuted'].includes(row.status)).length,eligible=this.rows.filter(row=>row.eligible).length;
      this.summary.textContent='Связей: '+this.rows.length+' · Проверены в этой версии: '+done+' · Доступны: '+eligible+(this.preview?'':' · уточняем доступность');
      const key=JSON.stringify(this.rows.map(row=>[row.transition.id,row.transition.title,row.status,row.label,row.eligible,row.needsContract,row.correctionExplanation,row.runId,row.attempt?.derived,row.msc,row.check?.reason]));
      if(key!==this.cardsKey){this.cardsKey=key;this.cards.replaceChildren();for(const row of this.rows)this.cards.append(this.card(row));}
      this.reviewButton.disabled=this.pending||active.has(this.batch?.status)||!this.rows.length;this.paintReview();this.paintBatch();
    }
    card(row){
      const card=this.el('article','candidate-check'),head=this.el('div','candidate-check-heading'),status=this.el('span','candidate-check-status',row.label);status.dataset.status=row.status;
      head.append(this.prose(row.transition.title||row.transition.id,'h3'),status);card.append(head);
      if(list(row.msc?.items).length){const details=this.el('details','candidate-check-msc'),items=this.el('ul');details.append(this.el('summary','','Рубрики MSC2020 · '+row.msc.items.map(item=>item.code).join(', ')),this.el('p','',row.msc.label));for(const item of row.msc.items)items.append(this.el('li','',item.code+' — '+item.title));details.append(items);card.append(details);}
      if(row.needsContract)card.append(this.el('p','candidate-check-explanation',row.correctionExplanation));
      else if(row.attempt?.derived)card.append(this.el('p','candidate-check-explanation','Сохранённая попытка относится к производной постановке. Её результат не является сертификатом исходной версии.'));
      else if(row.check?.reason)card.append(this.prose(row.check.reason,'p','candidate-check-explanation'));
      const actions=this.el('div','candidate-check-actions');
      if(row.runId)actions.append(this.button(row.hasFailure?'Открыть причину':'Открыть проверку',()=>this.onOpenRun?.(row.runId)));
      if(row.eligible){const b=this.button(row.runId?'Повторить проверку':'Проверить связь',()=>this.verify(this.rows.find(item=>item.transition.id===row.transition.id)),!row.runId);b.disabled=this.pending||this.itemBusy.has(row.transition.id)||active.has(this.batch?.status);actions.append(b);}
      actions.append(this.button('На карте',()=>{const current=this.rows.find(item=>item.transition.id===row.transition.id);if(current)this.onSelect?.(current.graph,current.transition);}));card.append(actions);return card;
    }
    async verify(row){if(!row||this.pending||this.itemBusy.has(row.transition.id)||active.has(this.batch?.status)||!row.eligible||row.graph!==this.graph)return;this.itemBusy.add(row.transition.id);this.cardsKey='';this.paint();try{await this.onVerify?.(row.graph,row.transition);}finally{this.itemBusy.delete(row.transition.id);this.cardsKey='';this.paint();}}
    async refreshPreview(review=false){
      // An uncertain create is retried with precisely the displayed, approved
      // request. A background preview must not replace that confirmation list.
      if(this.requestPayload){if(review){this.reviewOpen=true;this.paint();}return this.preview;}
      const epoch=this.epoch,graph=this.graph,budget={...this.budget},payload=previewPayload(graph,budget),token=(this.previewToken||0)+1;this.previewToken=token;
      const value=await this.api('/api/research/batches/preview',payload);if(this.destroyed||epoch!==this.epoch||token!==this.previewToken)return null;
      if(!exact(value.graph_ref,graph))throw new Error('Сервис вернул доступность другой версии карты.');this.preview=value;this.previewBudget=budget;
      if(review){this.reviewOpen=true;this.reviewDirty=false;}this.paint();return value;
    }
    async openReview(){if(this.pending||this.reviewLoading||active.has(this.batch?.status))return;this.reviewLoading=true;this.clearError();try{await this.refreshPreview(true);}finally{this.reviewLoading=false;}if(!this.destroyed&&this.reviewOpen)this.reviewHeading?.focus?.();}
    paintReview(){
      this.review.hidden=!this.reviewOpen;if(!this.reviewOpen)return;
      const key=JSON.stringify([this.preview,this.budget,this.pending,!!this.requestPayload]);if(key===this.reviewKey)return;this.reviewKey=key;this.review.replaceChildren();
      const h=this.el('h3','','Проверить связи последовательно');h.tabIndex=-1;this.reviewHeading=h;this.review.append(h,this.el('p','','Каждая связь получает отдельный запуск. Неудачная попытка сохраняется; затем очередь переходит к следующей. Остановка сохраняет выполненную работу.'));
      const controls=this.el('div','candidate-check-budget'),calls=this.el('input'),minutes=this.el('input');calls.type=minutes.type='number';calls.min=minutes.min='1';calls.max='24';minutes.max='30';calls.value=String(this.budget.max_calls);minutes.value=String(this.budget.timeout_seconds/60);calls.disabled=minutes.disabled=this.pending||!!this.requestPayload;
      const a=this.el('label','','Вызовов на одну связь'),b=this.el('label','','Минут на одну связь');a.append(calls);b.append(minutes);controls.append(a,b);this.review.append(controls);
      this.review.append(this.button('Пересчитать список и общий лимит',async()=>{if(this.pending||this.requestPayload)return;this.budget=perItemBudget(calls.value,minutes.value);await this.refreshPreview(true);}));
      const ul=this.el('ul','candidate-check-review-list');for(const item of list(this.preview?.candidates))ul.append(this.el('li','',item.title+' · '+(item.eligible?'Будет проверена':item.reason||'Пропущена')));this.review.append(ul);
      const total=this.preview?.aggregate,n=list(this.preview?.candidates).filter(item=>item.eligible).length;
      this.review.append(this.el('p','candidate-check-total',total?'Общий лимит пакета: до '+total.max_calls+' вызовов и '+Math.ceil(total.timeout_seconds/60)+' минут · одновременно 1 связь.':'Общий лимит ещё не рассчитан.'));
      const start=this.button(this.pending?'Создаём очередь…':this.requestPayload?'Повторить отправку того же пакета':'Начать проверку · '+n,()=>this.startBatch(),true);start.disabled=this.pending||!n||!total||this.reviewDirty;this.review.append(start);
      calls.oninput=minutes.oninput=()=>{this.reviewDirty=true;start.disabled=true;};
      if(this.requestPayload&&!this.pending)this.review.append(this.el('p','candidate-check-explanation','Ответ не получен. Повторная отправка использует тот же ключ и не создаёт вторую очередь.'));
      const close=this.button('Закрыть',()=>{if(this.pending)return;this.reviewOpen=false;this.review.hidden=true;this.reviewButton.focus?.();});close.disabled=this.pending;this.review.append(close);
    }
    async startBatch(){
      if(this.pending||active.has(this.batch?.status)||!this.reviewOpen||this.reviewDirty)return;
      if(!this.requestPayload){const key=root.crypto?.randomUUID?.();if(!key)throw new Error('Браузер не поддерживает безопасный идентификатор запуска.');this.requestPayload=batchPayload(this.graph,this.preview,this.previewBudget,key);}
      const epoch=this.epoch,payload=this.requestPayload;this.previewToken=(this.previewToken||0)+1;this.batchLoadToken=(this.batchLoadToken||0)+1;this.pending=true;this.clearError();this.cardsKey='';this.paint();
      try{const value=await this.api('/api/research/batches',payload);if(this.destroyed||epoch!==this.epoch)return;if(!exact(value.graph_ref,this.graph)||!value.id)throw new Error('Ответ очереди относится к другой версии карты.');this.batch=value;this.requestPayload=null;this.reviewOpen=false;this.pollSoon();}
      catch(error){if(!this.destroyed&&epoch===this.epoch){const status=Number(error?.status);if(status>=400&&status<500&&![408,429].includes(status)){this.requestPayload=null;this.previewKey='';this.reviewDirty=true;this.reviewKey='';this.fail(new Error('Пакет не создан. Обновите список и общий лимит перед новой отправкой. '+errorText(error)));}else this.fail(error);}}
      finally{if(!this.destroyed&&epoch===this.epoch){this.pending=false;this.cardsKey='';this.paint();}}
    }
    async loadBatches(epoch){const token=(this.batchLoadToken||0)+1;this.batchLoadToken=token;try{const response=await this.api('/api/research/batches?graph_id='+encodeURIComponent(this.graph.id)+'&graph_revision='+this.graph.revision);if(this.destroyed||epoch!==this.epoch||token!==this.batchLoadToken)return;this.batch=list(response.batches).filter(batch=>exact(batch.graph_ref,this.graph)).sort((a,b)=>(Date.parse(b.updated_at||b.created_at)||0)-(Date.parse(a.updated_at||a.created_at)||0))[0]||null;this.paint();this.pollSoon();}catch(error){if(!this.destroyed&&epoch===this.epoch)this.fail(error);}}
    pollSoon(){clearTimeout(this.timer);if(!this.destroyed&&!this.suspended&&active.has(this.batch?.status))this.timer=setTimeout(()=>this.pollBatch(),1800);}
    async pollBatch(){const epoch=this.epoch,id=this.batch?.id;if(!id||this.polling)return;this.polling=true;try{const value=await this.api('/api/research/batches/'+encodeURIComponent(id));if(!this.destroyed&&epoch===this.epoch&&this.batch?.id===id){this.batch=value;this.paint();if(!active.has(value.status))await this.refreshPreview();}}catch(error){if(!this.destroyed&&epoch===this.epoch)this.fail(error);}finally{this.polling=false;this.pollSoon();}}
    async cancelBatch(){if(this.cancelling||!active.has(this.batch?.status)||this.batch.cancel_requested)return;const epoch=this.epoch,id=this.batch.id;this.cancelling=true;this.paintBatch();try{const value=await this.api('/api/research/batches/'+encodeURIComponent(id)+'/cancel',{});if(!this.destroyed&&epoch===this.epoch&&this.batch?.id===id)this.batch=value;}finally{this.cancelling=false;this.paintBatch();this.pollSoon();}}
    paintBatch(){
      this.batchBox.hidden=!this.batch;if(!this.batch)return;const key=JSON.stringify([this.batch,this.cancelling]);if(key===this.batchKey)return;this.batchKey=key;this.batchBox.replaceChildren();
      const items=list(this.batch.items),done=items.filter(item=>!active.has(item.status)).length;
      this.batchBox.append(this.el('h3','',completed(this.batch.status)?'Очередь завершена':'Пакетная проверка · '+(batchLabels[this.batch.status]||this.batch.status)),this.el('p','candidate-check-batch-progress','Завершено: '+done+' из '+items.length+'. Связи проверяются по очереди.'));
      const ul=this.el('ul');for(const item of items){const li=this.el('li');li.append(this.prose(item.title||item.transition_id,'strong'),this.el('span','candidate-check-batch-state',batchItemLabel(item)));if(item.reason||item.termination?.message)li.append(this.prose(item.reason||item.termination.message,'p','candidate-check-explanation'));if(item.run_id)li.append(this.button('Открыть попытку',()=>this.onOpenRun?.(item.run_id)));ul.append(li);}this.batchBox.append(ul);
      if(this.batch.aggregate)this.batchBox.append(this.el('p','candidate-check-explanation','Общий лимит: '+this.batch.aggregate.max_calls+' вызовов · '+Math.ceil(this.batch.aggregate.timeout_seconds/60)+' минут.'));
      if(active.has(this.batch.status)){const cancel=this.button(this.cancelling||this.batch.cancel_requested?'Останавливаем очередь…':'Остановить пакет и сохранить',()=>this.cancelBatch());cancel.disabled=this.cancelling||this.batch.cancel_requested;this.batchBox.append(cancel);}else this.batchBox.append(this.button('Проверить оставшиеся доступные связи',()=>this.openReview()));
    }
    suspend(){this.suspended=true;clearTimeout(this.timer);}
    destroy(){this.destroyed=true;this.epoch++;clearTimeout(this.timer);root.removeEventListener?.('msc-atlas-ready',this.atlasReady);this.root.remove();}
  }
  return {Workspace,candidateRows,attemptsFor,certificateValid,perItemBudget,previewPayload,batchPayload,batchItemLabel};
});
