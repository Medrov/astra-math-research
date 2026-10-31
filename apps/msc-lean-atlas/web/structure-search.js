'use strict';

(function(root,factory){const model=factory();if(typeof module==='object'&&module.exports)module.exports=model;else root.StructureSearch=model;})(typeof window==='undefined'?globalThis:window,()=>{
  const array=value=>Array.isArray(value)?value:[];
  const text=value=>value==null?'':typeof value==='string'?value:JSON.stringify(value,null,2);
  const active=new Set(['queued','running','cancelling']);
  const localMap=typeof module==='object'&&module.exports?require('./research-map.js'):null,mapModel=()=>globalThis.ResearchMap||localMap;
  const sourceTransition=run=>mapModel()?.sourceTransition(run)||null;
  function ready(source){return source?.status==='ready'&&source.inspection?.status==='complete'&&source.inspection.success===true;}
  function generated(name){return /(?:^|\.)(?:eq_\d+|_proof_\d+|_match_\d+)$/.test(name);}
  function theorems(source){return ready(source)?array(source.declarations).filter(d=>d.kind==='theorem'&&typeof d.name==='string').sort((a,b)=>Number(generated(a.name))-Number(generated(b.name))):[];}
  function selectedTarget(source,previous=''){const declarations=theorems(source);if(declarations.some(item=>item.name===previous))return previous;return declarations.length===1&&!generated(declarations[0].name)?declarations[0].name:'';}
  function payload(source,target,{mode='single',budget,question=''}={}){
    if(!ready(source))throw new Error('Сначала успешно проверьте Lean-источник.');
    if(!theorems(source).some(d=>d.name===target))throw new Error('Выберите теорему из проверенного исходника.');
    if(!['single','multi'].includes(mode))throw new Error('Поиск общей структуры требует режима Astra.');
    return {purpose:'structure',source_id:source.id,target,mode,budget,...(question.trim()?{question:question.trim()}:{} )};
  }
  function candidateGroups(run){
    const transitions=new Map(array(run?.object_graph?.transitions).map(t=>[t.id,t])),seen=new Set();
    return array(run?.structure_routes).map((route,index)=>{
      const candidates=[];
      for(const candidate of array(route.candidates)){
        const id=candidate.transition_id;if(!id||seen.has(id)||!transitions.has(id))continue;seen.add(id);
        candidates.push({...candidate,transition:transitions.get(id),route,order:candidates.length});
      }
      candidates.sort((a,b)=>(Number.isFinite(a.rank)?a.rank:Infinity)-(Number.isFinite(b.rank)?b.rank:Infinity)||a.order-b.order);
      return {route,index,candidates};
    });
  }
  function rankedCandidates(run){return candidateGroups(run).flatMap(group=>group.candidates);}
  function excerpt(value,limit=230){const content=text(value).replace(/\s+/g,' ').trim();if(content.length<=limit)return content;const cut=content.lastIndexOf(' ',limit);return content.slice(0,cut>limit*.6?cut:limit).trimEnd()+'…';}
  function searchSummary(run){
    const count=rankedCandidates(run).length;
    if(run?.status==='complete')return 'Поиск завершён: '+count+' '+(count%10===1&&count%100!==11?'кандидат':count%10>=2&&count%10<=4&&!(count%100>=12&&count%100<=14)?'кандидата':'кандидатов');
    if(active.has(run?.status))return 'Поиск идёт · найдено кандидатов: '+count;
    return 'Поиск не завершён · сохранено кандидатов: '+count;
  }
  function candidateStatus(transition,model){
    if(typeof model?.statusOf==='function'){
      const result=model.statusOf(transition);
      if(result&&typeof result==='object')return result;
      if(typeof result==='string'&&model.STATUS?.[result])return {status:result,...model.STATUS[result]};
    }
    if(typeof model?.presentation==='function')return model.presentation(transition);
    return {status:'incomplete',label:'Статус проверки недоступен'};
  }
  function renderMath(node,value,renderer){
    const content=text(value);node.textContent=content;
    if(typeof renderer?.render==='function'){try{renderer.render(node,content);}catch{node.textContent=content;}}
    return node;
  }
  function profilePreview(run,profile,renderer){
    let summary=null;
    if(run?.purpose==='structure'&&typeof renderer?.runSummary==='function'){try{summary=renderer.runSummary(run);}catch{}}
    if(summary)return {known:true,summary,steps:[['Объекты','Полиномиальные преобразования F и G'],['Общий механизм','Подстановка и обратимость'],['Вывод',summary.description]],formula:array(summary.formulas).at(-1)};
    return {known:false,steps:[['Объекты',array(profile.objects).slice(0,2).join('; ')],['Общий механизм',profile.mechanism],['Вывод',profile.conclusion_shape]]};
  }
  function routeTitle(route){const titles=new Map([['13','Коммутативная алгебра'],['14','Алгебраическая геометрия'],['37','Динамические системы']]);return titles.get(route?.msc_code)||route?.title||'Область ещё не выбрана';}
  class Workspace {
    constructor(callbacks){
      this.callbacks=callbacks;this.source=null;this.sources=[];this.examples=[];this.busy=false;this.initialized=false;this.token=0;this.resultKey='';this.selected=null;
      this.$('structure-source').onchange=()=>this.choose();
      this.$('structure-file').onchange=()=>{this.source=null;this.renderSource();this.changed();};
      this.$('structure-inspect').onclick=()=>this.inspect();
      this.$('structure-target').onchange=()=>{this.renderTarget();this.changed();};
    }
    $(id){return document.getElementById(id);}
    el(tag,attrs={},value){const node=document.createElement(tag);for(const[k,v]of Object.entries(attrs))node.setAttribute(k,String(v));if(value!==undefined)node.textContent=text(value);return node;}
    changed(){this.callbacks.onChange?.();}
    notice(message,state=''){const node=this.$('structure-source-status');node.textContent=message;node.dataset.state=state;}
    details(title,value){const node=this.el('details');node.append(this.el('summary',{},title),this.el('pre',{},text(value)));return node;}
    math(tag,value,attrs={}){return renderMath(this.el(tag,attrs),value,globalThis.MathPresentation);}
    setSource(source,target=''){
      ++this.token;this.busy=false;this.source=source||null;this.$('structure-target').value='';
      if(source?.id){const index=this.sources.findIndex(item=>item.id===source.id);if(index<0)this.sources.unshift(source);else this.sources[index]=source;}
      this.renderPicker();this.renderSource();
      if(target){this.$('structure-target').value=theorems(source).some(item=>item.name===target)?target:'';this.renderTarget();}
      this.changed();
    }
    async refresh(){
      if(this.busy)return;this.busy=true;this.changed();
      try{const data=await this.callbacks.api('/api/structure/sources');this.sources=array(data.sources);this.examples=array(data.examples);this.initialized=true;this.renderPicker();}
      catch(e){this.notice('Источники недоступны: '+e.message,'error');}
      finally{this.busy=false;this.renderSource();this.changed();}
    }
    renderPicker(){
      const picker=this.$('structure-source'),previous=picker.value;picker.replaceChildren();
      if(this.source?.id&&!this.sources.some(s=>s.id===this.source.id))this.sources.unshift(this.source);
      for(const example of this.examples)picker.append(this.el('option',{value:'example:'+example.id},example.title||example.id));
      picker.append(this.el('option',{value:'upload'},'Загрузить свой .lean'));
      if(this.sources.length){const group=this.el('optgroup',{label:'Сохранённые источники'});for(const source of this.sources)group.append(this.el('option',{value:source.id},source.title||source.name||source.id));picker.append(group);}
      const chosen=this.source?.id||previous;if([...picker.options].some(o=>o.value===chosen))picker.value=chosen;
      this.$('structure-upload-fields').hidden=picker.value!=='upload';
    }
    async choose(){
      const value=this.$('structure-source').value,token=++this.token;this.source=null;this.$('structure-upload-fields').hidden=value!=='upload';this.renderSource();this.changed();
      if(!value||value==='upload'||value.startsWith('example:')){this.notice('Нажмите «Проверить исходник локально». Модель не вызывается.');return;}
      this.busy=true;this.notice('Загружаем проверенный источник…');this.renderSource();this.changed();
      try{const data=await this.callbacks.api('/api/structure/sources/'+encodeURIComponent(value));if(token!==this.token)return;this.source=data.source;this.renderSource();}
      catch(e){if(token===this.token)this.notice('Не удалось открыть источник: '+e.message,'error');}
      finally{if(token===this.token){this.busy=false;this.renderSource();this.changed();}}
    }
    async inspect(){
      if(this.busy)return;const value=this.$('structure-source').value;if(value&&!value.startsWith('example:')&&value!=='upload'){await this.choose();return;}
      const token=++this.token;this.busy=true;this.source=null;this.notice('Lean проверяет исходник и зависимости аксиом. Это может занять некоторое время.');this.renderSource();this.changed();
      try{
        let body;if(value.startsWith('example:'))body={example_id:value.slice(8)};
        else{const file=this.$('structure-file').files?.[0];if(!file||!file.name.toLowerCase().endsWith('.lean'))throw new Error('Выберите один файл с расширением .lean.');if(file.size>250000)throw new Error('Размер исходника должен быть не больше 250 000 байт.');body={name:file.name,content:await file.text()};}
        const data=await this.callbacks.api('/api/structure/sources',body);if(token!==this.token)return;
        this.source=data.source;if(!this.source?.id)throw new Error('Сервер не вернул идентификатор источника.');
        const i=this.sources.findIndex(s=>s.id===this.source.id);if(i<0)this.sources.unshift(this.source);else this.sources[i]=this.source;this.renderPicker();this.renderSource();
      }catch(e){if(token===this.token)this.notice('Не удалось проверить исходник: '+e.message,'error');}
      finally{if(token===this.token){this.busy=false;this.renderSource();this.changed();}}
    }
    renderSource(){
      const source=this.source,box=this.$('structure-source-detail'),picker=this.$('structure-target'),previous=picker.value;
      this.$('structure-source').disabled=this.busy;this.$('structure-file').disabled=this.busy;this.$('structure-inspect').disabled=this.busy;
      this.$('structure-inspect').textContent=this.busy?'Проверяем источник…':source?'Обновить сведения об источнике':'Проверить исходник локально';
      box.replaceChildren();box.hidden=!source;picker.replaceChildren();picker.disabled=this.busy||!theorems(source).length;
      if(!source){picker.append(this.el('option',{value:''},'Сначала проверьте исходник'));this.renderTarget();return;}
      box.append(this.el('strong',{},source.title||source.name||source.id),this.el('p',{},ready(source)?'Исходник скомпилирован; аудит аксиом завершён.':'Исходник не прошёл проверку. Поиск по нему недоступен.'));
      if(source.source_sha256)box.append(this.details('Хеш сохранённого исходника',source.source_sha256));
      if(array(source.imports).length)box.append(this.details('Импорты',source.imports.join('\n')));
      if(source.provenance)box.append(this.details('Происхождение исходника',source.provenance));
      if(source.limitations)box.append(this.el('p',{},array(source.limitations).length?source.limitations.join(' '):source.limitations));
      if(!ready(source)){this.notice(source.inspection?.error||'Проверка Lean не завершилась успешно.','error');picker.append(this.el('option',{value:''},'Нет проверенных теорем'));}
      else{const declarations=theorems(source);if(declarations.length>1||declarations.some(d=>generated(d.name)))picker.append(this.el('option',{value:''},'Выберите исходную теорему…'));for(const declaration of declarations)picker.append(this.el('option',{value:declaration.name},declaration.name+(generated(declaration.name)?' · служебная':'')));picker.value=selectedTarget(source,previous);this.notice(declarations.length?'Проверено локально · теорем: '+declarations.length+'. Выберите исходную теорему.':'Исходник проверен, но экспортированных теорем в нём нет.',declarations.length?'ready':'error');}
      this.renderTarget();
    }
    renderTarget(){
      const box=this.$('structure-target-detail'),declaration=theorems(this.source).find(d=>d.name===this.$('structure-target').value);box.replaceChildren();box.hidden=!declaration;if(!declaration)return;
      box.append(this.details('Точное утверждение Lean',declaration.type));
      box.append(this.details('Аксиомы и зависимости',{'Аксиомы':declaration.axioms||[],'Зависимости доказательства':declaration.dependencies||[],'Зависимости типа':declaration.type_dependencies||[]}));
    }
    canStart(){return !this.busy&&theorems(this.source).some(d=>d.name===this.$('structure-target').value);}
    input(options){return payload(this.source,this.$('structure-target').value,{...options,question:this.$('structure-question').value});}
    title(){return this.$('structure-target').value||'От теоремы к общей структуре';}
    async restore(run){
      if(!run?.source_id){if(sourceTransition(run)){++this.token;this.busy=false;this.source=null;this.$('structure-target').value='';this.renderSource();this.notice('Источник этого поиска — сохранённый переход статьи. Lean-файл для поиска аналогов не требуется.','ready');this.changed();}return;}const token=++this.token;
      if(this.source?.id===run.source_id){this.$('structure-target').value=run.target||'';this.renderTarget();return;}
      this.source=null;this.busy=true;this.renderSource();this.changed();
      try{const data=await this.callbacks.api('/api/structure/sources/'+encodeURIComponent(run.source_id));if(token!==this.token)return;this.source=data.source;if(!this.sources.some(s=>s.id===this.source.id))this.sources.unshift(this.source);this.renderPicker();this.renderSource();this.$('structure-target').value=run.target||'';this.renderTarget();}
      catch(e){if(token===this.token)this.notice('Исходник этого запуска недоступен: '+e.message,'error');}
      finally{if(token===this.token){this.busy=false;this.renderSource();this.changed();}}
    }
    sourceEvidence(evidence){
      const node=this.el('div',{class:'structure-evidence'}),url=evidence.url||evidence.source_url||evidence.source?.url;let safe;try{const parsed=new URL(url,location.origin);if(url&&['http:','https:'].includes(parsed.protocol))safe=parsed.href;}catch{}
      const title=evidence.title||evidence.name||evidence.id||'Источник';node.append(safe?this.el('a',{href:safe,target:'_blank',rel:'noopener noreferrer'},title):this.el('p',{},title));
      if(evidence.module||evidence.name)node.append(this.el('p',{},[evidence.module,evidence.name].filter(Boolean).join(' · ')));
      if(evidence.statement)node.append(this.math('p',evidence.statement));
      if(evidence.content&&evidence.content!==evidence.statement)node.append(this.math('p',evidence.content));
      if(evidence.text&&evidence.text!==evidence.statement&&evidence.text!==evidence.content)node.append(this.math('p',evidence.text));
      if(evidence.extraction)node.append(this.el('p',{class:'research-hint'},'Способ извлечения: '+evidence.extraction+'. Наличие источника не доказывает переход.'));
      return node;
    }
    renderSourceTransition(run){
      const source=sourceTransition(run);if(!source)return null;const value=source.transition,objects=new Map(array(source.objects).map(object=>[object.id,object])),box=this.el('section',{class:'structure-origin'});
      box.append(this.el('span',{class:'structure-kicker'},'Исходный переход статьи'),this.math('h3',value.title||value.id),this.el('p',{class:'research-hint'},'Утверждение источника зафиксировано для поиска аналогов. Сам поиск не подтверждает его в Lean.'));
      const flow=this.el('div',{class:'structure-origin-flow'});for(const[label,ids]of [['Входные объекты',value.source_ids],['Выходные объекты',value.target_ids]]){const group=this.el('div');group.append(this.el('h4',{},label));const ul=this.el('ul');for(const id of [...new Set(array(ids))])ul.append(this.math('li',objects.get(id)?.title||'Объект '+id+' отсутствует в снимке источника'));if(!ul.children.length)ul.append(this.el('li',{},'Не указаны'));group.append(ul);flow.append(group);}box.append(flow);
      const full=this.el('details');full.append(this.el('summary',{},'Исходное утверждение, условия и источники'),this.math('p',value.claim||'Утверждение не сохранено.'));if(value.construction)full.append(this.el('h4',{},'Конструкция'),this.math('p',value.construction));if(array(value.assumptions).length){full.append(this.el('h4',{},'Предпосылки'));const ul=this.el('ul');for(const assumption of value.assumptions)ul.append(this.math('li',assumption));full.append(ul);}for(const evidence of array(source.sources))full.append(this.sourceEvidence(evidence));full.append(this.el('p',{class:'research-hint'},'Версия исходной карты: '+source.graph_ref.revision+' · '+(source.source_sha256||source.semantic_hash||'').slice(0,12)));box.append(full);return box;
    }
    renderProfile(profile,run){
      const panel=this.el('section',{class:'structure-profile structure-theorem-paper'});
      const preview=profilePreview(run,profile,globalThis.MathPresentation);
      const fromArticle=!!sourceTransition(run);panel.append(this.el('span',{class:'structure-kicker'},fromArticle?'Предложение модели · требует проверки':'Отправная точка'),this.el('h3',{},preview.known?preview.summary.title:fromArticle?'Предложенный структурный паттерн':'Структура исходной теоремы'));
      if(preview.known){
        panel.append(this.math('p',preview.summary.description));
        const formulas=this.el('div',{class:'structure-source-formulas'});
        for(const item of array(preview.summary.formulas)){
          const f=this.el('div',{class:'structure-profile-formula'});f.append(this.el('span',{class:'structure-formula-label'},item.label||'Формула'));
          const math=this.el('div');globalThis.MathPresentation.formula(math,item.tex,{display:true});f.append(math);formulas.append(f);
        }
        panel.append(formulas);
        if(array(preview.summary.assumptions).length)panel.append(this.math('p',preview.summary.assumptions.map(a=>a.replace(/\.$/,'')).join('; ')+'.',{class:'structure-math-conditions'}));
      }else{const pattern=this.el('div',{class:'structure-pattern'});for(const[title,value]of preview.steps){const step=this.el('div');step.append(this.el('h4',{},title),this.math('p',value||'Пока не предложено'));pattern.append(step);}panel.append(pattern,this.el('p',{class:'research-hint'},'Это интерпретация модели для поиска соответствий. Проверяется выбранная общая структура в отдельном запуске.'));}
      const full=this.el('details');full.append(this.el('summary',{},fromArticle?'Полный профиль и условия предложения':'Полный профиль, условия и исходная Lean-теорема'));
      if(preview.known){for(const [title,items]of [['Условия исходной теоремы',preview.summary.assumptions],['Границы исходного результата',preview.summary.limitations]]){if(array(items).length){full.append(this.el('h5',{},title));for(const item of items)full.append(this.math('p',item));}}}
      if(profile.summary)full.append(this.math('p',profile.summary));
      const dl=this.el('dl');for(const[key,title]of [['objects','Объекты'],['operations','Операции'],['assumptions','Предпосылки'],['conclusion_shape','Форма вывода'],['mechanism','Предполагаемый механизм']]){
        if(profile[key]&&(!Array.isArray(profile[key])||profile[key].length))dl.append(this.el('dt',{},title),this.math('dd',Array.isArray(profile[key])?profile[key].join('; '):profile[key]));
      }
      full.append(dl);if(profile.formal)full.append(this.details('Зафиксированное утверждение и аксиомы',profile.formal));panel.append(full);return panel;
    }
    renderRoute(route,index,count){
      const card=this.el('section',{class:'structure-route','data-structure-route':route?.id||'route_'+(index+1)}),names={pending:'Ожидает поиска',searched:'Источники найдены',complete:'Поиск завершён',failed:'Ошибка поиска'};
      const header=this.el('div',{class:'structure-route-header'});header.append(this.el('span',{class:'research-small-label'},'Направление '+(index+1)),this.el('span',{class:'research-status '+(route?.status==='failed'?'failed':'unknown')},names[route?.status]||'Ожидает профиля'));
      card.append(header,this.math('h4',excerpt(routeTitle(route),110)));
      if(route?.rationale)card.append(this.math('p',route.rationale,{class:'structure-route-rationale'}));
      if(route?.msc_code){const button=this.el('button',{type:'button',class:'text-button'},'MSC '+route.msc_code+' ↗');button.onclick=()=>this.callbacks.onMSC?.(route.msc_code);card.append(button);}
      card.append(this.el('p',{class:'structure-route-count'},'Кандидатов: '+count+' · источников: '+array(route?.hits).length));
      if(route){
        const full=this.el('details');full.append(this.el('summary',{},'Почему эта область · запросы и источники'));
        if(route.title)full.append(this.math('p',route.title));if(route.rationale)full.append(this.math('p',route.rationale));
        if(array(route.queries).length){full.append(this.el('h5',{},'Поисковые запросы'));const ul=this.el('ul');for(const query of route.queries)ul.append(this.math('li',query));full.append(ul);}
        if(array(route.hits).length){full.append(this.el('h5',{},'Найденные источники'));for(const hit of route.hits)full.append(this.sourceEvidence(hit));}
        card.append(full);
        if(route.status==='complete'&&!count)card.append(this.el('p',{class:'research-hint'},'Кандидат не предложен. Это не доказывает отсутствие связи.'));
      }
      return card;
    }
    renderCandidate(candidate,run){
      const transition=candidate.transition,state=candidateStatus(transition,globalThis.ObjectGraphModel),selected=this.selected===candidate.transition_id;
      const summary=globalThis.MathPresentation?.entitySummary?.(run,'transition',transition);
      const card=this.el('article',{class:'structure-candidate'+(selected?' selected':''),'data-structure-candidate':candidate.transition_id});
      const header=this.el('div',{class:'structure-candidate-header'});header.append(this.el('span',{class:'research-small-label'},Number.isFinite(candidate.rank)?'Место '+candidate.rank+' в этом направлении':'Без позиции в этом направлении'));
      header.append(this.el('span',{class:'structure-candidate-status','data-status':state.status||'incomplete'},state.label||'Статус проверки недоступен'));
      card.append(header,this.math('h4',summary?.title||candidate.title||transition.title));
      if(summary){
        if(summary.description)card.append(this.math('p',summary.description));
        const item=array(summary.formulas).at(-1);if(item?.tex){const f=this.el('div',{class:'structure-candidate-formula'});globalThis.MathPresentation.formula(f,item.tex,{display:true});card.append(f);}
      }else card.append(this.el('p',{class:'research-hint'},'Выберите связь на карте, чтобы рассмотреть её объекты, условия и исходную формулировку.'));
      const attempt=mapModel()?.priorAttempt(run,transition,this.callbacks.getRuns?.()||[]),actions=this.el('div',{class:'structure-candidate-actions'}),verify=this.el('button',{type:'button',class:'button primary'},attempt?attempt.label:'Проверить общую структуру в Lean');
      verify.disabled=attempt?!this.callbacks.onOpenRun:active.has(run.status)||!this.callbacks.onVerify;verify.onclick=()=>attempt?this.callbacks.onOpenRun?.(attempt.runId):this.callbacks.onVerify?.(run.object_graph,transition);
      const inspect=this.el('button',{type:'button',class:'button secondary','aria-pressed':String(selected)},'Показать на карте');
      inspect.onclick=()=>{this.selected=candidate.transition_id;this.callbacks.onSelect?.(transition);this.resultKey='';this.render(run,true);};actions.append(verify,inspect);card.append(actions);
      const full=this.el('details');full.append(this.el('summary',{},'Полная формулировка и ограничения'));
      if(candidate.title||transition.title)full.append(this.math('p',candidate.title||transition.title));
      if(candidate.rationale)full.append(this.math('p',candidate.rationale));
      if(transition.claim){full.append(this.el('h5',{},'Утверждение перехода'),this.math('p',transition.claim));}
      if(transition.construction)full.append(this.el('h5',{},'Конструкция'),this.math('p',transition.construction));
      for(const[title,items]of [['Предпосылки',array(transition.assumptions)],['Ограничения предложения',array(candidate.limitations)]]){
        if(items.length){full.append(this.el('h5',{},title));const ul=this.el('ul');for(const item of items)ul.append(this.math('li',item));full.append(ul);}
      }
      card.append(full);
      if(array(candidate.evidence).length){const details=this.el('details');details.append(this.el('summary',{},'Основания и оригиналы источников · '+candidate.evidence.length));for(const evidence of candidate.evidence)details.append(this.sourceEvidence(evidence));card.append(details);}
      const formal=this.el('details');formal.append(this.el('summary',{},'Lean-постановка и результат проверки'));
      if(transition.agent_task){formal.append(this.details('Точное задание Lean',transition.agent_task));for(const obligation of array(transition.obligations))formal.append(this.details(obligation.title||obligation.id||'Обязательство',obligation));}
      else formal.append(this.el('p',{},'Lean-постановка ещё не подготовлена. Проверка начнётся с формализации этой связи.'));
      if(transition.semantic_review)formal.append(this.details('Смысловая рецензия',transition.semantic_review));
      if(transition.certificate)formal.append(this.details('Сохранённый сертификат',transition.certificate));
      if(transition.last_result&&!transition.certificate)formal.append(this.details('Последняя попытка проверки',transition.last_result));
      card.append(formal);return card;
    }
    selectCandidate(id){
      this.selected=id;
      for(const card of this.$('structure-results').querySelectorAll('[data-structure-candidate]')){
        const selected=card.dataset.structureCandidate===id;card.classList.toggle('selected',selected);
        card.querySelector('[aria-pressed]')?.setAttribute('aria-pressed',String(selected));
      }
    }
    render(run,enabled){
      const box=this.$('structure-results');box.hidden=!enabled&&run?.purpose!=='structure';if(box.hidden){this.resultKey='';return;}
      if(this.runId!==run?.id){this.runId=run?.id;this.selected=null;}
      const key=JSON.stringify([run?.id,run?.status,run?.structure_profile,run?.structure_routes,run?.object_graph,sourceTransition(run),this.callbacks.getRuns?.(),this.selected]);if(key===this.resultKey)return;this.resultKey=key;box.replaceChildren();
      const intro=this.el('div',{class:'structure-intro'});intro.append(this.el('h3',{},run?.purpose==='structure'?searchSummary(run):'Теорема → три области → общая структура'),this.el('p',{},'Сравните направления и выберите связь для проверки. Поиск предлагает кандидатов; Lean проверяет выбранное утверждение в отдельном запуске.'));box.append(intro);
      if(!run||run.purpose!=='structure'){box.append(this.el('p',{class:'structure-empty'},'Проверьте Lean-источник, выберите теорему и задайте бюджет. Astra составит профиль доказательства и исследует три направления MSC.'));return;}
      const origin=this.renderSourceTransition(run);if(origin)box.append(origin);
      if(!active.has(run.status)&&run.status!=='complete'&&(run.error||run.result?.error))box.append(this.el('p',{class:'structure-empty',role:'status'},'Поиск остановлен: '+text(run.error||run.result.error)));
      const profile=run.structure_profile;
      if(profile)box.append(this.renderProfile(profile,run));
      else box.append(this.el('p',{class:'structure-empty'},active.has(run.status)?(origin?'Astra составляет структурный профиль исходного перехода.':'Astra составляет структурный профиль теоремы.'):'Структурный профиль пока не получен.'));
      box.append(this.el('h3',{},'Три направления поиска'));
      const groups=candidateGroups(run),routes=this.el('div',{class:'structure-routes'});
      for(let i=0;i<3;i++){
        const card=this.renderRoute(array(run.structure_routes)[i],i,groups[i]?.candidates.length||0);
        for(const candidate of groups[i]?.candidates||[])card.append(this.renderCandidate(candidate,run));
        routes.append(card);
      }
      box.append(routes);
      const candidates=groups.flatMap(group=>group.candidates);
      if(!candidates.length)box.append(this.el('p',{class:'structure-empty'},active.has(run.status)?'Кандидаты появятся по мере завершения направлений.':'Кандидатов с сохранённой постановкой нет. Посмотрите источники и журнал; отсутствие предложения не является опровержением.'));
    }
  }
  return {ready,theorems,selectedTarget,payload,candidateGroups,rankedCandidates,excerpt,searchSummary,candidateStatus,renderMath,profilePreview,routeTitle,sourceTransition,Workspace};
});
