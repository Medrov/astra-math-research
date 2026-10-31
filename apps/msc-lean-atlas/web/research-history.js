'use strict';

(function(root,factory){const api=factory();if(typeof module==='object'&&module.exports)module.exports=api;else root.ResearchHistory=api;})(typeof window==='undefined'?globalThis:window,()=>{
  const text=value=>typeof value==='string'?value.trim():'';
  const array=value=>Array.isArray(value)?value:[];
  const finished=new Set(['complete','completed']);
  const searching=run=>run.purpose==='structure'||run.purpose==='discover';
  const localGuided=typeof module==='object'&&module.exports?require('./guided-research.js'):null,guided=()=>globalThis.GuidedResearch||localGuided;
  let serial=0;

  function statusOf(run){
    const search=searching(run);
    if(run.status==='queued')return {kind:'active',label:'В очереди'};
    if(run.status==='running')return {kind:'active',label:search?'Идёт поиск':'Идёт проверка'};
    if(run.status==='cancelling')return {kind:'active',label:'Сохраняем и останавливаем'};
    if(!search&&run.formal_outcome==='proved'&&(!finished.has(run.status)||!['proved','refuted'].includes(run.outcome)))return {kind:'formal',label:'Lean-цель проверена · '+(finished.has(run.status)?'смысл не подтверждён':guided()?.terminationInfo(run)?.title||'запуск прерван')};
    const termination=guided()?.terminationInfo(run);if(termination)return {kind:'incomplete',label:termination.title};
    if(run.status==='cancelled')return {kind:'incomplete',label:'Остановлено'};
    if(run.status==='interrupted')return {kind:'incomplete',label:'Запуск прерван'};
    if(run.status==='budget_exhausted')return {kind:'incomplete',label:'Достигнут лимит'};
    if(run.status==='failed'||run.status==='timeout')return {kind:'incomplete',label:search?'Поиск не завершён':'Проверка не завершена'};
    if(finished.has(run.status)&&search)return {kind:'search',label:'Поиск завершён'};
    // A list summary is not a verifier report. These labels describe the saved
    // result; the opened run remains the place to inspect its exact certificate.
    if(finished.has(run.status)&&run.outcome==='proved')return {kind:'result',label:'Есть результат Lean'};
    if(finished.has(run.status)&&run.outcome==='refuted')return {kind:'result',label:'Отрицательная цель проверена'};
    if(finished.has(run.status)&&run.formal_outcome==='proved')return {kind:'formal',label:'Lean-цель проверена · смысл не подтверждён'};
    if(run.status==='needs_review')return {kind:'incomplete',label:'Нужно уточнить постановку'};
    return {kind:'incomplete',label:search?'Поиск ещё не завершён':'Связь пока не подтверждена'};
  }

  function summaryOf(run){
    const kind=run.purpose==='structure'?'Поиск общей структуры':run.purpose==='discover'?'Поиск по источнику':'Проверка связи';
    let title=text(run.display_title)||text(run.title)||kind;
    if(!text(run.display_title)&&/^Найти общую структуру для Lean-теоремы\s+/u.test(title))title='Поиск общей структуры';
    // Only explicit metadata is used. case_id / graph_ref / target names are
    // never guessed into a paper name or scientific description.
    const source=text(run.source_title);
    const rawDate=text(run.created_at),date=rawDate?new Date(rawDate):null;
    const valid=date&&Number.isFinite(date.getTime());
    return {id:run.id,title,source,kind,status:statusOf(run),
      date:valid?new Intl.DateTimeFormat('ru-RU',{day:'numeric',month:'long',year:'numeric',hour:'2-digit',minute:'2-digit'}).format(date):'Дата не сохранена',
      datetime:valid?date.toISOString():'',
      searchable:[title,text(run.title),source].join(' ')};
  }

  function matches(summary,query){
    const normalize=value=>String(value).normalize('NFKC').toLocaleLowerCase('ru-RU').replaceAll('ё','е');
    const haystack=normalize(summary.searchable);
    return normalize(query).trim().split(/\s+/u).filter(Boolean).every(word=>haystack.includes(word));
  }

  class Workspace {
    constructor({container,onOpen,onError}={}){
      if(!container?.ownerDocument||typeof onOpen!=='function')throw new TypeError('HistoryWorkspace requires a container and onOpen callback.');
      this.doc=container.ownerDocument;this.onOpen=onOpen;this.onError=onError;
      this.rows=new Map();this.runs=[];this.currentId=null;this.pendingId=null;this.session=0;this.returnFocus=null;
      const key='research-history-'+(++serial);
      this.dialog=this.el('dialog','research-history');this.dialog.setAttribute('aria-labelledby',key+'-title');
      this.dialog.setAttribute('aria-describedby',key+'-description');
      const header=this.el('header','research-history-header'),heading=this.el('div');
      const title=this.el('h2','','История');title.id=key+'-title';
      const description=this.el('p','research-history-description','Сохранённые поиски и проверки. Выберите запись, чтобы продолжить просмотр.');description.id=key+'-description';
      heading.append(title,description);
      this.closeButton=this.el('button','research-history-close','Закрыть');this.closeButton.type='button';
      this.closeButton.setAttribute('aria-label','Закрыть историю');this.closeButton.addEventListener('click',()=>this.hide());
      header.append(heading,this.closeButton);
      const tools=this.el('div','research-history-tools'),label=this.el('label','','Найти в истории');label.htmlFor=key+'-search';
      this.search=this.el('input','research-history-search');this.search.type='search';this.search.id=key+'-search';
      this.search.placeholder='Название или источник';this.search.autocomplete='off';
      this.count=this.el('p','research-history-count');this.count.setAttribute('role','status');this.count.setAttribute('aria-live','polite');this.count.setAttribute('aria-atomic','true');
      this.error=this.el('p','research-history-error');this.error.setAttribute('role','alert');this.error.hidden=true;
      tools.append(label,this.search,this.count,this.error);
      this.scroll=this.el('div','research-history-scroll');
      this.list=this.el('ul','research-history-list');this.list.setAttribute('aria-label','Сохранённые исследования');
      this.empty=this.el('p','research-history-empty');this.empty.hidden=true;
      this.scroll.append(this.list,this.empty);this.dialog.append(header,tools,this.scroll);container.append(this.dialog);
      this.search.addEventListener('input',()=>{this.updateVisibility();this.scroll.scrollTop=0;});
      this.dialog.addEventListener('cancel',event=>{event.preventDefault();this.hide();});
      this.dialog.addEventListener('close',()=>this.restoreFocus());
      this.dialog.addEventListener('click',event=>{
        if(event.target!==this.dialog)return;
        const rect=this.dialog.getBoundingClientRect();
        if(event.clientX<rect.left||event.clientX>rect.right||event.clientY<rect.top||event.clientY>rect.bottom)this.hide();
      });
      this.render([],null);
    }

    el(tag,className='',value){const node=this.doc.createElement(tag);if(className)node.className=className;if(value!==undefined)node.textContent=value;return node;}

    createRow(id){
      const item=this.el('li','research-history-row'),button=this.el('button','research-history-card');button.type='button';
      const top=this.el('span','research-history-card-top'),kind=this.el('span','research-history-kind');
      const current=this.el('span','research-history-current','Сейчас открыто');current.hidden=true;top.append(kind,current);
      const title=this.el('strong','research-history-title'),source=this.el('span','research-history-source');
      const meta=this.el('span','research-history-meta'),status=this.el('span','research-history-status'),date=this.el('time','research-history-date');
      meta.append(status,date);button.append(top,title,source,meta);item.append(button);
      button.addEventListener('click',()=>this.open(id));
      return {item,button,kind,current,title,source,status,date,summary:null};
    }

    render(runs,currentId){
      const focus=this.doc.activeElement,position=this.scroll.scrollTop;
      const focusedRow=[...this.rows.entries()].find(([,row])=>row.button===focus)?.[0];
      this.currentId=currentId;const seen=new Set();
      this.runs=array(runs).filter(run=>run&&typeof run.id==='string'&&run.id&&!seen.has(run.id)&&seen.add(run.id));
      for(const [id,row]of this.rows)if(!seen.has(id)){row.item.remove();this.rows.delete(id);}
      for(let index=0;index<this.runs.length;index++){
        const run=this.runs[index],summary=summaryOf(run);let row=this.rows.get(run.id);
        if(!row){row=this.createRow(run.id);this.rows.set(run.id,row);}
        row.summary=summary;
        row.title.textContent=summary.title;row.kind.textContent=summary.kind;
        row.source.textContent=summary.source?'Источник: '+summary.source:'';row.source.hidden=!summary.source;
        row.status.textContent=summary.status.label;row.status.dataset.kind=summary.status.kind;
        row.date.textContent=summary.date;if(summary.datetime)row.date.setAttribute('datetime',summary.datetime);else row.date.removeAttribute('datetime');
        row.current.hidden=run.id!==currentId;
        row.button.dataset.current=String(run.id===currentId);
        if(run.id===currentId)row.button.setAttribute('aria-current','page');else row.button.removeAttribute('aria-current');
        if(this.list.children[index]!==row.item)this.list.insertBefore(row.item,this.list.children[index]||null);
      }
      this.updateVisibility();this.updatePending();
      if(focusedRow){
        const row=this.rows.get(focusedRow);
        if(row&&!row.item.hidden){if(this.doc.activeElement!==row.button)row.button.focus({preventScroll:true});}
        else this.search.focus({preventScroll:true});
      }
      this.scroll.scrollTop=position;
    }

    updateVisibility(){
      let visible=0;
      for(const row of this.rows.values()){row.item.hidden=!matches(row.summary,this.search.value);if(!row.item.hidden)visible++;}
      const total=this.rows.size;
      const count=this.search.value.trim()?'Найдено: '+visible+' из '+total:'Сохранено: '+total;
      if(this.count.textContent!==count)this.count.textContent=count;
      this.empty.hidden=visible!==0;
      this.empty.textContent=total?'Ничего не найдено. Попробуйте другое название или источник.':'Здесь появятся ваши поиски и проверки.';
    }

    updatePending(){
      this.list.setAttribute('aria-busy',String(this.pendingId!==null));
      for(const [id,row]of this.rows){
        row.button.setAttribute('aria-disabled',String(this.pendingId!==null));
        row.button.dataset.loading=String(id===this.pendingId);
        if(id===this.pendingId)row.status.textContent='Открываем…';
        else row.status.textContent=row.summary.status.label;
      }
    }

    async open(id){
      if(this.pendingId!==null||!this.rows.has(id))return;
      this.pendingId=id;const session=this.session;this.error.hidden=true;this.error.textContent='';this.updatePending();
      try{await this.onOpen(id);if(this.session===session)this.hide();}
      catch(error){
        this.error.textContent='Не удалось открыть исследование. Попробуйте ещё раз.';this.error.hidden=false;
        if(typeof this.onError==='function'){try{this.onError(error);}catch(_){/* The local error remains readable. */}}
      }finally{this.pendingId=null;this.updatePending();}
    }

    show(){
      if(this.dialog.open)return;
      this.returnFocus=this.doc.activeElement;this.session++;this.dialog.showModal();this.search.focus({preventScroll:true});
    }

    hide(){if(this.dialog.open)this.dialog.close();this.restoreFocus();}
    restoreFocus(){const node=this.returnFocus;this.returnFocus=null;if(node?.isConnected&&typeof node.focus==='function')node.focus({preventScroll:true});}
  }
  return {Workspace,summaryOf,statusOf,matches};
});
