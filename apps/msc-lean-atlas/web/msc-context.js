'use strict';

(function(root,factory){const api=factory();if(typeof module==='object'&&module.exports)module.exports=api;else root.MSCContext=api;})(typeof window==='undefined'?globalThis:window,()=>{
  const list=value=>Array.isArray(value)?value:[];
  const codes=value=>[...new Set(list(value).filter(code=>typeof code==='string'&&code.trim()).map(code=>code.trim()))];

  // UI translations are selected only by the exact code AND official wording
  // from the local MSC2020 catalog. Unlisted or changed wording stays verbatim.
  const translations=Object.freeze({
    '13':['Commutative algebra','Коммутативная алгебра'],
    '14':['Algebraic geometry','Алгебраическая геометрия'],
    '37':['Dynamical systems and ergodic theory','Динамические системы и эргодическая теория'],
    '34':['Ordinary differential equations','Обыкновенные дифференциальные уравнения'],
    '34B':['Boundary value problems for ordinary differential equations','Краевые задачи для обыкновенных дифференциальных уравнений'],
    '34B24':['Sturm-Liouville theory','Теория Штурма — Лиувилля'],
    '53':['Differential geometry','Дифференциальная геометрия'],
    '53A':['Classical differential geometry','Классическая дифференциальная геометрия'],
    '53A10':['Minimal surfaces in differential geometry, surfaces with prescribed mean curvature','Минимальные поверхности в дифференциальной геометрии, поверхности с заданной средней кривизной'],
    '53C':['Global differential geometry','Глобальная дифференциальная геометрия'],
    '53C42':['Differential geometry of immersions (minimal, prescribed curvature, tight, etc.)','Дифференциальная геометрия погружений'],
    '58':['Global analysis, analysis on manifolds','Глобальный анализ, анализ на многообразиях'],
    '58J':['Partial differential equations on manifolds; differential operators','Дифференциальные уравнения в частных производных на многообразиях; дифференциальные операторы'],
    '58J50':['Spectral problems; spectral geometry; scattering theory on manifolds','Спектральные задачи; спектральная геометрия; теория рассеяния на многообразиях']
  });
  const uiTitle=(code,title)=>Object.hasOwn(translations,code)&&translations[code][0]===title?translations[code][1]:title;

  function itemFor(code,lookup){
    let descriptor=null;
    if(typeof lookup==='function'){try{descriptor=lookup(code);}catch(_){/* Missing local metadata does not create a classification. */}}
    if(!descriptor||descriptor.code!==code||typeof descriptor.title!=='string'||!descriptor.title.trim()){
      return {code,title:typeof lookup==='function'?'Рубрика не найдена в локальном MSC2020':'Название рубрики недоступно',officialTitle:'',path:[],known:false};
    }
    // Never reconstruct hierarchy by slicing the code or interpreting a title.
    const path=list(descriptor.path).filter(part=>part&&typeof part.code==='string'&&part.code&&typeof part.title==='string'&&part.title.trim())
      .map(part=>({code:part.code,title:uiTitle(part.code,part.title)}));
    return {code,title:uiTitle(code,descriptor.title),officialTitle:descriptor.title,path,known:true};
  }

  function transitionContext(run,transition){
    if(!transition||typeof transition!=='object')return null;
    const own=codes(transition.msc_codes);
    if(own.length)return {origin:'explicit',label:'Рубрики узла',codes:own};
    if(typeof transition.id==='string'&&transition.id){
      const routeCodes=codes(list(run?.structure_routes).filter(route=>list(route?.candidates).some(candidate=>candidate?.transition_id===transition.id))
        .flatMap(route=>typeof route.msc_code==='string'?[route.msc_code]:[]));
      if(routeCodes.length)return {origin:'route',label:'Область маршрута поиска',codes:routeCodes};
    }
    const refs=new Set([...list(transition.source_ids),...list(transition.target_ids)].filter(ref=>typeof ref==='string'));
    const related=codes(list(run?.object_graph?.objects).filter(object=>object&&refs.has(object.id)).flatMap(object=>list(object.msc_codes)));
    return related.length?{origin:'related_objects',label:'По связанным объектам',codes:related}:null;
  }

  function forNode(run,node,lookup){
    const value=node?.value;
    let context=null;
    const own=codes(value?.msc_codes);
    if(own.length)context={origin:'explicit',label:'Рубрики узла',codes:own};
    else if(node?.kind==='transition')context=transitionContext(run,value);
    else if(node?.kind==='proof'){
      const selected=typeof run?.selected_transition_id==='string'?list(run?.object_graph?.transitions).find(transition=>transition?.id===run.selected_transition_id):null;
      const inherited=transitionContext(run,selected);
      if(inherited)context={origin:'selected_transition',label:'Область проверяемого перехода',codes:inherited.codes};
    }
    if(!context){
      const graphCodes=codes(run?.object_graph?.msc_codes),savedCodes=graphCodes.length?graphCodes:codes(run?.msc_codes);
      if(savedCodes.length)context={origin:'research',label:'Области исследования',codes:savedCodes};
    }
    if(!context)return {origin:'none',label:'Рубрика не указана',items:[]};
    return {origin:context.origin,label:context.label,items:context.codes.map(code=>itemFor(code,lookup))};
  }
  return {forNode};
});
