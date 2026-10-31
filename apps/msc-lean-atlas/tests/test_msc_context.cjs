const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const vm=require('node:vm');
const {forNode}=require('../web/msc-context.js');
const catalog=JSON.parse(fs.readFileSync(require.resolve('../data/msc2020.json'),'utf8'));
const byCode=new Map(catalog.nodes.map(node=>[node.id,node]));
function lookup(code){
  const node=byCode.get(code);if(!node)return null;
  const path=[],seen=new Set();let current=node;
  while(current&&!seen.has(current.id)){seen.add(current.id);path.unshift({code:current.id,title:current.title,parent_id:current.parent_id});current=byCode.get(current.parent_id);}
  return {code:node.id,title:node.title,parent_id:node.parent_id,path};
}
const node=(kind,value)=>({kind,value});
const codes=result=>result.items.map(item=>item.code);
function deepFreeze(value){if(value&&typeof value==='object'&&!Object.isFrozen(value)){Object.freeze(value);for(const part of Object.values(value))deepFreeze(part);}return value;}

// Thin metadata snapshots read from the retained local runs. They contain no
// expected proof status and remain portable without ignored research_data/.
const frolov={msc_codes:[],structure_routes:[
  {msc_code:'13',candidates:[{transition_id:'route_1_base_change'}]},
  {msc_code:'14',candidates:[{transition_id:'route_2_graph_quotient_bridge'}]},
  {msc_code:'37',candidates:[{transition_id:'route_3_polynomial_conjugacy'}]}
],object_graph:{msc_codes:['13','14','37'],objects:[
  {id:'input_object',title:'Исходная Lean-теорема: Arxiv261038474.subtract_restore',msc_codes:[]},
  {id:'route_1_input_object',msc_codes:['13']},{id:'route_1_coefficient_map',msc_codes:['13']},{id:'route_1_changed_coordinates',msc_codes:['13']},
  {id:'route_2_input',msc_codes:['14']},{id:'route_2_ideals',msc_codes:['14']},{id:'route_2_substitution',msc_codes:['14']},{id:'route_2_quotient',msc_codes:['14']},
  {id:'route_3_input',msc_codes:['37']},{id:'route_3_coordinates',msc_codes:['37']},{id:'route_3_dynamics',msc_codes:['37']}
],transitions:[
  {id:'route_1_base_change',source_ids:['input_object','route_1_input_object','route_1_coefficient_map'],target_ids:['route_1_changed_coordinates']},
  {id:'route_2_graph_quotient_bridge',source_ids:['input_object','route_2_input','route_2_ideals'],target_ids:['route_2_substitution','route_2_quotient']},
  {id:'route_3_polynomial_conjugacy',source_ids:['input_object','route_3_input'],target_ids:['route_3_coordinates','route_3_dynamics']}
]}};
const catenoid={msc_codes:['34B24','53A10','53C42','58J50'],object_graph:{msc_codes:['34B24','53A10','53C42','58J50'],objects:[
  {id:'profile',title:'Радиальный профиль',msc_codes:['53A10']},
  {id:'immersion',title:'Параметризованный сферический катеноид',msc_codes:['53A10','53C42']},
  {id:'truncation',title:'Катеноид со свободной границей',msc_codes:['53A10','53C42']},
  {id:'jacobi',title:'Форма второй вариации и оператор Якоби',msc_codes:['53C42','58J50']},
  {id:'radial',title:'Радиальные задачи Робена',msc_codes:['34B24','58J50']},
  {id:'wronskian',title:'Вронскиан радиальных функций',msc_codes:['34B24','53A10']},
  {id:'conformal',title:'Радиальная задача в конформальной координате',msc_codes:['34B24','58J50']},
  {id:'rotations',title:'Нормальные компоненты вращений',msc_codes:['53C42','58J50']}
],transitions:[
  {id:'geometry',source_ids:['profile'],target_ids:['immersion']},
  {id:'free_boundary',source_ids:['profile','immersion'],target_ids:['truncation']},
  {id:'separation',source_ids:['immersion','truncation'],target_ids:['jacobi','radial']},
  {id:'boundary_inequality',source_ids:['profile','truncation','radial'],target_ids:['wronskian']},
  {id:'coordinate_change',source_ids:['profile','truncation','radial'],target_ids:['conformal']},
  {id:'kernel_rotations',source_ids:['immersion','truncation','jacobi','radial'],target_ids:['rotations']}
]}};

test('explicit node rubrics win, deduplicate and retain official catalog titles',()=>{
  const r=forNode(frolov,node('transition',{...frolov.object_graph.transitions[0],msc_codes:['34B24','34B24',' 53A10 ']}),lookup);
  assert.equal(r.origin,'explicit');assert.equal(r.label,'Рубрики узла');assert.deepEqual(codes(r),['34B24','53A10']);
  assert.equal(r.items[0].title,'Теория Штурма — Лиувилля');assert.equal(r.items[0].officialTitle,'Sturm-Liouville theory');assert.ok(r.items.every(item=>item.known));
});

test('exact route candidate reference supplies context; IDs, titles and prefixes never classify',()=>{
  const transition=frolov.object_graph.transitions[2];const r=forNode(frolov,node('transition',transition),lookup);
  assert.equal(r.origin,'route');assert.equal(r.label,'Область маршрута поиска');assert.deepEqual(codes(r),['37']);
  const misleading={id:'route_3_polynomial_conjugacy_extra',title:'MSC 37 Dynamical systems',source_ids:[],target_ids:[]};
  assert.equal(forNode({...frolov,object_graph:{objects:[],transitions:[]}},node('transition',misleading),lookup).origin,'none');
  assert.equal(forNode({},node('object',{id:'53A10',title:'Minimal surfaces'}),lookup).origin,'none');
});

test('multiple exact route references are merged without unrelated route rubrics',()=>{
  const run={structure_routes:[{msc_code:'13',candidates:[{transition_id:'chosen'}]},{msc_code:'14',candidates:[{transition_id:'chosen'}]},{msc_code:'13',candidates:[{transition_id:'chosen'}]},{msc_code:'37',candidates:[{transition_id:'other'}]}]};
  assert.deepEqual(codes(forNode(run,node('transition',{id:'chosen'}),lookup)),['13','14']);
});

test('transition fallback uses only explicit codes of its own source and target objects',()=>{
  const run={object_graph:{msc_codes:['37'],objects:[{id:'a',msc_codes:['13']},{id:'b',msc_codes:['14','13']},{id:'other',msc_codes:['34']}],transitions:[]}};
  const r=forNode(run,node('transition',{source_ids:['a','a','missing'],target_ids:['b']}),lookup);
  assert.equal(r.origin,'related_objects');assert.equal(r.label,'По связанным объектам');assert.deepEqual(codes(r),['13','14']);
  assert.equal(forNode(run,node('transition',{source_ids:['missing'],target_ids:[]}),lookup).origin,'research');
});

test('proof without explicit codes inherits selected transition context, never its own classification',()=>{
  const run={...frolov,selected_transition_id:'route_3_polynomial_conjugacy'};
  const r=forNode(run,node('proof',{target:'Route3.coordinate_conjugacy'}),lookup);
  assert.equal(r.origin,'selected_transition');assert.equal(r.label,'Область проверяемого перехода');assert.deepEqual(codes(r),['37']);
  assert.equal(forNode(run,node('proof',{msc_codes:['13']}),lookup).origin,'explicit');
  const missing=forNode({...run,selected_transition_id:'not-present'},node('proof',{}),lookup);
  assert.equal(missing.origin,'research');assert.deepEqual(codes(missing),['13','14','37']);
});

test('research fallback prefers saved graph context, then run; empty input is explicitly unclassified',()=>{
  assert.deepEqual(codes(forNode({msc_codes:['13'],object_graph:{msc_codes:['14']}},node('object',{}),lookup)),['14']);
  const fromRun=forNode({msc_codes:['13']},node('object',{}),lookup);assert.equal(fromRun.label,'Области исследования');assert.deepEqual(codes(fromRun),['13']);
  assert.deepEqual(forNode({},node('object',{}),lookup),{origin:'none',label:'Рубрика не указана',items:[]});
  assert.deepEqual(forNode(null,null,lookup),{origin:'none',label:'Рубрика не указана',items:[]});
});

test('unknown code is preserved; no root or title is invented from code shape',()=>{
  const r=forNode({},node('object',{msc_codes:['53ZZZ','53C42']}),lookup);
  assert.equal(r.origin,'explicit');assert.equal(r.items[0].code,'53ZZZ');assert.equal(r.items[0].known,false);assert.equal(r.items[0].officialTitle,'');assert.deepEqual(r.items[0].path,[]);
  assert.equal(r.items[1].officialTitle,byCode.get('53C42').title);
  assert.equal(r.items[1].title,'Дифференциальная геометрия погружений');
  const missing=forNode({},node('object',{msc_codes:['13']}));assert.equal(missing.items[0].known,false);assert.equal(missing.items[0].title,'Название рубрики недоступно');
  assert.equal(forNode({},node('object',{msc_codes:['13']}),()=>({code:'14',title:'Algebraic geometry'})).items[0].known,false);
});

test('hierarchy comes verbatim from supplied catalog path and exact parent links',()=>{
  const r=forNode({},node('object',{msc_codes:['34B24','58J50']}),lookup);
  assert.deepEqual(r.items[0].path.map(p=>p.code),['34','34B','34B24']);assert.equal(r.items[0].path[0].title,'Обыкновенные дифференциальные уравнения');
  assert.deepEqual(r.items[1].path.map(p=>p.code),['58','58J','58J50']);
  const unusual=forNode({},node('object',{msc_codes:['53A10']}),code=>({code,title:'Different category',parent_id:'34',path:[{code:'34',title:'Ordinary differential equations'}]}));
  assert.deepEqual(unusual.items[0].path,[{code:'34',title:'Обыкновенные дифференциальные уравнения'}]);
});

test('Russian UI translations require unchanged official wording; remaining catalog stays English',()=>{
  const examples=['13','14','37','34','34B','34B24','53','53A','53A10','53C','53C42','58','58J','58J50'];
  for(const code of examples){
    const result=forNode({},node('object',{msc_codes:[code]}),lookup).items[0];assert.notEqual(result.title,result.officialTitle);assert.equal(result.officialTitle,byCode.get(code).title);
    const changed=forNode({},node('object',{msc_codes:[code]}),id=>({...lookup(id),title:'Changed: '+byCode.get(id).title})).items[0];assert.equal(changed.title,changed.officialTitle);
  }
  const other=forNode({},node('object',{msc_codes:['11']}),lookup).items[0];assert.equal(other.title,'Number theory');
});

test('real retained Frolov map keeps three separate route contexts and input-wide scope',()=>{
  for(const [i,transition]of frolov.object_graph.transitions.entries()){
    const r=forNode(frolov,node('transition',transition),lookup);assert.equal(r.origin,'route');assert.deepEqual(codes(r),[['13'],['14'],['37']][i]);
  }
  const input=forNode(frolov,node('object',frolov.object_graph.objects[0]),lookup);assert.equal(input.origin,'research');assert.deepEqual(codes(input),['13','14','37']);
  const noRoutes={...frolov,structure_routes:[]};assert.deepEqual(codes(forNode(noRoutes,node('transition',frolov.object_graph.transitions[2]),lookup)),['37']);
});

test('real retained Catenoid map shows leaf rubrics and unions only related endpoint objects',()=>{
  for(const object of catenoid.object_graph.objects){const r=forNode(catenoid,node('object',object),lookup);assert.equal(r.origin,'explicit');assert.deepEqual(codes(r),object.msc_codes);assert.ok(r.items.every(item=>item.known&&item.path.length===3));}
  const geometry=forNode(catenoid,node('transition',catenoid.object_graph.transitions[0]),lookup);assert.equal(geometry.origin,'related_objects');assert.deepEqual(codes(geometry),['53A10','53C42']);
  const separation=forNode(catenoid,node('transition',catenoid.object_graph.transitions[2]),lookup);assert.deepEqual(codes(separation),['53A10','53C42','58J50','34B24']);
  const proof=forNode({...catenoid,selected_transition_id:'geometry'},node('proof',{id:'Geometry.goal'}),lookup);assert.equal(proof.origin,'selected_transition');assert.deepEqual(codes(proof),['53A10','53C42']);
});

test('pure API never mutates graph, node or lookup descriptors and exposes no result status',()=>{
  const run=deepFreeze(structuredClone(catenoid)),n=deepFreeze(node('object',run.object_graph.objects[0])),descriptor=deepFreeze(lookup('53A10'));
  const before=JSON.stringify({run,n,descriptor}),result=forNode(run,n,()=>descriptor);
  assert.equal(JSON.stringify({run,n,descriptor}),before);assert.deepEqual(Object.keys(result).sort(),['items','label','origin']);assert.deepEqual(Object.keys(result.items[0]).sort(),['code','known','officialTitle','path','title']);
  result.items[0].path[0].title='Changed UI';assert.notEqual(descriptor.path[0].title,'Changed UI');
});

test('UMD browser export works without DOM, network or application globals',()=>{
  const context={window:{}};vm.runInNewContext(fs.readFileSync(require.resolve('../web/msc-context.js'),'utf8'),context);
  assert.equal(typeof context.window.MSCContext.forNode,'function');assert.equal(context.window.MSCContext.forNode({},null).origin,'none');
});
