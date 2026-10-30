'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const Model = require('../web/graph-model.js');
const presentation = require('../web/graph-presentation.js');
const dataset = JSON.parse(fs.readFileSync(path.join(__dirname, '../data/msc2020.json'), 'utf8'));
const original = JSON.stringify(dataset);
const model = new Model(dataset);
const originalEdges = new Map(dataset.edges.map(edge => [edge.id, edge]));
const ids = graph => new Set(graph.nodes.map(node => node.data.id));
let passed = 0;

function check(name, test) {
  test();
  passed++;
  console.log('PASS ' + name);
}

check('Browser and CommonJS exports are constructors with the same interface', () => {
  const sandbox = {};
  vm.runInNewContext(fs.readFileSync(path.join(__dirname, '../web/graph-model.js'), 'utf8'), sandbox);
  assert.equal(typeof sandbox.MSCGraphModel, 'function');
  assert.equal(new sandbox.MSCGraphModel(dataset).elements().nodes.length, 598);
});

check('Overview contains exactly all 63 roots and 534 groups plus the virtual overview', () => {
  const graph = model.elements({mode: 'overview'});
  const expected = new Set(['__msc__', ...dataset.nodes.filter(node => node.level <= 1).map(node => node.id)]);
  assert.deepEqual(ids(graph), expected);
  assert.equal(graph.nodes.length, 598);
  assert.equal(graph.realNodeCount, 597);
  assert.equal(graph.edges.length, 597);
  assert.equal(graph.referenceCount, 0);
});

check('Full graph preserves every category, terminal code and official edge without pagination', () => {
  const graph = model.elements({mode: 'full', references: true});
  assert.equal(graph.nodes.length, 6604);
  assert.equal(graph.realNodeCount, 6603);
  assert.equal(graph.edges.length, 9872 + 63);
  assert.equal(graph.referenceCount, 3332);
  const nodeIds = ids(graph);
  for (const node of dataset.nodes) assert.ok(nodeIds.has(node.id), node.id);
  assert.equal(graph.nodes.filter(node => node.data.level === 2).length, 6006);
  assert.equal(new Set([...graph.nodes, ...graph.edges].map(element => element.data.id)).size, graph.nodes.length + graph.edges.length);
  for (const edge of graph.edges) {
    assert.ok(nodeIds.has(edge.data.source), edge.data.id);
    assert.ok(nodeIds.has(edge.data.target), edge.data.id);
  }
});

check('Original edges keep directions, qualifiers and exclusion types; only virtual overview edges are added', () => {
  const graph = model.elements({mode: 'full', references: true});
  for (const element of graph.edges) {
    const edge = element.data;
    if (edge.type === 'overview') {
      assert.equal(edge.target, '__msc__');
      assert.equal(model.nodeMap.get(edge.source).parent_id, null);
      assert.ok(!originalEdges.has(edge.id));
    } else {
      const source = originalEdges.get(edge.id);
      assert.ok(source, edge.id);
      assert.equal(edge.source, source.source);
      assert.equal(edge.target, source.target);
      assert.equal(edge.type, source.type);
      assert.equal(edge.reference_text, source.reference_text || '');
    }
  }
  for (const type of ['avoid_classification', 'classify_elsewhere', 'co_classify', 'classification_alternative', 'related_topic']) {
    assert.equal(graph.edges.filter(edge => edge.data.type === type).length, dataset.edges.filter(edge => edge.type === type).length);
  }
  const hierarchy = model.elements({mode: 'full', references: false});
  assert.equal(hierarchy.edges.length, 6540 + 63);
  assert.ok(hierarchy.edges.every(edge => ['broader', 'overview'].includes(edge.data.type)));
});

check('Focus on leaf 05C50 includes its 41 siblings/categories, group and ancestors without a twelve-node cap', () => {
  const graph = model.elements({mode: 'focus', focusId: '05C50'});
  const expected = new Set(['__msc__', '05', '05C', ...dataset.nodes.filter(node => node.parent_id === '05C').map(node => node.id)]);
  assert.deepEqual(ids(graph), expected);
  assert.equal(graph.focusId, '05C50');
  assert.equal(graph.nodes.length, 44);
  assert.ok(ids(graph).has('05C50'));
  assert.equal(graph.referenceCount, 0);
});

check('Largest branch preserves all 323 descendants including special hyphen categories', () => {
  const graph = model.elements({mode: 'focus', focusId: '35'});
  const expected = dataset.nodes.filter(node => node.id === '35' || node.id.startsWith('35'));
  assert.equal(expected.length, 323);
  assert.equal(graph.realNodeCount, 323);
  assert.deepEqual(ids(graph), new Set(['__msc__', ...expected.map(node => node.id)]));
  assert.ok(ids(graph).has('35-01'));
});

check('Focused references include exactly one incoming/outgoing hop from the branch core', () => {
  const without = model.elements({mode: 'focus', focusId: '05C50'});
  const expected = ids(without);
  const core = new Set(model.descendants('05C'));
  for (const edge of dataset.edges) {
    if (edge.type !== 'broader' && (core.has(edge.source) || core.has(edge.target))) {
      expected.add(edge.source);
      expected.add(edge.target);
    }
  }
  const graph = model.elements({mode: 'focus', focusId: '05C50', references: true});
  assert.deepEqual(ids(graph), expected);
  const sourceEdges = dataset.edges.filter(edge => expected.has(edge.source) && expected.has(edge.target));
  assert.deepEqual(new Set(graph.edges.filter(edge => edge.data.type !== 'overview').map(edge => edge.data.id)), new Set(sourceEdges.map(edge => edge.id)));
  assert.equal(graph.referenceCount, sourceEdges.filter(edge => edge.type !== 'broader').length);
});

check('Reference expansion is not recursive and preserves exclusion edges in a minimal witness', () => {
  const sample = new Model({
    nodes: [
      {id: 'R', code: 'R', title: 'Root', level: 0, parent_id: null},
      {id: 'G', code: 'G', title: 'Group', level: 1, parent_id: 'R'},
      {id: 'A', code: 'A', title: 'Leaf', level: 2, parent_id: 'G'},
      {id: 'B', code: 'B', title: 'Sibling', level: 2, parent_id: 'G'},
      {id: 'S', code: 'S', title: 'Other root', level: 0, parent_id: null},
      {id: 'X', code: 'X', title: 'One hop', level: 2, parent_id: 'S'},
      {id: 'Y', code: 'Y', title: 'Two hops', level: 2, parent_id: 'S'},
      {id: 'Z', code: 'Z', title: 'Ancestor reference', level: 2, parent_id: 'S'}
    ],
    edges: [
      {id: 'G-R', source: 'G', target: 'R', type: 'broader'},
      {id: 'A-G', source: 'A', target: 'G', type: 'broader'},
      {id: 'B-G', source: 'B', target: 'G', type: 'broader'},
      {id: 'X-S', source: 'X', target: 'S', type: 'broader'},
      {id: 'Y-S', source: 'Y', target: 'S', type: 'broader'},
      {id: 'Z-S', source: 'Z', target: 'S', type: 'broader'},
      {id: 'A-X', source: 'A', target: 'X', type: 'avoid_classification', reference_text: 'except X'},
      {id: 'X-Y', source: 'X', target: 'Y', type: 'see_also'},
      {id: 'R-Z', source: 'R', target: 'Z', type: 'see_also'}
    ]
  }).elements({mode: 'focus', focusId: 'A', references: true});
  assert.deepEqual(ids(sample), new Set(['__msc__', 'R', 'G', 'A', 'B', 'X']));
  assert.equal(sample.edges.find(edge => edge.data.id === 'A-X').data.type, 'avoid_classification');
  assert.equal(sample.edges.find(edge => edge.data.id === 'A-X').data.reference_text, 'except X');
  assert.ok(!sample.edges.some(edge => edge.data.id === 'X-Y' || edge.data.id === 'R-Z'));
});

check('Cytoscape metadata never creates compound parents and carries correct roots and sizes', () => {
  const graph = model.elements({mode: 'full'});
  for (const node of graph.nodes) {
    assert.ok(!Object.hasOwn(node.data, 'parent'));
    assert.equal(node.data.size, node.data.level < 0 ? 36 : node.data.level === 0 ? 22 : node.data.level === 1 ? 13 : 7);
    assert.equal(node.data.root, model.rootOf(node.data.id));
  }
  assert.equal(model.rootOf('05C50'), '05');
  assert.equal(model.rootOf('__msc__'), '__msc__');
  assert.equal(model.rootOf('unknown'), null);
  assert.deepEqual(model.descendants('unknown'), []);
  assert.equal(model.descendants('__msc__').length, 6604);
  assert.equal(model.descendants('05C50').length, 1);
});

check('Repeated views are deterministic, reject invalid requests and leave source data unchanged', () => {
  const options = {mode: 'focus', focusId: '05C50', references: true};
  assert.deepEqual(model.elements(options), model.elements(options));
  assert.equal(JSON.stringify(dataset), original);
  assert.throws(() => model.elements({mode: 'invented'}), /Unknown MSC graph mode/);
  assert.throws(() => model.elements({focusId: 'unknown'}), /Unknown MSC focus/);
  assert.throws(() => new Model({nodes: [{id: 'A', parent_id: 'B'}], edges: []}), /Unknown MSC parent/);
  assert.throws(() => new Model({nodes: [{id: 'A', parent_id: 'B'}, {id: 'B', parent_id: 'A'}], edges: []}), /Cyclic MSC hierarchy/);
});

const localWitness = new Model({
  nodes: [
    {id:'R',code:'R',title:'Root',level:0,parent_id:null},
    {id:'G',code:'G',title:'Group',level:1,parent_id:'R'},
    {id:'A',code:'A',title:'Chosen',level:2,parent_id:'G'},
    {id:'B',code:'B',title:'Sibling',level:2,parent_id:'G'},
    {id:'S',code:'S',title:'Other root',level:0,parent_id:null},
    {id:'X',code:'X',title:'Excluded',level:2,parent_id:'S'},
    {id:'Y',code:'Y',title:'Next reference',level:2,parent_id:'S'},
    {id:'Z',code:'Z',title:'Ancestor reference',level:2,parent_id:'S'}
  ],
  edges: [
    {id:'G-R',source:'G',target:'R',type:'broader'},
    {id:'A-G',source:'A',target:'G',type:'broader'},
    {id:'B-G',source:'B',target:'G',type:'broader'},
    {id:'X-S',source:'X',target:'S',type:'broader'},
    {id:'Y-S',source:'Y',target:'S',type:'broader'},
    {id:'Z-S',source:'Z',target:'S',type:'broader'},
    {id:'A-X',source:'A',target:'X',type:'avoid_classification',reference_text:'Do not use X for this subject'},
    {id:'X-Y',source:'X',target:'Y',type:'see_also',reference_text:'Related Y'},
    {id:'R-Z',source:'R',target:'Z',type:'classify_elsewhere',reference_text:'If in the specified case'}
  ]
});

check('Local depth is exact graph distance, with no sibling expansion at depth one', () => {
  const one=localWitness.elements({mode:'local',focusId:'A',depth:1});
  assert.deepEqual(ids(one),new Set(['A','G']));
  assert.deepEqual(one.edges.map(e=>e.data.id),['A-G']);
  assert.equal(one.realNodeCount,2);
  assert.equal(one.depth,1);
  const two=localWitness.elements({mode:'local',focusId:'A',depth:2});
  assert.deepEqual(ids(two),new Set(['A','G','R','B']));
  assert.deepEqual(new Set(two.edges.map(e=>e.data.id)),new Set(['G-R','A-G','B-G']));
  assert.equal(two.realNodeCount,4);
});

check('Local reference traversal is undirected while source directions and exclusions stay intact', () => {
  const one=localWitness.elements({mode:'local',focusId:'A',depth:1,references:true});
  assert.deepEqual(ids(one),new Set(['A','G','X']));
  const exclusion=one.edges.find(e=>e.data.id==='A-X').data;
  assert.equal(exclusion.source,'A');assert.equal(exclusion.target,'X');
  assert.equal(exclusion.type,'avoid_classification');
  assert.equal(exclusion.reference_text,'Do not use X for this subject');
  const reverse=localWitness.elements({mode:'local',focusId:'X',depth:1,references:true});
  assert.ok(ids(reverse).has('A'),'Incoming edges must be navigable in a local neighborhood');
  assert.equal(reverse.edges.find(e=>e.data.id==='A-X').data.source,'A');
  const two=localWitness.elements({mode:'local',focusId:'A',depth:2,references:true});
  assert.deepEqual(ids(two),new Set(['A','G','X','R','B','S','Y']));
  assert.equal(two.referenceCount,2);
  const three=localWitness.elements({mode:'local',focusId:'A',depth:3,references:true});
  assert.ok(ids(three).has('Z'));
  assert.equal(three.edges.find(e=>e.data.id==='R-Z').data.type,'classify_elsewhere');
});

check('Local graph cannot shortcut between roots through the synthetic overview center', () => {
  const graph=localWitness.elements({mode:'local',focusId:'R',depth:3,references:false});
  assert.deepEqual(ids(graph),new Set(['R','G','A','B']));
  assert.ok(!ids(graph).has('__msc__'));
  assert.ok(graph.edges.every(e=>e.data.type!=='overview'));
  const actual=model.elements({mode:'local',focusId:'05',depth:3,references:false});
  assert.equal(actual.realNodeCount,92);
  assert.ok(actual.nodes.every(n=>n.data.root==='05'));
  assert.ok(actual.edges.every(e=>originalEdges.has(e.data.id)));
});

check('Local mode validates its focus and depth and leaves the original dataset intact', () => {
  assert.throws(()=>model.elements({mode:'local'}),/actual MSC category/);
  assert.throws(()=>model.elements({mode:'local',focusId:'unknown'}),/Unknown MSC focus/);
  for(const depth of [0,4,-1,1.5,'2',NaN])assert.throws(()=>model.elements({mode:'local',focusId:'05',depth}),/integer from 1 to 3/);
  const graph=model.elements({mode:'local',focusId:'05C50',depth:1});
  assert.deepEqual(ids(graph),new Set(['05C50','05C']));
  assert.equal(JSON.stringify(dataset),original);
});

check('Color groups cover each of the 63 official roots exactly once and contain no invented codes', () => {
  assert.equal(presentation.groups.length,9);
  const assigned=presentation.groups.flatMap(group=>group.roots);
  assert.equal(assigned.length,63);
  assert.equal(new Set(assigned).size,63);
  assert.deepEqual(new Set(assigned),new Set(dataset.nodes.filter(n=>n.level===0).map(n=>n.id)));
  assert.equal(new Set(presentation.groups.map(g=>g.id)).size,9);
  assert.equal(new Set(presentation.groups.map(g=>g.color)).size,9);
  for(const group of presentation.groups){
    assert.match(group.color,/^#[0-9a-f]{6}$/i);
    assert.ok(group.label&&group.shortLabel);
    assert.ok(Object.isFrozen(group)&&Object.isFrozen(group.roots));
    for(const root of group.roots)assert.equal(presentation.groupForRoot(root),group);
  }
  assert.equal(presentation.groupForRoot('__msc__'),null);
  assert.equal(presentation.groupForRoot('05C50'),null);
  assert.match(presentation.description,/не дополнительный уровень MSC/);
});

check('Decoration adds presentation fields only, preserving inventory and every official edge', () => {
  const graph=model.elements({mode:'full',references:true}),before=JSON.stringify(graph);
  const colored=presentation.decorate(graph);
  assert.notEqual(colored,graph);
  assert.notEqual(colored.nodes,graph.nodes);
  assert.notEqual(colored.edges,graph.edges);
  assert.deepEqual(ids(colored),ids(graph));
  assert.deepEqual(colored.edges,graph.edges);
  assert.equal(colored.realNodeCount,6603);
  for(let i=0;i<graph.nodes.length;i++){
    const originalNode=graph.nodes[i],node=colored.nodes[i];
    assert.notEqual(node,originalNode);assert.notEqual(node.data,originalNode.data);
    for(const [key,value]of Object.entries(originalNode.data))assert.deepEqual(node.data[key],value);
    const group=presentation.groupForRoot(node.data.root);
    assert.equal(node.data.colorGroup,group?group.id:'context');
    assert.equal(node.data.color,group?group.color:'#64748b');
    assert.ok(!Object.hasOwn(node.data,'parent'),'Colors must not create compound parents');
  }
  colored.nodes[1].data.title='Changed only in result';
  colored.edges[0].data.type='Changed only in result';
  assert.equal(JSON.stringify(graph),before);
  assert.equal(JSON.stringify(dataset),original);
});

check('Color presentation works in a browser global without package runtime dependencies', () => {
  const sandbox={};
  vm.runInNewContext(fs.readFileSync(path.join(__dirname,'../web/graph-presentation.js'),'utf8'),sandbox);
  assert.equal(sandbox.MSCGraphPresentation.groups.length,9);
  assert.equal(sandbox.MSCGraphPresentation.groupForRoot('05').id,'discrete');
  const graph=model.elements({mode:'local',focusId:'05C50',depth:1});
  const colored=sandbox.MSCGraphPresentation.decorate(graph);
  assert.equal(colored.nodes.length,2);
  assert.ok(colored.nodes.every(n=>n.data.colorGroup==='discrete'));
});

console.log(JSON.stringify({passed, failed: 0, source_nodes: dataset.nodes.length, source_edges: dataset.edges.length}));
