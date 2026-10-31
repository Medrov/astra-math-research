'use strict';
const test=require('node:test'),assert=require('node:assert/strict');
const appearance=require('../web/research-appearance.js'),presentation=require('../web/graph-presentation.js');
const item=(code,root,known=true)=>({code,title:code,known,path:root?[{code:root,title:root},{code,title:code}]:[]});
const context=(items,origin='explicit')=>({origin,label:origin,items});

test('every shared MSC family gives light square objects and contrast-safe solid hexagonal transitions',()=>{
  for(const family of presentation.groups){const ctx=context([item(family.roots[0]+'A00',family.roots[0])]),object=appearance.forNode({kind:'object'},ctx,presentation),transition=appearance.forNode({kind:'transition'},ctx,presentation);
    assert.equal(object.classification,'family');assert.equal(object.families[0].color,family.color);assert.equal(object.label,family.label);assert.equal(object.shape,'round-rectangle');assert.equal(transition.shape,'round-hexagon');assert.equal(transition.text,'#ffffff');assert.notEqual(object.fill,transition.fill);assert.ok(appearance.contrast(transition.fill,transition.text)>=4.5,family.id+' white-on-solid');assert.ok(appearance.contrast(object.fill,object.text)>=4.5,family.id+' object label');
  }
});

test('several roots in one shared family stay together; different families become neutral without choosing the first',()=>{
  const same=appearance.forNode({kind:'object'},context([item('53A10','53'),item('58J50','58')]),presentation);assert.equal(same.classification,'family');assert.equal(same.families[0].id,'geometry');
  const items=[item('53A10','53'),item('34B24','34')],mixed=appearance.forNode({kind:'transition'},context(items),presentation),reversed=appearance.forNode({kind:'transition'},context([...items].reverse()),presentation);assert.equal(mixed.classification,'mixed');assert.equal(mixed.label,'Несколько областей');assert.equal(mixed.fill,reversed.fill);assert.deepEqual(new Set(mixed.families.map(family=>family.id)),new Set(['geometry','analysis']));assert.ok(appearance.contrast(mixed.fill,mixed.text)>=4.5);
  const neutral=appearance.forNode({kind:'transition'},context([],'none'),presentation);assert.equal(mixed.fill,neutral.fill);
});

test('unknown codes, missing hierarchy and research fallback never borrow a family from a prefix or a title',()=>{
  for(const ctx of [context([item('53A10',null)]),context([item('53A10','53',false)]),context([{code:'53A10',known:true,path:[{code:'XX',title:'Differential geometry'}]}]),context([item('53A10','53')],'research'),context([item('53A10','53')],'none')]){
    const result=appearance.forNode({kind:'object'},ctx,presentation);assert.notEqual(result.classification,'family');assert.equal(result.families.length,0);
  }
  const partial=appearance.forNode({kind:'object'},context([item('53A10','53'),item('99Z99',null,false)]),presentation);assert.equal(partial.classification,'partial');assert.equal(partial.fill,appearance.forNode({kind:'object'},context([],'none'),presentation).fill);
});

test('object-graph domain colour never changes when a proof status or certificate string changes',()=>{
  const ctx=context([item('53A10','53')]),before=appearance.forNode({kind:'transition',status:'hypothesis'},ctx,presentation);
  for(const status of ['proved','formal_only','refuted','needs_recheck'])assert.deepEqual(appearance.forNode({kind:'transition',status,certificate:{run_id:'ignored'}},ctx,presentation),before);
});

test('MSC chips retain individual families in a mixed context and keep readable text',()=>{
  const geometry=appearance.forMSC(item('53A10','53'),presentation),analysis=appearance.forMSC(item('34B24','34'),presentation),unknown=appearance.forMSC(item('99Z99',null,false),presentation);assert.equal(geometry.family.id,'geometry');assert.equal(analysis.family.id,'analysis');assert.notEqual(geometry.fill,analysis.fill);assert.equal(unknown.family,null);
  for(const chip of [geometry,analysis,unknown])assert.ok(appearance.contrast(chip.fill,chip.text)>=4.5);
});
