'use strict';
const assert=require('node:assert/strict');
const vm=require('node:vm');
const fs=require('node:fs');
const Model=require('../web/object-graph.js');
const graph={id:'example',revision:3,msc_codes:['05C50'],objects:[{id:'a',title:'Граф'},{id:'b',title:'Веса'},{id:'c',title:'Квадратичная форма'}],
  transitions:[{id:'energy',title:'Энергия',source_ids:['a','b'],target_ids:['c'],status:'hypothesis',case_id:'graph_energy',
    obligations:[{id:'identity',target:'energy_eq',statement:'x = x',status:'verified'}]}],sources:[{id:'source',title:'Источник'}]};
const tests=[
  ['Hyperedges preserve every endpoint without inventing pairwise equivalences',()=>{
    const elements=Model.elements(graph),edges=elements.filter(e=>e.data.source);
    assert.equal(elements.filter(e=>!e.data.source).length,4);assert.equal(edges.length,3);
    assert.deepEqual(edges.map(e=>[e.data.source,e.data.target]),[['object:a','transition:energy'],['object:b','transition:energy'],['transition:energy','object:c']]);
    assert.ok(edges.every(e=>e.data.status==='hypothesis'));
  }],
  ['Proposal/completion states never become proved',()=>{
    for(const status of ['proposed','candidate','complete','completed','pending','ready',undefined]) assert.equal(Model.transitionStatus({status}),'hypothesis');
    assert.equal(Model.transitionStatus({status:'failed'}),'incomplete');
    assert.equal(Model.presentation({status:'needs_recheck'}).label,'Нужна новая проверка');
    assert.equal(Model.transitionStatus({status:'refuted'}),'incomplete');
    assert.equal(Model.transitionStatus({status:'refuted',certificate:{id:'verified'}}),'refuted');
    assert.equal(Model.transitionStatus({status:'proved'}),'incomplete');
    assert.equal(Model.transitionStatus({status:'proved',certificate:{id:'verified'}}),'proved');
  }],
  ['Selection IDs cannot collide between objects and transitions',()=>{
    const collision={objects:[{id:'same',title:'Object'}],transitions:[{id:'same',title:'Transition'}]};
    assert.equal(Model.selected(collision,'object:same').value.title,'Object');
    assert.equal(Model.selected(collision,'transition:same').value.title,'Transition');
    assert.equal(Model.selected(collision,'object:missing'),null);
  }],
  ['Verification pins graph revision and selected transition',()=>{
    const payload=Model.verificationPayload(graph,graph.transitions[0],{mode:'pilot',budget:{max_calls:0}});
    assert.equal(payload.graph_revision,3);assert.equal(payload.transition_id,'energy');assert.equal(payload.case_id,'graph_energy');assert.equal(payload.purpose,'prove');
    assert.throws(()=>Model.verificationPayload({...graph,id:null},graph.transitions[0]),/сохраните/);
    assert.throws(()=>Model.verificationPayload(graph,{...graph.transitions[0],case_id:undefined},{mode:'pilot'}),/нет локального пилота/);
  }],
  ['New revision clears displayed evidence and leaves the original immutable',()=>{
    const original=JSON.parse(JSON.stringify(graph));original.transitions[0].status='proved';original.transitions[0].certificates=[{id:'cert'}];
    const draft=Model.revisionDraft(original);
    assert.equal(draft.transitions[0].status,'hypothesis');assert.equal(draft.transitions[0].certificates,undefined);
    assert.equal(draft.transitions[0].obligations[0].status,undefined);assert.equal(original.transitions[0].status,'proved');
  }],
  ['Obligation badges use bound certificate entries, not proposal flags',()=>{
    const obligation={id:'identity',target:'energy_eq',status:'verified',expected_outcome:'proved'};
    assert.equal(Model.obligationEvidence({},obligation).status,'pending');
    const transition={certificate:{result:{verification:{obligations:[{id:'identity',target:'energy_eq',ok:true}]}}}};
    assert.equal(Model.obligationEvidence(transition,obligation).status,'verified');
    assert.equal(Model.obligationEvidence(transition,{...obligation,target:'another'}).status,'pending');
    assert.equal(Model.obligationEvidence({last_result:{result:{verification:{obligations:[{id:'identity',target:'energy_eq',ok:false}]}}}},obligation).status,'incomplete');
  }],
  ['A transition proof view includes its ancestors, not another target',()=>{
    const proof={nodes:['definition','identity','nonnegative'].map(id=>({id})),edges:[{source:'definition',target:'identity'},{source:'identity',target:'nonnegative'}]};
    const sliced=Model.proofSlice(proof,{obligations:[{target:'identity'}]});
    assert.deepEqual(sliced.nodes.map(n=>n.id),['definition','identity']);assert.equal(sliced.edges.length,1);assert.equal(proof.nodes.length,3);
  }],
  ['Browser and CommonJS expose the same model',()=>{
    const context={};vm.runInNewContext(fs.readFileSync(require.resolve('../web/object-graph.js'),'utf8'),context);
    assert.deepEqual(Object.keys(context.ObjectGraphModel).sort(),Object.keys(Model).sort());
  }],
  ['Article claims cannot appear as formalized or expose unrelated proof nodes',()=>{
    const transition={id:'article',formulation_status:'literature_only',agent_task:null,obligations:[],status:'proved',certificate:{id:'wrong'}};
    assert.equal(Model.formulation(transition).formalized,false);assert.equal(Model.formulation(transition).action,'Формализовать и проверить');
    assert.equal(Model.presentation(transition).status,'incomplete');assert.equal(Model.presentation({...transition,status:'proposed'}).label,'Утверждение статьи');
    assert.deepEqual(Model.proofSlice({nodes:[{id:'unrelated_lemma'}],edges:[]},transition),{nodes:[],edges:[]});
    assert.throws(()=>Model.verificationPayload({id:'paper',revision:1,transitions:[transition]}, {...transition,case_id:'fixture'}, {mode:'pilot'}),/нет локального пилота/);
    assert.equal(Model.formulation({formulation_status:'formalized',agent_task:null,obligations:[]}).formalized,false);
    assert.equal(Model.formulation({agent_task:{target:'a',statement:'True'},obligations:[{id:'a',target:'a'}]}).formalized,true);
  }],
  ['Paper scope pins the saved version and excludes empty section containers',()=>{
    const paper={versioned_id:'2610.38474v1',sections:[{id:'document',title:'Paper',chunk_ids:[]},{id:'abstract1',title:'Abstract',chunk_ids:['a']},{id:'S0',title:'Introduction',chunk_ids:['b']},{id:'S2',title:'2. Finite inverses',chunk_ids:['c']}]};
    assert.equal(Model.defaultPaperSection(paper),'S2');
    assert.deepEqual(Model.paperScope(paper,'S2'),{paper_ids:['2610.38474v1'],section_ids:['S2']});
    assert.deepEqual(Model.paperScope(paper,''),{paper_ids:['2610.38474v1'],section_ids:[]});
    assert.deepEqual(Model.paperScope(paper,['S0','S2']),{paper_ids:['2610.38474v1'],section_ids:['S0','S2']});
    assert.throws(()=>Model.paperScope(paper,'other'),/нет текста/);assert.throws(()=>Model.paperScope(paper,'document'),/нет текста/);
    assert.throws(()=>Model.paperScope({sections:[]}),/версии/);
  }],
  ['Transition source references restrict article citations to their actual scope',()=>{
    const sources=[{id:'s1',title:'Section 1'},{id:'s2',title:'Section 2'}];
    assert.deepEqual(Model.relatedSources({sources},{source_refs:['s2']}),[sources[1]]);
    const graph={sources:[{id:'s1',versioned_id:'2610.38474v1',section_id:'S9.SS3'},{id:'s2',url:'https://arxiv.org/html/2610.38474v1#S9.SS4'},{id:'s3',url:'https://unrelated.example/abs/1111.11111v1'}]};
    assert.deepEqual(Model.sourcePaperScope(graph,{source_refs:['s2']}),{paper_ids:['2610.38474v1'],section_ids:['S9.SS4']});
    assert.deepEqual(Model.sourcePaperScope(graph,{source_refs:['s1']}),{paper_ids:['2610.38474v1'],section_ids:['S9.SS3']});
  }]
];
let failures=0;for(const [name,test] of tests){try{test();console.log('PASS '+name);}catch(error){failures++;console.error('FAIL '+name,error);}}
console.log(JSON.stringify({passed:tests.length-failures,failed:failures}));process.exitCode=failures?1:0;
