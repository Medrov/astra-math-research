'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path');
const objects=require('../web/object-graph.js'),guided=require('../web/guided-research.js'),map=require('../web/research-map.js');
const appearance=require('../web/research-appearance.js'),mscPresentation=require('../web/graph-presentation.js');
const noSummary={entitySummary:()=>null};
function fixture(){return {id:'run',purpose:'prove',status:'complete',outcome:'proved',selected_transition_id:'chosen',graph_ref:{id:'derived',revision:1},object_graph:{id:'derived',revision:1,objects:[{id:'a',title:'Input'},{id:'b',title:'Output'},{id:'c',title:'Other output'}],transitions:[{id:'chosen',title:'Chosen relation',source_ids:['a'],target_ids:['b'],formulation_status:'formalized',agent_task:{target:'Goal'},obligations:[],status:'proved',certificate:{run_id:'run'},semantic_review:{status:'aligned'}},{id:'other',title:'Other candidate',source_ids:['a'],target_ids:['c'],formulation_status:'candidate',agent_task:null,status:'proposed'}]},formal_contract:{target:'Goal',required_obligations:[{id:'lemma',target:'Lemma',expected_outcome:'proved'},{id:'goal',target:'Goal',expected_outcome:'proved'}]},nodes:[{id:'Def',kind:'def',status:'defined'},{id:'Lemma',kind:'theorem',status:'proved',statement:'True'},{id:'Goal',kind:'theorem',status:'proved',statement:'True'},{id:'Unrelated',kind:'theorem',status:'proved',dependencies:['Goal']}],edges:[{source:'Def',target:'Lemma',type:'type_dependency'},{source:'Lemma',target:'Goal',type:'proof_dependency'},{source:'Missing',target:'Goal',type:'planned_dependency'}],result:{outcome:'proved',verification:{target:'Goal',success:true,target_preserved:true,obligations_passed:true,audit:{status:'passed'},obligations:[{id:'lemma',target:'Lemma',ok:true,expected_outcome:'proved'},{id:'goal',target:'Goal',ok:true,expected_outcome:'proved'}]},semantic_review:{status:'aligned'}}};}
const build=(run,options={})=>map.buildModel(run,{view:'proof',objectModel:objects,verdict:guided.verdict,renderer:noSummary,...options});
const descendants=node=>[node,...node.children.flatMap(descendants)];

test('object overview always contains all saved entities and preserves the source graph',()=>{
  const run=fixture(),before=JSON.stringify(run),focus=build(run,{view:'objects'});
  assert.deepEqual(focus.nodes.map(n=>n.id),['object:a','object:b','object:c','transition:chosen','transition:other']);assert.equal(focus.edges.length,4);assert.deepEqual(build(run,{view:'objects',focusTransitionId:'other'}).nodes.map(n=>n.id),focus.nodes.map(n=>n.id));
  const all=build(run,{view:'objects',scope:'all'});assert.equal(all.nodes.length,5);assert.equal(all.nodes.find(n=>n.id==='transition:chosen').status,'proved');assert.equal(all.nodes.find(n=>n.id==='transition:other').status,'hypothesis');assert.equal(JSON.stringify(run),before);
});
test('proof overview uses all current nodes and only stored edges',()=>{
  const model=build(fixture());assert.equal(model.view,'proof');assert.deepEqual(model.nodes.map(n=>n.id),['proof:Def','proof:Lemma','proof:Goal','proof:Unrelated']);assert.equal(model.edges.length,2);assert.deepEqual(model.edges.map(e=>e.type),['type_dependency','proof_dependency']);
  const all=build(fixture(),{scope:'all'});assert.equal(all.nodes.length,4);assert.equal(all.edges.length,2);assert.equal(all.nodes.find(n=>n.id==='proof:Unrelated').status,'pending');
  const cy=map.cyElements(all);assert.ok(cy.filter(e=>e.data.source).every(e=>!('status'in e.data)&&!('color'in e.data)),'dependency edges never inherit a verified colour');
});
test('changing branch, graph identity, revision or formal target cannot reveal another proof',()=>{
  const original=fixture();for(const scope of ['selected','all']){
    assert.equal(build(original,{focusTransitionId:'other',scope}).nodes.length,0);
    for(const change of [r=>r.object_graph.id='source',r=>r.object_graph.revision=2,r=>r.object_graph.transitions=r.object_graph.transitions.filter(t=>t.id!=='chosen'),r=>r.object_graph.transitions[0].agent_task.target='OtherGoal']){const run=structuredClone(original);change(run);const model=build(run,{scope});assert.equal(model.nodes.length,0);assert.equal(model.edges.length,0);assert.ok(model.emptyReason);}
  }
});
test('a missing contract target never falls back to all existing proof nodes',()=>{
  const run=fixture();run.nodes=[{id:'Unrelated',status:'proved',kind:'theorem'}];run.edges=[];const model=build(run);assert.equal(model.nodes.length,0);assert.match(model.emptyReason,/Цели выбранной связи/);
});
test('a proved status string alone cannot colour a proof node green',()=>{
  const run=fixture();delete run.result;for(const node of run.nodes)assert.notEqual(map.proofStatus(run,node,guided.verdict).status,'proved');
  const checked=fixture();assert.deepEqual(build(checked).counts,{obligations:2,verified:2});assert.equal(build(checked).nodes.find(n=>n.id==='proof:Def').status,'defined');
  checked.result.verification.audit.status='failed';assert.equal(build(checked).counts.verified,0);
});
test('obligation certificates match their id, target and expected outcome',()=>{
  for(const change of [r=>r.result.verification.obligations[0].id='other',r=>r.result.verification.obligations[0].target='Other',r=>r.result.verification.obligations[0].expected_outcome='refuted',r=>r.result.verification.obligations[0].ok=false]){const run=fixture();change(run);assert.equal(map.proofStatus(run,run.nodes[1],guided.verdict).status,'pending');}
});
test('final proof colour is guarded by the completed verdict and semantic review',()=>{
  const run=fixture(),goal=run.nodes[2];assert.equal(map.proofStatus(run,goal,guided.verdict).status,'proved');
  run.result.semantic_review.status='uncertain';assert.equal(map.proofStatus(run,goal,guided.verdict).status,'formal_only');
  run.status='failed';assert.equal(map.proofStatus(run,goal,guided.verdict).status,'incomplete');
  run.status='running';assert.equal(map.proofStatus(run,goal,guided.verdict).status,'checking');
});
test('even a permissive final verdict cannot certify a report for a different target',()=>{
  const run=fixture(),goal=run.nodes[2];run.result.verification.target='OtherGoal';
  for(const kind of ['proved','formal_only','refuted'])assert.equal(map.proofStatus(run,goal,()=>({kind})).status,'incomplete');
});

test('a stopped final review leaves exact compiled goal evidence formal-only, never a green connection',()=>{
  const run=fixture();run.status='budget_exhausted';run.result.verification.compilation_success=true;run.result.semantic_review={status:'pending'};run.final_semantic_review={status:'not_performed',reason:'Budget ended'};assert.equal(map.proofStatus(run,run.nodes[2],guided.verdict).status,'formal_only');assert.equal(map.proofStatus(run,run.nodes[2],()=>({kind:'proved'})).status,'incomplete');run.result.verification.target='Other';assert.equal(map.proofStatus(run,run.nodes[2],guided.verdict).status,'incomplete');
});
test('short graph labels use mathematical captions without changing the full inspector title',()=>{
  const model=build(fixture(),{renderer:{entitySummary:()=>({graphLabel:'Обратимость',title:'Полное математическое описание со всеми предпосылками и ограничениями'})}});
  assert.ok(model.nodes.every(node=>node.label==='Обратимость'));assert.ok(model.nodes.every(node=>node.title.includes('предпосылками')));
});
test('large numeric labels retain their geometry at every zoom',()=>{
  const baseline=map.labelMetrics(1);assert.deepEqual(baseline,{size:26,width:52});
  for(const zoom of [.1,.25,.6,.8,1,2]){const metrics=map.labelMetrics(zoom);assert.deepEqual(metrics,baseline,'Zoom must not enlarge text inside fixed-size cards');assert.equal(metrics.width/metrics.size,baseline.width/baseline.size,'Wrapping capacity must remain unchanged');}
});
test('canvas contains only numbers in original order with distinct object and transition shapes',()=>{
  const model=build(fixture(),{view:'objects'}),data=map.cyElements(model).filter(item=>!item.data.source).map(item=>item.data);assert.ok(data.every(item=>item.shape===(item.kind==='transition'?'round-hexagon':'round-rectangle')));assert.deepEqual(data.map(item=>item.number),[1,2,3,4,5]);assert.deepEqual(data.map(item=>item.id),model.nodes.map(node=>node.id));
  for(const item of data){assert.equal(item.label,String(item.number));assert.match(item.label,/^\d+$/);assert.ok(item.color&&item.border);}
  assert.equal(data.find(item=>item.id==='transition:other').status,'hypothesis');assert.equal(data.find(item=>item.id==='object:a').kind,'object');assert.notEqual(data[0].color,data[4].color);
});
test('saved node reports require exact target, audited success and matching statement',()=>{
  const run=fixture();delete run.result;const node=run.nodes[1];node.verification={success:true,target:'Lemma',target_preserved:true,audit:{status:'passed'},expected_statement:'True'};
  assert.equal(map.proofStatus(run,node,guided.verdict).status,'proved');
  for(const change of [{target:'Different'},{target_preserved:false},{expected_statement:'False'},{audit:{status:'failed'}},{success:false}])assert.notEqual(map.proofStatus(run,{...node,verification:{...node.verification,...change}},guided.verdict).status,'proved');
});

function compiledFixture(){
  const run=fixture(),node=run.nodes[1];node.extraction='lean_environment';const report=run.result.verification;Object.assign(report,{compilation_success:true,source_sha256:'a'.repeat(64),olean_sha256:'b'.repeat(64),environment_fingerprint:'c'.repeat(64),declarations:[{name:'Lemma',kind:'theorem',module:'Candidate',type:'True',unsafe:false}]});report.audit.audited_roots=['Lemma','Goal'];run.formal_contract.required_obligations=run.formal_contract.required_obligations.filter(item=>item.target!=='Lemma');
  run.object_graph.environment_fingerprint=report.environment_fingerprint;run.object_graph.active_environment_fingerprint=report.environment_fingerprint;run.object_graph.transitions[0].certificate={graph_id:'derived',revision:1,transition_id:'chosen',run_id:'run',environment_fingerprint:report.environment_fingerprint,validation_errors:[],result:{verification:structuredClone(report)}};return run;
}
test('compiled helper theorems use the matching audited final report rather than a status string or target success alone',()=>{
  const run=compiledFixture(),node=run.nodes[1],before=JSON.stringify(run);assert.equal(map.compiledTheoremEvidence(run,node),true);assert.deepEqual(map.proofStatus(run,node,guided.verdict),{status:'proved',label:'Проверено в итоговой сборке'});assert.equal(map.proofStatus(run,run.nodes[0],guided.verdict).status,'defined');assert.equal(map.proofStatus(run,run.nodes[3],guided.verdict).status,'pending');assert.equal(JSON.stringify(run),before);
});
test('final compiled helper evidence fails closed for changed source, environment, declaration, audit, branch and planned nodes',()=>{
  const changes=[
    r=>r.status='running',r=>r.result.verification.success=false,r=>r.result.verification.target='Other',r=>r.result.verification.target_preserved=false,r=>r.result.verification.compilation_success=false,r=>r.result.verification.obligations_passed=false,r=>r.result.verification.audit.status='failed',r=>r.result.verification.audit.audited_roots=['Goal'],r=>r.result.verification.declarations[0].type='False',r=>r.result.verification.declarations[0].module='ImportedModule',r=>r.result.verification.declarations[0].unsafe=true,
    r=>r.result.verification.source_sha256='d'.repeat(64),r=>r.result.verification.olean_sha256='d'.repeat(64),r=>r.result.verification.environment_fingerprint='d'.repeat(64),r=>r.object_graph.active_environment_fingerprint='d'.repeat(64),r=>r.object_graph.environment_fingerprint='d'.repeat(64),r=>r.object_graph.transitions[0].certificate.run_id='other-run',r=>r.object_graph.transitions[0].certificate.revision=2,r=>r.object_graph.transitions[0].certificate.result.verification.declarations=[],r=>r.object_graph.transitions[0].certificate.result.verification.audit.audited_roots=[],r=>r.graph_ref.revision=2,r=>r.selected_transition_id='other',r=>r.nodes[1].planned=true,r=>r.nodes[1].extraction='plan',r=>r.nodes[1].statement='False'
  ];
  for(const change of changes){const run=compiledFixture();change(run);assert.equal(map.compiledTheoremEvidence(run,run.nodes[1]),false,String(change));assert.notEqual(map.proofStatus(run,run.nodes[1],guided.verdict).status,'proved',String(change));}
});

const compiledBridgeFile=path.join(__dirname,'../research_data/3fbf2768b3084da998c006650fca78ee/run.json');
test('the actual finite-dimensional bridge shows four checked theorems and one definition',{skip:!fs.existsSync(compiledBridgeFile)&&'Local research fixture is not distributed'},()=>{
  const run=JSON.parse(fs.readFileSync(compiledBridgeFile,'utf8')),before=JSON.stringify(run),model=build(run),checked=model.nodes.filter(node=>node.status==='proved');assert.equal(model.nodes.length,5);assert.equal(checked.length,4);assert.equal(checked.filter(node=>node.statusLabel==='Проверено в итоговой сборке').length,3);assert.equal(model.nodes.find(node=>node.value.id==='bridgeScalar').status,'defined');assert.deepEqual(model.counts,{obligations:1,verified:1});assert.equal(JSON.stringify(run),before);
});

function withWorkspace(check){
  class Element{constructor(tag='div'){this.tagName=tag.toUpperCase();this.children=[];this.attributes={};this.text='';}append(...children){for(const child of children){child.parent=this;this.children.push(child);}}replaceChildren(...children){this.children=[];this.text='';this.append(...children);}setAttribute(k,v){this.attributes[k]=String(v);}getAttribute(k){return this.attributes[k];}set textContent(v){this.children=[];this.text=String(v);}get textContent(){return this.text+this.children.map(c=>c.textContent).join('');}remove(){if(this.parent)this.parent.children=this.parent.children.filter(c=>c!==this);}focus(){this.focused=true;document.activeElement=this;}}
  const saved={document:global.document,GuidedResearch:global.GuidedResearch,MathPresentation:global.MathPresentation,cytoscape:global.cytoscape,MSCContext:global.MSCContext,MSCAtlas:global.MSCAtlas,ResearchAppearance:global.ResearchAppearance,MSCGraphPresentation:global.MSCGraphPresentation,addEventListener:global.addEventListener,removeEventListener:global.removeEventListener};global.document={createElement:tag=>new Element(tag)};global.GuidedResearch=guided;global.MathPresentation=noSummary;global.ResearchAppearance=appearance;global.MSCGraphPresentation=mscPresentation;delete global.cytoscape;delete global.MSCContext;delete global.MSCAtlas;
  try{const container=new Element();return check(container);}finally{for(const[k,v]of Object.entries(saved))if(v===undefined)delete global[k];else global[k]=v;}
}
test('workspace keeps separate selections, resets on another run and never auto-verifies',()=>withWorkspace(container=>{
  const calls=[],selected=[],workspace=new map.Workspace({container,onVerify:(...args)=>calls.push(args),onSelection:value=>selected.push(value)}),run=fixture();workspace.render(run);assert.equal(workspace.view,'objects');workspace.select('proof:Lemma');workspace.setView('objects');workspace.select('transition:other');workspace.setView('proof');assert.equal(workspace.view,'objects');assert.equal(workspace.tabs.proof.hidden,true);assert.equal(workspace.model.nodes.length,5);workspace.select('transition:chosen');workspace.setView('proof');assert.equal(workspace.selection.proof,'proof:Lemma');
  workspace.select('proof:Lemma');workspace.setView('objects');workspace.setView('proof');assert.equal(workspace.selection.proof,'proof:Lemma');assert.equal(calls.length,0);assert.equal(selected[0].kind,'proof');
  workspace.render({...run,id:'new-run',purpose:'structure',selected_transition_id:null,nodes:[],edges:[]});assert.equal(workspace.view,'objects');assert.equal(workspace.focus,'chosen');assert.equal(workspace.selection.proof,null);assert.equal(calls.length,0);
  workspace.select('transition:other');const button=workspace.selectionBar.children.find(n=>n.tagName==='BUTTON');assert.ok(button);assert.equal(button.textContent,'Проверить общую структуру в Lean');button.onclick();assert.equal(calls.length,1);assert.equal(calls[0][0],workspace.run.object_graph);assert.equal(calls[0][1].id,'other');
  workspace.destroy();workspace.destroy();assert.equal(container.children.length,0);
}));
test('opening another saved graph or revision resets selection even without a run id',()=>withWorkspace(container=>{
  const workspace=new map.Workspace({container}),draft={purpose:'discover',object_graph:fixture().object_graph};workspace.render(draft);workspace.select('transition:other');
  workspace.render({...draft,object_graph:{...draft.object_graph,id:'another-graph'}});assert.equal(workspace.focus,'chosen');assert.equal(workspace.selection.objects,'transition:chosen');
  workspace.select('transition:other');workspace.render({...draft,object_graph:{...draft.object_graph,id:'another-graph',revision:2}});assert.equal(workspace.focus,'chosen');assert.equal(workspace.selection.objects,'transition:chosen');workspace.destroy();
}));
test('featured formulas stay visible and the remaining construction is collapsible',()=>withWorkspace(container=>{
  global.MathPresentation={entitySummary:()=>({title:'Readable object',formulas:[{label:'Main',tex:'x=y',featured:true},{label:'Construction',tex:'z=x+y'}]}),render:(node,text)=>node.textContent=text,formula:(node,text)=>node.textContent=text};
  const workspace=new map.Workspace({container});workspace.render(fixture(),{view:'objects',selection:'object:a'});
  const cards=workspace.inspector.children.filter(n=>n.attributes.class==='research-map-formula'),details=workspace.inspector.children.find(n=>n.tagName==='DETAILS'&&n.children[0].textContent==='Обозначения и построение');assert.equal(cards.length,1);assert.match(cards[0].textContent,/Main/);assert.ok(details);assert.match(details.textContent,/Construction/);workspace.destroy();
}));
test('fit preserves all numbered nodes without font inflation or centering only a target',()=>withWorkspace(container=>{
  const workspace=new map.Workspace({container});workspace.render(fixture());workspace.listDetails.open=false;const calls=[],data={};
  const collection={length:3,toggleClass(){return this;},removeClass(){return this;},data(key,value){data[key]=value;return this;}};
  workspace.cy={nodes:()=>collection,elements:()=>collection,resize:()=>calls.push('resize'),fit:()=>calls.push('fit'),zoom(...args){assert.equal(args.length,0,'fit must never override the fitted zoom');return .8;},center(){throw Error('fit must never center only the target');}};
  workspace.fit();assert.deepEqual(calls,['resize','fit']);assert.equal(data.labelFont,26);assert.equal(data.labelWidth,52);assert.equal(workspace.listDetails.open,false);
  for(const zoom of [.25,1,.4,1]){workspace.cy.zoom=()=>zoom;workspace.overviewLabels();assert.deepEqual(data,{labelFont:26,labelWidth:52},'Mobile-to-desktop refits must not change label geometry');}
  workspace.cy=null;workspace.destroy();
}));
test('polling preserves inspector disclosures and keyboard focus, including report updates',()=>withWorkspace(container=>{
  const workspace=new map.Workspace({container}),run=fixture();workspace.render(run,{view:'proof'});
  const detail=workspace.inspector.children.find(node=>node.tagName==='DETAILS'&&node.children[0].textContent==='Точный узел Lean');detail.open=true;
  const button=descendants(workspace.listBox).find(node=>node.attributes['data-node-id']==='proof:Lemma');button.focus();workspace.render(structuredClone(run));assert.ok(descendants(workspace.listBox).includes(button));assert.equal(document.activeElement,button);assert.ok(workspace.inspector.children.includes(detail));assert.equal(detail.open,true);
  const summary=detail.children[0];summary.focus();const next=structuredClone(run);next.result.verification.diagnostics=['new saved diagnostic'];workspace.render(next);
  const refreshed=workspace.inspector.children.find(node=>node.tagName==='DETAILS'&&node.children[0].textContent==='Точный узел Lean');assert.equal(refreshed.open,true);assert.equal(document.activeElement,refreshed.children[0]);workspace.destroy();
}));
test('node selection opens the inspector without automatic viewport movement',()=>withWorkspace(container=>{
  const workspace=new map.Workspace({container});workspace.render(fixture());workspace.centerSelection=()=>{throw Error('Selection must not zoom or pan');};workspace.select('proof:Lemma');assert.equal(workspace.selection.proof,'proof:Lemma');assert.match(workspace.inspector.textContent,/Lemma/);workspace.destroy();
}));
test('objects and proof use directed layouts with horizontal desktop and vertical mobile ranks',()=>withWorkspace(container=>{
  const workspace=new map.Workspace({container}),layouts=[];workspace.cy={layout(options){layouts.push(options);return{run(){},stop(){}};}};
  for(const view of ['objects','proof'])for(const[width,direction]of [[900,'LR'],[740,'LR'],[650,'TB'],[390,'TB']]){workspace.view=view;workspace.canvas.clientWidth=width;assert.equal(workspace.direction(),direction);workspace.positionGraph();assert.equal(layouts.at(-1).name,'dagre');assert.equal(layouts.at(-1).rankDir,direction);assert.equal(layouts.at(-1).fit,false);}
  workspace.cy=null;workspace.destroy();
}));

test('selecting any object or transition preserves topology, domain fill and its distinguishing shape',()=>withWorkspace(container=>{
  const workspace=new map.Workspace({container});workspace.render(fixture());const before=JSON.stringify(map.cyElements(workspace.model)),ids=workspace.model.nodes.map(n=>n.id);
  for(const id of ['transition:other','object:c','transition:chosen']){workspace.select(id);assert.deepEqual(workspace.model.nodes.map(n=>n.id),ids);assert.equal(JSON.stringify(map.cyElements(workspace.model)),before);const selected=descendants(workspace.listBox).find(n=>n.attributes['data-node-id']===id);assert.equal(selected.attributes['aria-pressed'],'true');assert.match(selected.attributes.class,/research-map-node-card/);const visual=map.cyElements(workspace.model).find(n=>n.data.id===id).data;assert.equal(visual.shape,visual.kind==='transition'?'round-hexagon':'round-rectangle');const number=descendants(selected).find(n=>n.attributes.class==='research-map-node-number');assert.ok(number.attributes.style.includes(visual.color));assert.ok(number.attributes.style.includes(visual.textColor));}
  assert.equal(workspace.focusButton,undefined);assert.equal(workspace.allButton,undefined);assert.match(workspace.listBox.children[0].children[0].textContent,/Объекты/);assert.match(workspace.listBox.children[1].children[0].textContent,/Переходы/);workspace.destroy();
}));
test('each canvas number resolves to the same full title in the list, selected bar and inspector',()=>withWorkspace(container=>{
  const actions=[],workspace=new map.Workspace({container,onVerify:()=>actions.push('verify'),onOpenRun:()=>actions.push('open')}),run=fixture();workspace.render(run);
  for(const view of ['objects','proof']){
    if(view==='proof')workspace.select('transition:chosen');workspace.setView(view);
    const ids=workspace.model.nodes.map(node=>node.id),canvas=map.cyElements(workspace.model).filter(item=>item.data.source===undefined);
    assert.equal(new Set(canvas.map(item=>item.data.number)).size,ids.length);
    const rows=()=>descendants(workspace.listBox).filter(node=>node.tagName==='BUTTON'&&node.attributes['data-node-id']);assert.equal(rows().length,ids.length);
    assert.deepEqual(rows().map(node=>Number(node.attributes['data-number'])),canvas.map(item=>item.data.number));
    for(const item of canvas){
      const node=workspace.model.nodes.find(value=>value.id===item.data.id),row=rows().find(value=>value.attributes['data-node-id']===node.id);assert.equal(row.attributes['data-number'],item.data.label);assert.ok(row.textContent.includes(node.title));row.onclick();
      for(const surface of [workspace.selectionBar,workspace.inspector]){const badge=descendants(surface).find(value=>value.attributes.class==='research-map-node-number');assert.equal(badge.attributes['data-node-id'],node.id);assert.equal(badge.textContent,item.data.label);assert.ok(surface.textContent.includes(node.title));}
      assert.deepEqual(workspace.model.nodes.map(value=>value.id),ids);assert.equal(map.cyElements(workspace.model).find(value=>value.data.id===node.id).data.label,item.data.label);
    }
  }
  assert.deepEqual(actions,[]);assert.ok(workspace.legend.textContent.includes('Выбранный узел'));workspace.destroy();
}));

test('polling preserves existing numbers across proof reordering, status changes and new nodes',()=>withWorkspace(container=>{
  const workspace=new map.Workspace({container}),run=fixture();workspace.render(run,{view:'proof'});const original=new Map(workspace.model.nodes.map(node=>[node.id,node.number]));assert.deepEqual([...original.values()],[1,2,3,4]);
  const update=structuredClone(run);update.status='running';update.nodes=[update.nodes[3],{id:'NewLemma',kind:'theorem',statement:'True',status:'pending'},update.nodes[2],update.nodes[0],update.nodes[1]];workspace.render(update);
  for(const node of workspace.model.nodes)assert.equal(node.number,original.get(node.id)||5);assert.equal(workspace.model.nodes.find(node=>node.id==='proof:NewLemma').number,5);assert.equal(new Set(workspace.model.nodes.map(node=>node.number)).size,5);
  workspace.select('proof:NewLemma');workspace.render(structuredClone(update));assert.equal(workspace.selection.proof,'proof:NewLemma');assert.equal(workspace.model.nodes.find(node=>node.id==='proof:NewLemma').number,5);
  workspace.setView('objects');assert.deepEqual(workspace.model.nodes.map(node=>node.number),[1,2,3,4,5]);workspace.setView('proof');for(const node of workspace.model.nodes)assert.equal(node.number,original.get(node.id)||5);
  const reordered=structuredClone(update);reordered.nodes.reverse();workspace.render(reordered);assert.equal(workspace.model.nodes.find(node=>node.id==='proof:NewLemma').number,5);for(const[id,number]of original)assert.equal(workspace.model.nodes.find(node=>node.id===id).number,number);
  const revised=structuredClone(reordered);revised.object_graph.revision=2;revised.graph_ref.revision=2;workspace.render(revised,{view:'proof'});assert.deepEqual(workspace.model.nodes.map(node=>node.number),[1,2,3,4,5]);workspace.destroy();
}));

test('MSC labels preserve attribution, use plain text in list buttons and open only known codes',()=>withWorkspace(container=>{
  const opened=[],actions=[],lookedUp=[],known={code:'53A10',title:'Минимальные поверхности',officialTitle:'Minimal surfaces',path:[{code:'53',title:'Дифференциальная геометрия'},{code:'53A10',title:'Минимальные поверхности'}],known:true};
  global.MSCAtlas={lookup(code){lookedUp.push(code);return code==='53A10'?known:null;},open:code=>opened.push(code)};
  global.MSCContext={forNode(run,node,lookup){assert.equal(run.id,'run');assert.ok(node.value&&node.id&&node.kind);return {origin:node.kind==='transition'?'related_objects':'explicit',label:node.kind==='transition'?'По связанным объектам':'Рубрики узла',items:[lookup('53A10'),{code:'99Z99',title:'Название рубрики недоступно',officialTitle:'',path:[],known:false}]};}};
  const workspace=new map.Workspace({container,onVerify:()=>actions.push('verify'),onOpenRun:()=>actions.push('run')});workspace.render(fixture());
  const row=descendants(workspace.listBox).find(node=>node.tagName==='BUTTON'&&node.attributes['data-node-id']==='transition:chosen');assert.match(row.textContent,/По связанным объектам/);assert.match(row.textContent,/53A10 — Минимальные поверхности/);assert.equal(descendants(row).filter(node=>node.tagName==='BUTTON').length,1,'MSC text must not add a nested button');
  for(const surface of [workspace.selectionBar,workspace.inspector]){assert.match(surface.textContent,/По связанным объектам/);assert.match(surface.textContent,/53A10 — Минимальные поверхности/);assert.match(surface.textContent,/99Z99 — Название рубрики недоступно/);}
  assert.match(workspace.inspector.textContent,/Minimal surfaces/);assert.match(workspace.inspector.textContent,/53 — Дифференциальная геометрия → 53A10/);
  const links=descendants(workspace.inspector).filter(node=>node.attributes.class==='research-map-msc-open');assert.equal(links.length,1);assert.equal(links[0].textContent,'Открыть MSC 53A10 на карте');assert.equal(links[0].disabled,false);assert.deepEqual(opened,[]);assert.deepEqual(actions,[]);links[0].onclick();assert.deepEqual(opened,['53A10']);assert.deepEqual(actions,[]);assert.ok(lookedUp.length);assert.ok(map.cyElements(workspace.model).filter(node=>!node.data.source).every(node=>/^\d+$/.test(node.data.label)));workspace.destroy();
}));

test('the mobile selection caption retains every MSC code and origin while full names stay in the list and inspector',()=>withWorkspace(container=>{
  const items=['53A10','53C42','58J50','34B24'].map((code,i)=>({code,title:'Полное название рубрики '+i,officialTitle:'Official title '+i,path:[],known:false}));global.MSCContext={forNode:()=>({origin:'related_objects',label:'По связанным объектам',items})};
  const workspace=new map.Workspace({container});workspace.render(fixture());const compact=descendants(workspace.selectionBar).find(node=>node.attributes.class==='research-map-msc-codes'),full=descendants(workspace.selectionBar).find(node=>node.attributes.class==='research-map-msc-full');assert.equal(compact.textContent,'53A10 · 53C42 · 58J50 · 34B24');assert.match(workspace.selectionBar.textContent,/По связанным объектам/);
  for(const item of items){assert.ok(full.textContent.includes(item.code+' — '+item.title));assert.ok(workspace.listBox.textContent.includes(item.code+' — '+item.title));assert.ok(workspace.inspector.textContent.includes(item.code+' — '+item.title));}assert.equal(descendants(workspace.listBox).filter(node=>node.attributes.class==='research-map-msc-codes').length,0);assert.equal(descendants(workspace.inspector).filter(node=>node.attributes.class==='research-map-msc-codes').length,0);workspace.destroy();
}));

test('MSC readiness refreshes cached text without reframing, changing numbers or starting actions',()=>withWorkspace(container=>{
  const listeners=new Map(),removed=[],actions=[];global.addEventListener=(type,handler)=>listeners.set(type,handler);global.removeEventListener=(type,handler)=>{removed.push([type,handler]);listeners.delete(type);};
  global.MSCContext={forNode(run,node,lookup){const hit=lookup('53A10');return {origin:'related_objects',label:'По связанным объектам',items:[{code:'53A10',title:hit?.title||'Название рубрики недоступно',officialTitle:hit?.officialTitle||'',path:hit?.path||[],known:!!hit}]};}};
  const workspace=new map.Workspace({container,onVerify:()=>actions.push('verify'),onOpenRun:()=>actions.push('run')});workspace.render(fixture());const numbers=workspace.model.nodes.map(node=>[node.id,node.number]),ready=listeners.get('msc-atlas-ready');assert.equal(typeof ready,'function');assert.match(workspace.selectionBar.textContent,/Название рубрики недоступно/);assert.equal(descendants(workspace.inspector).filter(node=>node.attributes.class==='research-map-msc-open').length,0);
  const primary=workspace.selectionBar.children.find(node=>node.tagName==='BUTTON');primary.focus();workspace.draw=()=>{throw Error('MSC readiness must not redraw topology');};workspace.initialFrame=()=>{throw Error('MSC readiness must not reframe');};workspace.centerSelection=()=>{throw Error('MSC readiness must not move selection');};
  global.MSCAtlas={lookup:()=>({title:'Минимальные поверхности',officialTitle:'Minimal surfaces',path:[]}),open:code=>actions.push('MSC '+code)};ready();
  for(const surface of [workspace.listBox,workspace.selectionBar,workspace.inspector]){assert.match(surface.textContent,/53A10 — Минимальные поверхности/);assert.doesNotMatch(surface.textContent,/Название рубрики недоступно/);}assert.deepEqual(workspace.model.nodes.map(node=>[node.id,node.number]),numbers);assert.equal(document.activeElement.textContent,primary.textContent);assert.ok(workspace.selectionBar.children.includes(document.activeElement));assert.deepEqual(actions,[]);
  workspace.destroy();assert.deepEqual(removed,[['msc-atlas-ready',ready]]);assert.equal(listeners.size,0);ready();assert.deepEqual(actions,[]);
}));

test('known MSC arrival changes the canvas appearance cache without changing topology, numbers or frame',()=>withWorkspace(container=>{
  let context={origin:'explicit',label:'Рубрики узла',items:[{code:'53A10',title:'Недоступно',known:false,path:[]}]};global.MSCContext={forNode:()=>context};const workspace=new map.Workspace({container});workspace.render(fixture());const before=map.cyElements(workspace.model),numbers=workspace.model.nodes.map(node=>[node.id,node.number]),draws=[];
  workspace.draw=(model,reframe)=>draws.push({nodes:map.cyElements(model),reframe});workspace.initialFrame=workspace.positionGraph=workspace.centerSelection=()=>{throw Error('MSC recolouring must not move or lay out the graph');};
  context={origin:'explicit',label:'Рубрики узла',items:[{code:'53A10',title:'Минимальные поверхности',known:true,path:[{code:'53',title:'Дифференциальная геометрия'},{code:'53A10',title:'Минимальные поверхности'}]}]};workspace.atlasReady();assert.equal(draws.length,1);assert.equal(draws[0].reframe,false);assert.deepEqual(workspace.model.nodes.map(node=>[node.id,node.number]),numbers);assert.notEqual(draws[0].nodes.find(item=>item.data.id==='transition:chosen').data.color,before.find(item=>item.data.id==='transition:chosen').data.color);assert.deepEqual(draws[0].nodes.filter(item=>item.data.source),before.filter(item=>item.data.source));assert.match(workspace.legend.textContent,/Цвет — область MSC/);assert.match(workspace.legend.textContent,/Геометрия/);workspace.render(structuredClone(workspace.run));assert.equal(draws.length,1);workspace.destroy();
}));

test('object-graph proof badges remain explicit while domain fill ignores status; proof view retains status colours',()=>{
  const context={origin:'explicit',label:'Рубрики узла',items:[{code:'53A10',known:true,path:[{code:'53',title:'Геометрия'}]}]},model=build(fixture(),{view:'objects'}),node=model.nodes.find(value=>value.id==='transition:chosen');node.mscContext=context;const domain=map.appearanceFor(node);assert.equal(node.status,'proved');node.status='hypothesis';assert.deepEqual(map.appearanceFor(node),domain);assert.equal(domain.shape,'round-hexagon');assert.ok(appearance.contrast(domain.fill,domain.text)>=4.5);
  const proof=build(fixture()).nodes.find(value=>value.id==='proof:Goal');proof.mscContext=context;const proved=map.appearanceFor(proof);assert.equal(proved.classification,'status');assert.equal(proved.shape,'round-rectangle');proof.mscContext={origin:'research',items:[]};assert.deepEqual(map.appearanceFor(proof),proved);proof.status='pending';assert.notEqual(map.appearanceFor(proof).fill,proved.fill);
});

test('missing MSC module is explicitly unavailable without invented codes or navigation',()=>withWorkspace(container=>{
  const workspace=new map.Workspace({container});workspace.render(fixture());assert.match(workspace.selectionBar.textContent,/Контекст MSC2020 ещё не загружен/);assert.ok(workspace.model.nodes.every(node=>node.mscContext.items.length===0));assert.equal(descendants(workspace.inspector).filter(node=>node.attributes.class==='research-map-msc-open').length,0);workspace.destroy();
}));

test('transition context uses only exact endpoint ids, deduplicates them and does not invent pairwise relations',()=>{
  const run=fixture();run.object_graph.transitions[1].source_ids=['a','b','a'];run.object_graph.transitions[1].target_ids=['c','c'];const model=build(run,{view:'objects'});model.edges.push({id:'irrelevant-neighbour',source:'object:c',target:'object:a'});const before=JSON.stringify(model),context=map.transitionContext(model,'transition:other');
  assert.deepEqual(context.inputs.map(node=>[node.id,node.number,node.title]),[['object:a',1,'Input'],['object:b',2,'Output']]);assert.deepEqual(context.outputs.map(node=>[node.id,node.number,node.title]),[['object:c',3,'Other output']]);assert.equal(context.transition.number,5);assert.equal(context.endpointsComplete,true);assert.deepEqual(context.missing,[]);assert.equal(map.endpointRole(context,'object:a'),'input');assert.equal(map.endpointRole(context,'object:c'),'output');assert.equal(map.transitionContext(model,'object:a'),null);assert.equal(JSON.stringify(model),before);assert.equal(context.pairs,undefined);
});

test('self-loop endpoints retain both roles and missing endpoints never acquire a fabricated number',()=>withWorkspace(container=>{
  const run=fixture();run.object_graph.transitions[1].source_ids=['a','a'];run.object_graph.transitions[1].target_ids=['a','missing','missing'];const workspace=new map.Workspace({container,onVerify(){throw Error('Must not verify');}});workspace.render(run);workspace.select('transition:other');
  assert.equal(map.endpointRole(workspace.context,'object:a'),'both');assert.equal(workspace.context.endpointsComplete,false);assert.deepEqual(workspace.context.missing,['missing']);const absent=workspace.context.outputs.find(node=>node.missing);assert.equal(absent.number,null);assert.equal(absent.id,null);assert.match(workspace.flowPanel.textContent,/Вход и выход перехода/);assert.match(workspace.flowPanel.textContent,/Состав входов и выходов неполон/);assert.match(workspace.flowPanel.textContent,/missing/);assert.doesNotMatch(workspace.flowPanel.textContent,/№null|№undefined/);
  const row=descendants(workspace.listBox).find(node=>node.tagName==='BUTTON'&&node.attributes['data-node-id']==='object:a');assert.equal(row.attributes['data-endpoint-role'],'both');assert.equal(workspace.selectionBar.children.find(node=>node.tagName==='BUTTON').disabled,true);
  const fixed=structuredClone(run);fixed.object_graph.transitions[1].target_ids=['a'];workspace.render(fixed);assert.equal(workspace.context.endpointsComplete,true);assert.equal(workspace.selectionBar.children.find(node=>node.tagName==='BUTTON').disabled,false);workspace.destroy();
}));

test('flow preserves the complete claim and conditions, explains the action and passes the untouched transition',()=>withWorkspace(container=>{
  const rendered=[],calls=[],run=fixture(),value=run.object_graph.transitions[1];value.source_ids=['a','b'];value.target_ids=['c'];value.formulation_status='literature_only';value.claim=String.raw`При \(a>1/2\) существует единственное \(S>0\): `+'полное условие '.repeat(40)+String.raw`\(F(S)=0\).`;value.assumptions=[String.raw`\(e_0=2\pi\)`,String.raw`\(a>1/2\)`];global.MathPresentation={entitySummary:()=>null,render(node,text){rendered.push(text);node.textContent=text;}};
  const workspace=new map.Workspace({container,onVerify:(...args)=>calls.push(args),onOpenRun:id=>calls.push(id)});workspace.render(run);workspace.select('transition:other');assert.equal(workspace.flowPanel.hidden,false);assert.ok(rendered.includes(value.claim));for(const assumption of value.assumptions)assert.ok(rendered.includes(assumption));assert.match(workspace.flowPanel.textContent,/Что предлагается формализовать и проверить/);assert.match(workspace.flowPanel.textContent,/Astra попробует/);assert.match(workspace.flowPanel.textContent,/№1 — Input/);assert.match(workspace.flowPanel.textContent,/№2 — Output/);assert.match(workspace.flowPanel.textContent,/№3 — Other output/);assert.equal(calls.length,0);
  const details=workspace.flowPanel.children.find(node=>node.tagName==='DETAILS');details.open=true;details.children[0].focus();workspace.render(structuredClone(run));assert.equal(workspace.flowPanel.children.find(node=>node.tagName==='DETAILS').open,true);assert.equal(document.activeElement,details.children[0]);const primary=workspace.selectionBar.children.find(node=>node.tagName==='BUTTON');primary.onclick();assert.equal(calls.length,1);assert.equal(calls[0][0],workspace.run.object_graph);assert.equal(calls[0][1],workspace.run.object_graph.transitions[1]);assert.equal(calls[0][1].claim,value.claim);assert.deepEqual(calls[0][1].source_ids,['a','b']);
  workspace.render(workspace.run,{runs:[{id:'previous',purpose:'prove',status:'failed',selected_transition_id:'other',source_graph_ref:{id:'derived',revision:1}}]});assert.match(workspace.flowPanel.textContent,/«Открыть попытку» открывает сохранённый запуск/);assert.equal(calls.length,1);workspace.destroy();
}));

test('endpoint highlighting touches only direct nodes and directed edges and clears without moving the viewport',()=>withWorkspace(container=>{
  const run=fixture();run.object_graph.transitions[1].source_ids=['a','b'];run.object_graph.transitions[1].target_ids=['c'];const workspace=new map.Workspace({container});workspace.render(run);const before=JSON.stringify(map.cyElements(workspace.model)),classes=new Map([...workspace.model.nodes,...workspace.model.edges].map(node=>[node.id,new Set()])),item=id=>({length:classes.has(id)?1:0,addClass(names){for(const name of names.split(' '))classes.get(id)?.add(name);return this;},connectedEdges(){return{addClass(name){for(const edge of workspace.model.edges)if(edge.source===id||edge.target===id)classes.get(edge.id)?.add(name);}};}});
  workspace.cy={getElementById:item,elements:()=>({removeClass(names){for(const state of classes.values())for(const name of names.split(' '))state.delete(name);}})};workspace.draw=workspace.positionGraph=workspace.initialFrame=workspace.centerSelection=()=>{throw Error('Selection must not redraw, lay out or move the viewport');};workspace.select('transition:other');assert.equal(JSON.stringify(map.cyElements(workspace.model)),before);assert.ok(classes.get('object:a').has('map-input'));assert.ok(classes.get('object:b').has('map-input'));assert.ok(classes.get('object:c').has('map-output'));assert.ok(classes.get('transition:other').has('map-selected'));assert.equal(classes.get('transition:chosen').size,0);
  for(const edge of workspace.model.edges){assert.equal(classes.get(edge.id).has('map-input-edge'),['object:a','object:b'].includes(edge.source)&&edge.target==='transition:other');assert.equal(classes.get(edge.id).has('map-output-edge'),edge.source==='transition:other'&&edge.target==='object:c');}
  workspace.select('object:a');assert.equal(workspace.context,null);assert.equal(workspace.flowPanel.hidden,true);assert.equal(workspace.flowPanel.textContent,'');assert.ok([...classes.values()].every(state=>![...state].some(name=>/^map-(input|output|both)/.test(name))));assert.ok(descendants(workspace.listBox).filter(node=>node.tagName==='BUTTON').every(node=>node.attributes['data-endpoint-role']===''));assert.doesNotMatch(workspace.legend.textContent,/Вход перехода|Выход перехода/);assert.equal(JSON.stringify(map.cyElements(workspace.model)),before);workspace.cy=null;workspace.destroy();
}));

test('prior attempt lookup requires exact graph revision and transition lineage without promoting a candidate',()=>{
  const run={purpose:'structure',object_graph:fixture().object_graph},transition=run.object_graph.transitions[1],before=JSON.stringify(run),base={purpose:'prove',selected_transition_id:'other',source_graph_ref:{id:'derived',revision:1}};
  const history=[{...base,id:'success',status:'complete',finished_at:'2026-10-30T11:00:00Z'},{...base,id:'failed-latest',status:'failed',finished_at:'2026-10-31T11:00:00Z'},{...base,id:'wrong-revision',status:'complete',finished_at:'2026-11-01T11:00:00Z',source_graph_ref:{id:'derived',revision:2}},{...base,id:'wrong-transition',selected_transition_id:'chosen',status:'complete',finished_at:'2026-11-02T11:00:00Z'}];
  assert.deepEqual(map.priorAttempt(run,transition,history),{runId:'failed-latest',label:'Открыть попытку',origin:'history'});assert.equal(map.priorAttempt(run,transition,[history[0]]).label,'Открыть проверку');assert.equal(map.priorAttempt(run,transition,history.slice(2)),null);assert.equal(map.priorAttempt(run,transition,[{...base,id:'direct',status:'complete',source_graph_ref:null,graph_ref:{id:'derived',revision:1}}]).runId,'direct');
  assert.equal(map.priorAttempt(run,{...transition,last_result:{run_id:'stale',graph_id:'derived',revision:2,transition_id:'other'}}),null);assert.equal(JSON.stringify(run),before);assert.equal(objects.presentation(transition).status,'hypothesis');
});
test('prior results open through a callback; repetition remains a separate explicit action',()=>withWorkspace(container=>{
  const opened=[],verified=[],workspace=new map.Workspace({container,onOpenRun:id=>opened.push(id),onVerify:(...args)=>verified.push(args)}),run=fixture();workspace.render(run);assert.equal(opened.length,0);assert.equal(verified.length,0);
  const open=workspace.selectionBar.children.find(n=>n.tagName==='BUTTON');assert.equal(open.textContent,'Открыть проверку');open.onclick();assert.deepEqual(opened,['run']);assert.equal(verified.length,0);
  const repeat=workspace.inspector.children.find(n=>n.tagName==='DETAILS'&&n.children[0].textContent==='Повторное исследование');assert.ok(repeat);repeat.children.find(n=>n.tagName==='BUTTON').onclick();assert.equal(verified.length,1);
  workspace.select('transition:other');assert.equal(workspace.selectionBar.children.find(n=>n.tagName==='BUTTON').textContent,'Проверить общую структуру в Lean');
  workspace.render(run,{runs:[{id:'prior-failure',purpose:'prove',status:'failed',selected_transition_id:'other',source_graph_ref:{id:'derived',revision:1}}]});const attempt=workspace.selectionBar.children.find(n=>n.tagName==='BUTTON');assert.equal(attempt.textContent,'Открыть попытку');attempt.onclick();assert.deepEqual(opened,['run','prior-failure']);assert.equal(verified.length,1);workspace.destroy();
}));
test('a single primary action and the selected title and status stay above the canvas',()=>withWorkspace(container=>{
  global.MathPresentation={entitySummary:()=>({title:'Selected relation',description:'Readable description',formulas:[{label:'Formula',tex:'x=y'}]}),render:(node,text)=>node.textContent=text,formula:(node,text)=>node.textContent=text};
  const workspace=new map.Workspace({container,onOpenRun(){},onVerify(){}});workspace.render(fixture());
  assert.ok(descendants(workspace.body.children[0]).includes(workspace.canvas));assert.equal(workspace.body.children[1],workspace.listDetails);assert.equal(workspace.body.children[2],workspace.inspector);
  assert.equal(workspace.root.children.indexOf(workspace.selectionBar)+1,workspace.root.children.indexOf(workspace.body));
  const primary=descendants(workspace.root).filter(node=>node.attributes.class==='research-map-verify');assert.equal(primary.length,1);assert.equal(primary[0].parent,workspace.selectionBar);assert.equal(primary[0].textContent,'Открыть проверку');assert.match(workspace.selectionBar.textContent,/Selected relation/);assert.ok(descendants(workspace.selectionBar).some(node=>node.attributes['data-status']==='proved'));assert.ok(workspace.inspector.children.some(node=>node.attributes.class==='research-map-formula'));assert.ok(!descendants(workspace.inspector).includes(primary[0]));
  primary[0].focus();workspace.render(structuredClone(workspace.run));assert.equal(document.activeElement,primary[0]);assert.ok(workspace.selectionBar.children.includes(primary[0]));workspace.select('object:a');assert.equal(descendants(workspace.root).filter(node=>node.attributes.class==='research-map-verify').length,0);workspace.destroy();
}));

test('the numbered list distinguishes an article assertion from a new model candidate',()=>withWorkspace(container=>{
  const run=fixture();run.object_graph.transitions[1].formulation_status='literature_only';const workspace=new map.Workspace({container});workspace.render(run);workspace.select('transition:other');const row=()=>descendants(workspace.listBox).find(node=>node.tagName==='BUTTON'&&node.attributes['data-node-id']==='transition:other');assert.match(row().textContent,/Утверждение статьи/);assert.equal(row().attributes['data-number'],'5');assert.match(workspace.selectionBar.textContent,/Утверждение статьи/);
  run.object_graph.transitions[1].formulation_status='candidate';workspace.render(run);assert.match(row().textContent,/Кандидат/);assert.equal(row().attributes['data-number'],'5');assert.equal(map.cyElements(workspace.model).find(n=>n.data.id==='transition:other').data.label,'5');workspace.destroy();
}));
test('proof tab is absent without bound nodes and saved plans remain explicitly unverified',()=>withWorkspace(container=>{
  const workspace=new map.Workspace({container}),run=fixture();run.nodes=[];run.edges=[];delete run.result;run.status='running';workspace.render(run);assert.equal(workspace.tabs.proof.hidden,true);
  run.planned_nodes=[{id:'Lemma',title:'Planned lemma',statement:'True',dependencies:[]},{id:'Goal',title:'Planned goal',statement:'True',dependencies:['Lemma']}];workspace.render(run);assert.equal(workspace.tabs.proof.hidden,false);workspace.setView('proof');assert.equal(workspace.model.nodes.length,2);assert.ok(workspace.model.nodes.every(n=>n.status==='pending'&&n.statusLabel.includes('План')));assert.equal(workspace.model.edges[0].type,'planned_dependency');assert.equal(workspace.model.counts.verified,0);
  workspace.select('transition:other');assert.equal(workspace.tabs.proof.hidden,true);workspace.destroy();
}));

const catenoidFile=path.join(__dirname,'../research_data/fb7abf77c240446d85666f3ccfade06a/run.json'),failureFile=path.join(__dirname,'../research_data/624de3c0099e4e978f50bbc781154a8e/run.json');

function articleFixture(){const run=fixture();run.purpose='discover';run.object_graph.sources=[{id:'article',url:'https://arxiv.org/html/2610.35651v2#S2'}];run.object_graph.transitions[1].formulation_status='literature_only';return run;}
test('article transitions and inherited bridge sources have different actions, including after formalization',()=>{
  const article=articleFixture(),transition=article.object_graph.transitions[1],snapshot={kind:'literature_transition',graph_ref:{id:'original',revision:1},transition:{id:'original-link'}};
  assert.equal(map.transitionRole(article,transition),'article');
  for(const run of [{...article,purpose:'structure'},{...article,contract:{source_transition:snapshot}},{...article,object_graph:{...article.object_graph,sources:[...article.object_graph.sources,{structure_transition:snapshot}]}},{...article,structure_routes:[{candidates:[{transition_id:transition.id}]}]}]){
    for(const formulation_status of ['candidate','formalized'])assert.equal(map.transitionRole(run,{...transition,formulation_status}),'bridge');
  }
  assert.equal(map.transitionRole(article,{...transition,formulation_status:'candidate'}),'bridge');
  assert.equal(map.sourceTransition({...article,contract:{source_transition:snapshot}}),snapshot);
  assert.equal(map.sourceTransition({...article,contract:{source_transition:{...snapshot,kind:'untrusted-title'}}}),null);
});

test('article selection searches only by explicit primary click; original-claim verification stays secondary',()=>withWorkspace(container=>{
  const run=articleFixture(),before=JSON.stringify(run),searches=[],verifications=[],opened=[],workspace=new map.Workspace({container,onSearchAnalogies:(...args)=>searches.push(args),onVerify:(...args)=>verifications.push(args),onOpenRun:id=>opened.push(id)});
  workspace.render(run,{runs:[{id:'old-article-attempt',purpose:'prove',status:'failed',source_graph_ref:{id:'derived',revision:1},selected_transition_id:'other'}]});workspace.select('transition:other');workspace.render(structuredClone(run));
  assert.deepEqual([searches.length,verifications.length,opened.length],[0,0,0]);assert.equal(workspace.model.nodes.length,5);
  const primary=workspace.selectionBar.children.find(node=>node.tagName==='BUTTON');assert.equal(primary.textContent,'Найти аналоги в других областях');assert.equal(primary.disabled,false);primary.onclick();
  assert.deepEqual(searches,[[workspace.run.object_graph,workspace.run.object_graph.transitions[1]]]);assert.equal(verifications.length,0);
  const direct=descendants(workspace.inspector).find(node=>node.tagName==='DETAILS'&&node.children[0]?.textContent==='Прямая проверка утверждения статьи');assert.ok(direct);
  direct.children.find(node=>node.tagName==='BUTTON'&&node.textContent==='Открыть попытку').onclick();assert.deepEqual(opened,['old-article-attempt']);assert.equal(verifications.length,0);
  direct.children.find(node=>node.tagName==='BUTTON'&&node.textContent==='Проверить утверждение статьи').onclick();assert.deepEqual(verifications,[[workspace.run.object_graph,workspace.run.object_graph.transitions[1]]]);
  assert.match(workspace.flowPanel.textContent,/отправной точкой поиска аналогов в трёх областях MSC/);assert.equal(JSON.stringify(run),before);workspace.destroy();
}));

test('invalid endpoints and an active run cannot launch an article analogy search',()=>withWorkspace(container=>{
  const calls=[],workspace=new map.Workspace({container,onSearchAnalogies:(...args)=>calls.push(args)}),run=articleFixture();run.object_graph.transitions[1].target_ids=['missing'];workspace.render(run);workspace.select('transition:other');
  assert.equal(workspace.selectionBar.children.find(node=>node.tagName==='BUTTON').disabled,true);workspace.searchAnalogies('other');assert.equal(calls.length,0);
  run.object_graph.transitions[1].target_ids=['c'];run.status='running';workspace.render(run);assert.equal(workspace.selectionBar.children.find(node=>node.tagName==='BUTTON').disabled,true);workspace.searchAnalogies('other');assert.equal(calls.length,0);workspace.destroy();
}));

test('the saved catenoid coordinate change remains number thirteen and searches its whole source transition',{skip:!fs.existsSync(catenoidFile)&&'Local research fixtures are not distributed'},()=>withWorkspace(container=>{
  const run=JSON.parse(fs.readFileSync(catenoidFile,'utf8')),calls=[],workspace=new map.Workspace({container,onSearchAnalogies:(...args)=>calls.push(args)});workspace.render(run);workspace.select('transition:coordinate_change');
  assert.equal(workspace.context.transition.number,13);assert.equal(workspace.model.nodes.length,14);assert.equal(map.transitionRole(run,workspace.context.transition.value),'article');assert.deepEqual(workspace.context.inputs.map(n=>n.objectId),workspace.context.transition.value.source_ids);assert.deepEqual(workspace.context.outputs.map(n=>n.objectId),workspace.context.transition.value.target_ids);assert.equal(calls.length,0);
  workspace.selectionBar.children.find(node=>node.tagName==='BUTTON').onclick();assert.equal(calls.length,1);assert.equal(calls[0][0].id,'7e0c1ebc4a4640838c236276e700df99');assert.equal(calls[0][0].revision,1);assert.equal(calls[0][1].id,'coordinate_change');assert.equal(calls[0][1],run.object_graph.transitions.find(t=>t.id==='coordinate_change'));workspace.destroy();
}));
test('real catenoid transition ten is exactly inputs one and two to output three, with the complete source claim',{skip:!fs.existsSync(catenoidFile)&&'Local research fixtures are not distributed'},()=>withWorkspace(container=>{
  const run=JSON.parse(fs.readFileSync(catenoidFile,'utf8')),before=JSON.stringify(run),rendered=[],calls=[];global.MathPresentation={entitySummary:()=>null,render(node,text){rendered.push(text);node.textContent=text;}};const workspace=new map.Workspace({container,onVerify:(...args)=>calls.push(args)});workspace.render(run);workspace.select('transition:free_boundary');const context=workspace.context;
  assert.equal(context.transition.number,10);assert.equal(context.transition.value.formulation_status,'literature_only');assert.deepEqual(context.inputs.map(node=>[node.objectId,node.number,node.title]),[['profile',1,'Радиальный профиль'],['immersion',2,'Параметризованный сферический катеноид']]);assert.deepEqual(context.outputs.map(node=>[node.objectId,node.number,node.title]),[['truncation',3,'Катеноид со свободной границей']]);assert.equal(context.endpointsComplete,true);
  assert.ok(rendered.includes(context.transition.value.claim));for(const assumption of context.transition.value.assumptions)assert.ok(rendered.includes(assumption));assert.match(workspace.flowPanel.textContent,/существование ровно одного/);assert.match(workspace.flowPanel.textContent,/строго внутри шара/);assert.match(workspace.flowPanel.textContent,/Исходное утверждение и условия/);assert.equal(workspace.model.nodes.length,14);assert.equal(context.transition.status,'hypothesis');assert.equal(calls.length,0);assert.equal(JSON.stringify(run),before);workspace.destroy();
}));
test('real catenoid MSC metadata distinguishes explicit object rubrics from endpoint-derived transition context',{skip:!fs.existsSync(catenoidFile)&&'Local research fixtures are not distributed'},()=>withWorkspace(container=>{
  const context=require('../web/msc-context.js'),run=JSON.parse(fs.readFileSync(catenoidFile,'utf8')),before=JSON.stringify(run),data=JSON.parse(fs.readFileSync(path.join(__dirname,'../data/msc2020.json'),'utf8')),byCode=new Map(data.nodes.map(node=>[node.code,node])),opened=[];
  const lookup=code=>{const node=byCode.get(code);if(!node)return null;const chain=[];let current=node;while(current){chain.unshift({code:current.code,title:current.title});current=byCode.get(current.parent_id);}return {code:node.code,title:node.title,path:chain};};global.MSCContext=context;
  const workspace=new map.Workspace({container});workspace.render(run);const rawProfile=workspace.model.nodes.find(node=>node.id==='object:profile');assert.equal(rawProfile.mscContext.origin,'explicit');assert.deepEqual(rawProfile.mscContext.items.map(item=>item.code),['53A10']);assert.equal(rawProfile.mscContext.items[0].known,false);
  global.MSCAtlas={lookup,open:code=>opened.push(code)};workspace.atlasReady();workspace.select('transition:geometry');const geometry=workspace.model.nodes.find(node=>node.id==='transition:geometry');assert.equal(geometry.value.msc_codes,undefined);assert.equal(geometry.mscContext.origin,'related_objects');assert.deepEqual(geometry.mscContext.items.map(item=>item.code),['53A10','53C42']);assert.ok(geometry.mscContext.items.every(item=>item.known));assert.match(workspace.selectionBar.textContent,/По связанным объектам/);
  const row=descendants(workspace.listBox).find(node=>node.tagName==='BUTTON'&&node.attributes['data-node-id']==='transition:geometry');assert.match(row.textContent,/По связанным объектам/);for(const item of geometry.mscContext.items){assert.ok(row.textContent.includes(item.code+' — '+item.title));assert.ok(workspace.inspector.textContent.includes(byCode.get(item.code).title));assert.ok(item.path.length>=2);}
  assert.equal(descendants(row).filter(node=>node.tagName==='BUTTON').length,1);assert.equal(descendants(workspace.inspector).filter(node=>node.attributes.class==='research-map-msc-open').length,2);assert.deepEqual(opened,[]);assert.equal(JSON.stringify(run),before);assert.ok(map.cyElements(workspace.model).filter(item=>item.data.source===undefined).every(item=>/^\d+$/.test(item.data.label)));
  assert.equal(geometry.appearance.classification,'family');assert.equal(geometry.appearance.families[0].id,'geometry');workspace.select('transition:separation');const mixed=workspace.model.nodes.find(node=>node.id==='transition:separation');assert.equal(mixed.appearance.classification,'mixed');assert.match(workspace.selectionBar.textContent,/Несколько областей/);assert.match(workspace.legend.textContent,/Несколько областей/);const chips=descendants(workspace.selectionBar).filter(node=>node.attributes.class==='research-map-msc-chip');assert.deepEqual(new Set(chips.map(node=>node.attributes['data-family'])),new Set(['geometry','analysis']));assert.equal(mixed.status,'hypothesis');workspace.destroy();
}));
test('the real fourteen-node discovery opens its failed derived attempt without changing its snapshot',{skip:(!fs.existsSync(catenoidFile)||!fs.existsSync(failureFile))&&'Local research fixtures are not distributed'},()=>{
  const discovery=JSON.parse(fs.readFileSync(catenoidFile,'utf8')),failure=JSON.parse(fs.readFileSync(failureFile,'utf8')),before=JSON.stringify(discovery),model=build(discovery,{view:'objects'});assert.equal(model.nodes.length,14);assert.deepEqual(model.nodes.map(node=>node.number),Array.from({length:14},(_,i)=>i+1));for(const node of model.nodes){assert.equal(node.title,node.value.title);const card=map.cyElements(model).find(item=>item.data.id===node.id);assert.equal(card.data.label,String(node.number));assert.match(card.data.label,/^\d+$/);}const transition=discovery.object_graph.transitions.find(t=>t.id==='geometry');assert.equal(map.priorAttempt(discovery,transition,[failure]).runId,failure.id);assert.equal(map.priorAttempt(discovery,transition,[failure]).label,'Открыть попытку');assert.equal(model.nodes.find(n=>n.id==='transition:geometry').status,'hypothesis');assert.equal(JSON.stringify(discovery),before);
});

for(const [id,kind]of [['f5e3c278060f4b8e98fb17039789e651','prove'],['a8e79652f07e46b8924bb70c9925e37a','structure'],['abf14508267f4c1a83e58b37d01e65dc','prove']]){
  const filename=path.join(__dirname,'../research_data',id,'run.json');
  test('saved '+kind+' fixture '+id+' keeps proof and object topology separate',{skip:!fs.existsSync(filename)&&'Local research fixture is not distributed'},()=>{
    const run=JSON.parse(fs.readFileSync(filename,'utf8')),before=JSON.stringify(run),objectView=build(run,{view:'objects',scope:'all'});assert.equal(objectView.nodes.filter(n=>n.kind==='transition').length,run.object_graph.transitions.length);
    if(kind==='structure'){assert.equal(objectView.nodes.filter(n=>n.status==='proved').length,0);assert.equal(build(run,{view:'proof'}).nodes.length,0);}
    else{const proof=build(run);assert.ok(proof.nodes.length);assert.equal(proof.counts.obligations,3);assert.equal(proof.counts.verified,3);assert.equal(proof.nodes.find(n=>n.goal).status,'proved');const other=run.object_graph.transitions.find(t=>t.id!==run.selected_transition_id);assert.equal(build(run,{focusTransitionId:other.id,scope:'all'}).nodes.length,0);assert.equal(objectView.nodes.filter(n=>n.kind==='transition'&&n.status==='proved').length,1);}
    assert.equal(JSON.stringify(run),before);
  });
}


test('Lean stage returns to the current proof after browsing another object transition',()=>withWorkspace(container=>{
  const run=fixture(),before=JSON.stringify(run),workspace=new map.Workspace({container});workspace.render(run);workspace.select('transition:other');const selected=workspace.selection.objects;
  workspace.render(run,{view:'proof',proofTransitionId:run.selected_transition_id});assert.equal(workspace.view,'proof');assert.ok(workspace.model.nodes.length);assert.equal(workspace.selection.objects,selected);assert.equal(workspace.focus,'other');
  workspace.render(run,{view:'objects'});assert.equal(workspace.selection.objects,selected);assert.equal(workspace.focus,'other');assert.equal(workspace.model.nodes.find(n=>n.id===selected).value.id,'other');assert.equal(JSON.stringify(run),before);workspace.destroy();
}));
