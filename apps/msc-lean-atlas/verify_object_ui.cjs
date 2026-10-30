'use strict';
/* Real UI/API acceptance checks. Local Lean pilots only; no mocks or model runs. */
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {chromium}=require(process.env.ATLAS_PLAYWRIGHT_MODULE||'playwright');
const base=process.env.ATLAS_BASE_URL||'http://127.0.0.1:8765';
const previewOnly=process.env.ATLAS_UI_PREVIEW_ONLY==='1';
const folder=path.join(__dirname,'verification','object-ui');
fs.mkdirSync(folder,{recursive:true});
const report={checked_at:new Date().toISOString(),base_url:base,preview_only:previewOnly,mocked:false,checks:[],errors:[],failed_requests:[],posts:[],runs:[],screenshots:[]};
let browser,page;
async function api(route){const response=await fetch(base+route);assert.ok(response.ok,route+' HTTP '+response.status);return response.json();}
async function check(name,fn){const start=Date.now();try{const evidence=await fn();report.checks.push({name,passed:true,elapsed_ms:Date.now()-start,evidence});console.log('PASS '+name);}catch(error){report.checks.push({name,passed:false,elapsed_ms:Date.now()-start,error:error.stack});console.error('FAIL '+name+': '+error.message);if(page)await page.screenshot({path:path.join(folder,'failure.png'),fullPage:true}).catch(()=>{});throw error;}}
async function ready(){await page.waitForFunction(()=>document.querySelector('#research-case option[value="graph_energy"]')&&document.querySelector('#objects-graph')?.objectGraph);}
async function shot(name,selector){const file=path.join(folder,name+'.png');if(selector)await page.locator(selector).screenshot({path:file});else await page.screenshot({path:file,fullPage:true});report.screenshots.push(file);}
async function chooseTransition(id){await page.locator('[data-object-item="transition:'+id+'"]').click();await page.locator('[data-verify-transition="'+id+'"]').waitFor({state:'visible'});}
async function startPilot(caseId,transitionId){
  await page.goto(base+'/#research');await ready();
  await page.locator('#research-case').selectOption(caseId);await page.locator('#research-mode').selectOption('pilot');
  await chooseTransition(transitionId);
  const responsePromise=page.waitForResponse(r=>r.request().method()==='POST'&&new URL(r.url()).pathname==='/api/research/runs');
  await page.locator('[data-verify-transition="'+transitionId+'"]').click();
  const response=await responsePromise;assert.ok(response.ok(),await response.text());const data=await response.json(),run=data.run||data;
  assert.equal(run.mode,'pilot');assert.equal(run.selected_transition_id,transitionId);assert.equal(run.budget.max_calls,0);
  report.runs.push({id:run.id,case_id:caseId,transition_id:transitionId});
  await page.waitForFunction(id=>new URL(location.href).searchParams.get('research')===id,run.id);
  return run;
}
async function complete(run){
  await page.waitForFunction(()=>['complete','failed','cancelled','budget_exhausted','interrupted'].includes(document.querySelector('#research-progress').dataset.state),null,{timeout:180000});
  const data=await api('/api/research/runs/'+run.id),final=data.run||data;
  assert.equal(final.status,'complete',JSON.stringify({status:final.status,error:final.error,result:final.result}));
  assert.equal(final.usage?.calls||final.calls_used||0,0);
  return final;
}
async function graphFits(selector,property){
  return page.locator(selector).evaluate((element,property)=>{const cy=element[property],box=cy.elements().renderedBoundingBox();return {nodes:cy.nodes().length,positions:cy.nodes().map(n=>({id:n.id(),...n.position()})),edges:cy.edges().length,box,width:cy.width(),height:cy.height(),zoom:cy.zoom()};},property);
}
function assertFits(graph){assert.ok(graph.nodes>0);assert.equal(new Set(graph.positions.map(p=>Math.round(p.x)+','+Math.round(p.y))).size,graph.nodes,'Graph nodes collapsed to identical positions');assert.ok(graph.box.x1>=-2&&graph.box.x2<=graph.width+2,JSON.stringify(graph));assert.ok(graph.box.y1>=-2&&graph.box.y2<=graph.height+2,JSON.stringify(graph));}
(async()=>{
  await check('API health and prepared graph contracts',async()=>{
    const health=await api('/api/research/status'),data=await api('/api/research/cases');assert.equal(health.ready,true);assert.equal(health.lean.available,true);
    assert.ok(data.cases.some(c=>c.id==='graph_energy'));assert.ok(data.cases.some(c=>c.id==='graph_energy_negative'));
    const energy=data.cases.find(c=>c.id==='graph_energy');assert.ok(energy.object_graph.transitions.some(t=>t.id==='energy_identity'));assert.ok(!energy.object_graph.id);
    return {ready:health.ready,lean_available:health.lean.available,cases:data.cases.map(c=>c.id)};
  });
  browser=await chromium.launch({headless:true,...(process.env.ATLAS_BROWSER_EXECUTABLE?{executablePath:process.env.ATLAS_BROWSER_EXECUTABLE}:{})});report.browser_version=browser.version();page=await browser.newPage({viewport:{width:1600,height:1100},deviceScaleFactor:1});page.setDefaultTimeout(15000);
  page.on('pageerror',error=>report.errors.push(error.message));
  page.on('response',response=>{if(response.status()>=400)report.failed_requests.push({url:response.url(),status:response.status()});});
  page.on('request',request=>{if(request.method()==='POST')report.posts.push({url:request.url(),body:request.postDataJSON()});});
  await check('MSC selection opens bounded discovery without starting a run',async()=>{
    await page.goto(base+'/#map');await page.locator('#msc-search').fill('05C50');
    await page.locator('[data-msc="05C50"]').click();await page.locator('#research-selected').click();await ready();
    assert.equal(await page.locator('#research-msc').inputValue(),'05C50');assert.equal(await page.locator('[data-purpose="discover"]').getAttribute('aria-pressed'),'true');
    assert.equal(await page.locator('#research-max-calls').inputValue(),'8');assert.equal(await page.locator('#research-timeout').inputValue(),'600');assert.equal(report.posts.length,0);
    await shot('01-msc-discovery-desktop');return {msc:'05C50',max_calls:8,timeout_seconds:600,posts:0};
  });
  await check('Prepared graph preview exposes objects, exact obligations and unproved status',async()=>{
    await page.locator('[data-purpose="prove"]').click();await page.locator('#research-case').selectOption('graph_energy');await page.locator('#research-mode').selectOption('pilot');
    await chooseTransition('energy_identity');assert.equal(await page.locator('#objects-inspector .research-status').first().textContent(),'Гипотеза');
    assert.equal(await page.locator('[data-obligation-status="pending"]').count(),1);assert.equal(await page.locator('[data-obligation-status="verified"]').count(),0);
    await page.locator('[data-object-item="object:edge_energy"]').click();assert.match(await page.locator('#objects-inspector').textContent(),/Определение/);
    await chooseTransition('energy_identity');await page.locator('#objects-fit').click();const graph=await graphFits('#objects-graph','objectGraph');assertFits(graph);
    await shot('02-objects-preview-desktop');return graph;
  });
  await check('Selected transition opens only its relevant proof plan',async()=>{
    await page.locator('#objects-inspector').getByRole('button',{name:'Открыть граф лемм →'}).click();await page.locator('#research-proof-view').waitFor({state:'visible'});
    const nodes=await page.locator('#research-graph').evaluate(element=>element.researchGraph.nodes().map(node=>node.id()));
    assert.ok(nodes.includes('TriangleEnergy.graph_energy_eq'),nodes.join(','));assert.ok(!nodes.includes('TriangleEnergy.laplacian_nonnegative'));const cases=await api('/api/research/cases');const expected=cases.cases.find(c=>c.id==='graph_energy').object_graph.transitions.find(t=>t.id==='energy_identity').obligations[0].statement;assert.ok((await page.locator('#research-node-inspector').textContent()).includes(expected),'Inspector must show the selected obligation statement');
    await shot('03-proof-plan-desktop');await page.locator('[data-research-view="objects"]').click();return {nodes};
  });
  if(!previewOnly){
    let identity,negative;
    await check('UI starts identity pilot and displays bound certificate and obligations',async()=>{
      identity=await complete(await startPilot('graph_energy','energy_identity'));
      const transition=identity.object_graph.transitions.find(t=>t.id==='energy_identity');assert.equal(transition.status,'proved');assert.ok(transition.certificate);assert.equal(transition.certificate.run_id,identity.id);
      assert.notEqual(identity.object_graph.transitions.find(t=>t.id==='nonnegative_transfer').certificate?.run_id,identity.id);
      assert.equal(await page.locator('#objects-inspector .research-status').first().textContent(),'Доказано');assert.equal(await page.locator('[data-obligation-status="verified"]').count(),transition.obligations.length);
      await shot('04-identity-certified-desktop');await page.locator('[data-obligation-id]').first().click();
      await page.locator('#research-proof-view').waitFor({state:'visible'});assert.match(await page.locator('#research-proof-context').textContent(),/Представить энергию/);
      await shot('05-certified-proof-desktop');await page.locator('[data-research-view="objects"]').click();
      const before=page.url();await page.reload();await ready();await page.waitForFunction(()=>document.querySelector('#objects-inspector .research-status')?.textContent==='Доказано');assert.equal(page.url(),before);
      return {run_id:identity.id,graph_ref:identity.graph_ref,transition:transition.id,certificate:true,verified_obligations:transition.obligations.length,calls:identity.usage?.calls||0};
    });
    await check('Negative control is a certified counterexample, not a positive theorem',async()=>{
      negative=await complete(await startPilot('graph_energy_negative','nonnegative_transfer'));
      const transition=negative.object_graph.transitions.find(t=>t.id==='nonnegative_transfer');assert.equal(transition.status,'refuted');assert.ok(transition.certificate);assert.equal(transition.formal_outcome,'refuted');
      assert.equal(await page.locator('#objects-inspector .research-status').first().textContent(),'Контрпример');assert.equal(await page.locator('[data-obligation-status="verified"]').count(),transition.obligations.length);
      assert.match(await page.locator('#objects-inspector').textContent(),/Отрицание проверено/);await shot('06-negative-certified-desktop');
      return {run_id:negative.id,transition:transition.id,formal_outcome:transition.formal_outcome,verified_obligations:transition.obligations.length,calls:negative.usage?.calls||0};
    });
    await check('Library graph and pinned revision survive URL reload',async()=>{
      await page.locator('#objects-refresh').click();await page.locator('#objects-library option[value="'+negative.graph_ref.id+'"]').waitFor({state:'attached'});
      await page.locator('#objects-library').selectOption(negative.graph_ref.id);await page.waitForFunction(id=>new URL(location.href).searchParams.get('object_graph')===id,negative.graph_ref.id);
      await page.locator('[aria-label="Версия графа"]').selectOption(String(negative.graph_ref.revision));await page.waitForFunction(revision=>new URL(location.href).searchParams.get('graph_revision')===String(revision),negative.graph_ref.revision);const before=page.url();assert.equal(new URL(before).searchParams.get('graph_revision'),String(negative.graph_ref.revision));assert.equal(new URL(before).searchParams.has('research'),false);
      await page.reload();await ready();await page.locator('[aria-label="Версия графа"]').waitFor();assert.equal(page.url(),before);assert.equal(await page.locator('[aria-label="Версия графа"]').inputValue(),String(negative.graph_ref.revision));
      await chooseTransition('nonnegative_transfer');assert.equal(await page.locator('#objects-inspector .research-status').first().textContent(),'Контрпример');return {url:before};
    });
    await check('Semantic revision invalidates current certificate and retains old version',async()=>{
      const latest=await api('/api/objects/graphs/'+negative.graph_ref.id);await page.locator('[aria-label="Версия графа"]').selectOption(String(latest.revision));await page.waitForFunction(revision=>new URL(location.href).searchParams.get('graph_revision')===String(revision),latest.revision);await page.locator('#objects-edit').click();await page.locator('#objects-editor').waitFor({state:'visible'});
      assert.match(await page.locator('#objects-editor').textContent(),/Изменение описания не меняет Lean-цель автоматически/);
      const definition=page.locator('#objects-edit-fields').getByLabel('Определение',{exact:true}).first();await definition.fill((await definition.inputValue())+'\nДополнительное условие постановки: веса рассматриваются как целые числа.');
      await shot('07-revision-editor-desktop');const responsePromise=page.waitForResponse(r=>r.request().method()==='POST'&&r.url().includes('/revisions'));
      await page.locator('#objects-edit-save').click();const response=await responsePromise;assert.ok(response.ok(),await response.text());const data=await response.json(),graph=data.graph||data;
      const transition=graph.transitions.find(t=>t.id==='nonnegative_transfer');assert.equal(graph.revision,latest.revision+1);assert.equal(transition.status,'needs_recheck');assert.equal(transition.certificate,null);assert.ok(!transition.case_id);
      await page.waitForFunction(()=>document.querySelector('#objects-inspector .research-status')?.textContent==='Нужна новая проверка');assert.equal(await page.locator('[data-obligation-status="verified"]').count(),0);
      assert.notEqual(await page.locator('#research-mode').inputValue(),'pilot');await shot('08-revision-needs-recheck-desktop');
      await page.locator('[aria-label="Версия графа"]').selectOption(String(negative.graph_ref.revision));await page.waitForFunction(()=>document.querySelector('#objects-inspector .research-status')?.textContent==='Контрпример');
      assert.equal(new URL(page.url()).searchParams.get('graph_revision'),String(negative.graph_ref.revision));
      return {graph_id:graph.id,new_revision:graph.revision,status:transition.status,old_revision_preserved:true};
    });
    await check('Pilot cancellation and resumption use real persisted run',async()=>{
      const run=await startPilot('graph_energy','nonnegative_transfer');const responsePromise=page.waitForResponse(r=>r.request().method()==='POST'&&r.url().endsWith('/cancel'));
      await page.locator('#research-cancel').click();const response=await responsePromise;assert.ok(response.ok(),await response.text());
      await page.waitForFunction(()=>document.querySelector('#research-progress').dataset.state==='cancelled',null,{timeout:30000});
      await page.locator('#research-resume').waitFor({state:'visible'});const resumePromise=page.waitForResponse(r=>r.request().method()==='POST'&&r.url().endsWith('/resume'));
      await page.locator('#research-resume').click();assert.ok((await resumePromise).ok());await page.waitForFunction(()=>['queued','running','complete'].includes(document.querySelector('#research-progress').dataset.state));const final=await complete(run);
      const transition=final.object_graph.transitions.find(t=>t.id==='nonnegative_transfer');assert.equal(transition.status,'proved');assert.ok(transition.certificate);await page.locator('#objects-fit').click();await shot('12-objects-verified-final','#research-objects-view');return {run_id:run.id,cancelled:true,resumed:true,status:final.status};
    });
  }
  await check('Mobile layout and object/proof graphs stay within viewport',async()=>{
    await page.setViewportSize({width:390,height:844});await page.locator('[data-research-view="objects"]').click();await page.locator('#objects-fit').click();
    const size=await page.evaluate(()=>({scroll:document.documentElement.scrollWidth,viewport:innerWidth}));assert.ok(size.scroll<=size.viewport+1,JSON.stringify(size));
    const graph=await graphFits('#objects-graph','objectGraph');assertFits(graph);await shot('09-objects-mobile');await shot('10-object-workspace-mobile','.objects-workspace');
    await page.locator('#objects-inspector').getByRole('button',{name:'Открыть граф лемм →'}).click();await page.locator('#research-graph-fit').click();
    const proof=await graphFits('#research-graph','researchGraph');assertFits(proof);await shot('11-proof-mobile');return {...size,object_graph:graph,proof_graph:proof};
  });
  await check('No browser errors, failed requests or model-starting POSTs',async()=>{
    const creates=report.posts.filter(p=>new URL(p.url).pathname==='/api/research/runs');assert.ok(creates.every(p=>p.body.mode==='pilot'&&p.body.budget.max_calls===0));
    assert.deepEqual(report.errors,[]);assert.deepEqual(report.failed_requests,[]);return {browser_errors:0,failed_requests:0,model_runs:0,local_pilots:creates.length};
  });
})().catch(error=>{report.fatal_error=error.stack;process.exitCode=1;}).finally(async()=>{
  if(browser)await browser.close();report.finished_at=new Date().toISOString();report.passed=!report.fatal_error&&report.checks.every(c=>c.passed);
  const file=path.join(folder,previewOnly?'preview-report.json':'report.json');fs.writeFileSync(file,JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({passed:report.passed,checks:report.checks.length,report:file}));
});
