/* Live localhost regression for the Obsidian-inspired graph workspace. No API mocks or POSTs. */
const {chromium}=require(process.env.ATLAS_PLAYWRIGHT_MODULE || 'playwright');
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const Model=require('./web/graph-model.js'),Presentation=require('./web/graph-presentation.js');

(async()=>{
  const base=process.env.ATLAS_BASE_URL||'http://127.0.0.1:8765';
  const dataset=JSON.parse(fs.readFileSync(path.join(__dirname,'data/msc2020.json'))),model=new Model(dataset);
  const report={checked_at:new Date().toISOString(),base_url:base,mocked:false,compilation_started:false,checks:[],browser_errors:[],failed_requests:[],external_requests:[],mutating_requests:[]};
  const browser=await chromium.launch({headless:true});
  const context=await browser.newContext({viewport:{width:1500,height:1100},colorScheme:'dark'});
  const page=await context.newPage();page.setDefaultTimeout(10000);
  page.on('pageerror',error=>report.browser_errors.push(error.message));
  page.on('request',request=>{if(!request.url().startsWith(base)&&/^https?:/.test(request.url()))report.external_requests.push(request.url());if(request.method()!=='GET')report.mutating_requests.push(request.method()+' '+request.url());});
  page.on('response',response=>{if(response.status()>=400&&response.url().startsWith(base))report.failed_requests.push(response.status()+' '+response.url());});
  const read=fn=>page.evaluate(fn);
  async function check(name,fn){try{const evidence=await fn();report.checks.push({name,passed:true,evidence});console.log('PASS '+name);}catch(error){report.checks.push({name,passed:false,error:error.message});console.log('FAIL '+name+': '+error.message.slice(0,1000));}}
  async function ready(mode){await page.waitForFunction(mode=>{const c=document.getElementById('graph-canvas'),g=c?.mscGraph;return g&&c.getAttribute('aria-busy')==='false'&&g.snapshot().ready&&(!mode||g.mode===mode)&&!c.dataset.error;},mode,{timeout:30000});}
  const snapshot=()=>read(()=>document.getElementById('graph-canvas').mscGraph.snapshot());
  const ids=()=>read(()=>document.getElementById('graph-canvas').mscGraph.cy.nodes().map(n=>n.id()).sort());
  async function resetMap(){await page.goto(base+'/#map');await page.reload();await ready('overview');}
  async function search(id){await page.locator('#msc-search').fill(id);await page.locator(`#catalog-list button[data-msc="${id}"]`).click();await ready();}
  async function settings(){if(!await page.locator('#graph-settings').evaluate(n=>n.open))await page.locator('#graph-settings > summary').click();}
  async function closeSettings(){if(await page.locator('#graph-settings').evaluate(n=>n.open))await page.locator('#graph-settings > summary').click();}
  async function local(id='05C50'){await resetMap();await search(id);await page.locator('#graph-local').click();await ready('local');}
  function expectedLocal(id,depth,references=true){return model.elements({mode:'local',focusId:id,depth,references}).nodes.map(n=>n.data.id).sort();}
  async function point(id){await page.locator('#graph-canvas').scrollIntoViewIfNeeded();return page.evaluate(id=>{const c=document.getElementById('graph-canvas'),p=c.mscGraph.cy.getElementById(id).renderedPosition(),r=c.getBoundingClientRect();return {x:r.x+p.x,y:r.y+p.y};},id);}
  async function viewport(){return read(()=>{const g=document.getElementById('graph-canvas').mscGraph;return {zoom:g.cy.zoom(),pan:{...g.cy.pan()}};});}
  function sameViewport(actual,expected){assert.ok(Math.abs(actual.zoom-expected.zoom)<1e-8,'Zoom differs');assert.ok(Math.hypot(actual.pan.x-expected.pan.x,actual.pan.y-expected.pan.y)<0.01,'Pan differs');}

  await check('Nine meaningful navigation colors cover real source roots without changing source inventory',async()=>{
    await resetMap();assert.equal(await page.locator('#graph-color-groups > button').count(),9);
    const nodes=await read(()=>document.getElementById('graph-canvas').mscGraph.cy.nodes().filter(n=>n.data('level')===0).map(n=>({id:n.id(),group:n.data('colorGroup'),color:n.data('color'),rendered:n.style('background-color')})));
    assert.equal(nodes.length,63);assert.equal(new Set(nodes.map(n=>n.color)).size,9);
    for(const n of nodes){const group=Presentation.groupForRoot(n.id);assert.equal(n.group,group.id);assert.equal(n.color,group.color);assert.notEqual(n.rendered,'rgb(180,180,180)');}
    assert.equal((await snapshot()).realNodeCount,597);return {roots:63,color_groups:9,source_categories:6603};
  });
  await check('Color chips support isolate, add, remove and reset while preserving induced edges',async()=>{
    await page.locator('[data-group="algebra"]').click();await ready();assert.deepEqual((await snapshot()).groups,['algebra']);
    let actual=await read(()=>document.getElementById('graph-canvas').mscGraph.cy.nodes().filter(n=>n.id()!=='__msc__').map(n=>n.data('colorGroup')));assert.ok(actual.length&&actual.every(g=>g==='algebra'));
    await page.locator('[data-group="geometry"]').click();await ready();assert.deepEqual(new Set((await snapshot()).groups),new Set(['algebra','geometry']));
    await page.locator('[data-group="algebra"]').click();await ready();assert.deepEqual((await snapshot()).groups,['geometry']);
    await page.locator('[data-group="geometry"]').click();await ready();assert.equal((await snapshot()).groups,null);assert.equal((await snapshot()).realNodeCount,597);
    return {solo:true,multiple:true,reset_to_all:true};
  });
  await check('Root and color filters combine, empty result is explicit and reset restores the complete view',async()=>{
    await page.locator('[data-group="algebra"]').click();await ready();await settings();await page.locator('#graph-root-filter').selectOption('05');await ready();
    assert.equal((await snapshot()).realNodeCount,0);assert.equal((await snapshot()).nodeCount,0);assert.match(await page.locator('#graph-selection-status').innerText(),/Фильтры скрыли все рубрики/);
    await page.locator('#graph-reset-filters').click();await ready();assert.equal((await snapshot()).realNodeCount,597);assert.equal((await snapshot()).rootFilter,'all');
    await page.locator('#graph-root-filter').selectOption('05');await ready();const expected=model.elements({mode:'overview'}).nodes.filter(n=>n.data.root==='05').map(n=>n.data.id).sort();
    assert.deepEqual((await ids()).filter(id=>id!=='__msc__'),expected);await page.locator('#graph-reset-filters').click();await ready();await closeSettings();return {empty_result_explicit:true,root:'05',root_categories:expected.length};
  });
  await check('Real node hover dims unrelated elements and restores colors on mouseout',async()=>{
    await search('05');await page.locator('#graph-canvas').scrollIntoViewIfNeeded();await page.waitForTimeout(200);const p=await point('05C');await page.mouse.move(p.x,p.y);await page.waitForTimeout(120);
    const hovered=await read(()=>{const g=document.getElementById('graph-canvas').mscGraph;return {muted:g.cy.elements('.hover-muted').length,neighbors:g.cy.elements('.hover-neighbor').length,color:g.cy.getElementById('05C').style('background-color'),groupColor:g.cy.getElementById('05C').data('color')};});
    assert.ok(hovered.muted>0);assert.ok(hovered.neighbors>1);assert.equal(hovered.groupColor,Presentation.groupForRoot('05').color);
    await page.mouse.move(5,5);await page.waitForFunction(()=>document.getElementById('graph-canvas').mscGraph.cy.elements('.hover-muted,.hover-neighbor').length===0);assert.equal(await read(()=>document.getElementById('graph-canvas').mscGraph.cy.elements('.hover-muted,.hover-neighbor').length),0);
    return hovered;
  });
  await check('Local graph depths one to three exactly match real-edge BFS and never include the virtual hub',async()=>{
    await local();assert.equal(await page.locator('#graph-references').isChecked(),true);const evidence=[];
    for(const depth of [1,2,3]){await page.locator('#graph-depth').selectOption(String(depth));await ready('local');const actual=await ids(),expected=expectedLocal('05C50',depth);assert.deepEqual(actual,expected);assert.ok(!actual.includes('__msc__'));evidence.push({depth,nodes:actual.length});}
    await page.locator('#graph-references').uncheck();await ready('local');assert.deepEqual(await ids(),expectedLocal('05C50',3,false));return evidence;
  });
  await check('Rapid depth changes cannot let an older layout replace the final requested graph',async()=>{
    await local();assert.equal((await snapshot()).depth,1);
    await page.evaluate(()=>{const select=document.getElementById('graph-depth');select.value='2';select.dispatchEvent(new Event('change',{bubbles:true}));select.value='1';select.dispatchEvent(new Event('change',{bubbles:true}));});
    await ready('local');await page.waitForTimeout(400);const actual=await ids();assert.deepEqual(actual,expectedLocal('05C50',1));assert.equal((await snapshot()).depth,1);assert.equal(await page.locator('#graph-depth').inputValue(),'1');return {requested_depth:1,actual_nodes:actual.length};
  });
  await check('Click selects without relayout; inspector links continue a local exploration',async()=>{
    await local();await page.locator('#graph-canvas').scrollIntoViewIfNeeded();const id=(await ids()).find(x=>x!=='05C50');const p=await point(id),before=await read(()=>{const g=document.getElementById('graph-canvas').mscGraph;return {key:g.currentKey,positions:g.positions(),history:g.history.length};});
    await page.mouse.click(p.x,p.y);await ready();const after=await read(()=>{const g=document.getElementById('graph-canvas').mscGraph;return {key:g.currentKey,positions:g.positions(),selected:g.selected,history:g.history.length};});
    assert.equal(after.selected,id);assert.equal(after.key,before.key);assert.deepEqual(after.positions,before.positions);assert.ok(after.history>before.history);assert.ok(await page.locator('#graph-node-inspector').isVisible());
    const button=page.locator('#graph-node-inspector .inspector-links button').first(),target=await button.innerText();await button.click();await ready('local');assert.equal((await snapshot()).selected,target);assert.deepEqual(await ids(),expectedLocal(target,1));return {selected:id,next:target};
  });
  await check('History restores depth, selected node, mode and camera; new navigation truncates forward entries',async()=>{
    await local();await page.locator('#graph-zoom-in').click();await page.locator('#graph-canvas').focus();await page.keyboard.press('ArrowRight');const one=await snapshot(),camera=await viewport();
    await page.locator('#graph-depth').selectOption('2');await ready('local');const two=await snapshot();assert.ok(two.historyIndex>one.historyIndex);
    await page.locator('#graph-history-back').click();await ready('local');assert.equal((await snapshot()).depth,1);assert.equal((await snapshot()).selected,'05C50');sameViewport(await viewport(),camera);
    await page.locator('#graph-history-forward').click();await ready('local');assert.equal((await snapshot()).depth,2);
    await page.locator('#graph-history-back').click();await ready('local');await search('17C40');await ready('local');assert.equal((await snapshot()).selected,'17C40');assert.equal(await page.locator('#graph-history-forward').isEnabled(),false);return {restored_camera:camera,forward_truncated:true};
  });
  await check('History restores reference and color/root filters together',async()=>{
    await resetMap();await page.locator('[data-group="algebra"]').click();await ready();await settings();await page.locator('#graph-root-filter').selectOption('17');await ready();const filtered=await snapshot();await closeSettings();
    await page.locator('#graph-references').check();await ready();assert.ok((await snapshot()).historyIndex>filtered.historyIndex);await page.locator('#graph-history-back').click();await ready();const restored=await snapshot();assert.equal(restored.rootFilter,'17');assert.deepEqual(restored.groups,['algebra']);assert.equal(await page.locator('#graph-references').isChecked(),false);
    await page.locator('#graph-history-forward').click();await ready();assert.equal(await page.locator('#graph-references').isChecked(),true);return {restored_root:restored.rootFilter,restored_groups:restored.groups};
  });
  await check('Bookmarks persist through actual reload and reopen the selected rubric',async()=>{
    await resetMap();await search('05C50');await page.locator('#graph-bookmark-toggle').click();assert.equal(await page.locator('#graph-bookmark-toggle').getAttribute('aria-pressed'),'true');await page.reload();await ready('overview');
    await page.locator('#graph-bookmarks button').filter({hasText:'05C50'}).click();await ready();assert.equal((await snapshot()).selected,'05C50');assert.equal(await page.locator('#graph-bookmark-toggle').getAttribute('aria-pressed'),'true');await page.locator('#graph-bookmark-toggle').click();assert.equal(await page.locator('#graph-bookmark-toggle').getAttribute('aria-pressed'),'false');return {persisted_and_reopened:'05C50',removed:true};
  });
  await check('Labels and monochrome are optional appearance settings with reload persistence',async()=>{
    await settings();await page.locator('#graph-label-style').selectOption('name');let label=await read(()=>document.getElementById('graph-canvas').mscGraph.cy.getElementById('05C50').style('label'));assert.ok(label.includes('Graphs and linear algebra'));
    await page.locator('#graph-color-mode').selectOption('mono');assert.equal((await snapshot()).colorMode,'mono');const color=await read(()=>document.getElementById('graph-canvas').mscGraph.cy.getElementById('05C50').style('background-color'));assert.equal(color,'rgb(180,180,180)');await closeSettings();
    await page.locator('#graph-labels').uncheck();assert.equal(await read(()=>document.getElementById('graph-canvas').mscGraph.cy.getElementById('05C50').style('label')),'');await page.locator('#graph-labels').check();assert.ok((await read(()=>document.getElementById('graph-canvas').mscGraph.cy.getElementById('05C50').style('label'))).includes('Graphs'));
    await page.reload();await ready();await settings();assert.equal(await page.locator('#graph-color-mode').inputValue(),'mono');assert.equal(await page.locator('#graph-label-style').inputValue(),'name');await page.locator('#graph-color-mode').selectOption('groups');await page.locator('#graph-label-style').selectOption('code');await closeSettings();return {name_label:label,monochrome:color,persisted:true};
  });
  await check('Immersive view expands the graph and Escape restores normal workspace',async()=>{
    const before=await page.locator('#graph-canvas').boundingBox();await page.locator('#graph-fullscreen').click();await page.waitForTimeout(150);assert.equal((await snapshot()).immersive,true);const expanded=await page.locator('#graph-canvas').boundingBox();assert.ok(expanded.width>before.width);assert.equal(await page.locator('#graph-fullscreen').getAttribute('aria-pressed'),'true');await page.keyboard.press('Escape');await page.waitForTimeout(100);assert.equal((await snapshot()).immersive,false);return {before,expanded};
  });
  await check('Narrow desktop and mobile keep the colored graph, controls and settings inside the viewport',async()=>{
    const evidence=[];
    for(const viewportSize of [{width:768,height:737},{width:390,height:950},{width:320,height:950}]){
      await page.setViewportSize(viewportSize);await page.waitForTimeout(120);await settings();const measure=await read(()=>{const box=document.querySelector('.graph-settings-panel').getBoundingClientRect();return {width:innerWidth,scroll:document.documentElement.scrollWidth,canvas:document.getElementById('graph-canvas').getBoundingClientRect().toJSON(),settings:{left:box.left,right:box.right},background:getComputedStyle(document.body).backgroundColor};});
      assert.ok(measure.scroll<=viewportSize.width);assert.ok(measure.settings.left>=-1&&measure.settings.right<=viewportSize.width+1);assert.equal(measure.background,'rgb(255, 255, 255)');assert.ok(measure.canvas.height>=350);evidence.push(measure);await closeSettings();
    }
    await page.setViewportSize({width:1500,height:1100});return evidence;
  });
  await check('The real saved Lean certificate survives the new graph workspace',async()=>{
    await page.locator('#featured-example-open').click();await page.locator('#comparison-story[data-proof-status="verified"]').waitFor();assert.equal(await page.locator('#verification-result .success').count(),1);assert.ok((await page.locator('#file-content-0').inputValue()).includes('AlgebraObject.energy')||(await page.locator('#file-content-0').inputValue()).includes('namespace AlgebraObject'));await page.locator('[data-tab="map"]').click();await ready();return {run:new URL(page.url()).searchParams.get('run'),verified:true};
  });
  await check('No browser errors, failing HTTP responses, external calls or mutating requests',async()=>{
    assert.deepEqual(report.browser_errors,[]);assert.deepEqual(report.failed_requests,[]);assert.deepEqual(report.external_requests,[]);assert.deepEqual(report.mutating_requests,[]);return {browser_errors:0,failed_requests:0,external_requests:0,mutations:0};
  });
  report.passed=report.checks.filter(c=>c.passed).length;report.failed=report.checks.length-report.passed;report.success=report.failed===0;
  fs.mkdirSync(path.join(__dirname,'verification'),{recursive:true});fs.writeFileSync(path.join(__dirname,'verification/obsidian-functional.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({passed:report.passed,failed:report.failed}));await browser.close();if(report.failed)process.exitCode=1;
})().catch(error=>{console.error(error);process.exitCode=1;});
