/* Run against a local AMR server with a saved discovery program. Browser writes
   receive a test error before reaching the server. No Astra runs are dispatched. */
const assert = require('node:assert/strict');
const {chromium} = require(process.env.ATLAS_PLAYWRIGHT_MODULE || 'playwright');

async function main() {
  const base = process.env.ATLAS_BASE_URL || 'http://127.0.0.1:8765';
  const requested = process.argv[2];
  if (requested) assert.match(requested, /^[a-f0-9]{32}$/);
  const browser = await chromium.launch();
  try {
    const page = await browser.newPage({viewport:{width:1180, height:860}});
    const errors = [], writes = [];
    page.on('pageerror', err => errors.push(err.message));
    await page.route('**/api/**', async route => {
      const request = route.request();
      if (request.method() === 'GET') return route.continue();
      writes.push({path:new URL(request.url()).pathname, body:request.postDataJSON()});
      await route.fulfill({status:409, json:{error:'Тестовая остановка до запуска Astra.'}});
    });
    async function get(path) {
      const response = await page.request.get(base + path);
      assert.equal(response.status(), 200, path);
      return response.json();
    }
    const listing = await get('/api/research/programs?mode=patterns');
    assert.ok(listing.programs.every(p => p.mode === 'patterns'), 'discovery-only API history');
    const id = requested || listing.programs.find(p => p.status === 'complete')?.id;
    assert.ok(id, 'Pass the ID of a saved pattern discovery program with at least one proposal.');
    const program = await get('/api/research/programs/' + id);
    assert.equal(program.mode, 'patterns');
    const task = program.tasks.find(t => t.pattern && new Set(t.source_ids).size >= 2);
    assert.ok(task, 'The program must contain a hypothesis linked to two distinct observations.');

    const discovery = page.locator('#mode-pattern-discovery');
    await page.goto(base + '/#problems');
    await page.locator('#program-form').waitFor();
    await discovery.click();
    await page.locator('#pattern-form').waitFor();
    assert.equal(new URL(page.url()).searchParams.get('workflow'), 'patterns');
    assert.equal(await page.locator('#research-form').isVisible(), false);
    await page.locator('#pattern-question').fill('Энергия взвешенного графа');
    await page.locator('#pattern-msc').fill('05C50');
    await page.locator('#pattern-start').click();
    await page.getByText('Тестовая остановка до запуска Astra.', {exact:true}).waitFor();
    assert.equal(writes.length, 1);
    assert.equal(writes[0].path, '/api/research/programs');
    assert.equal(writes[0].body.mode, 'patterns');
    assert.equal(writes[0].body.question, 'Энергия взвешенного графа');
    assert.deepEqual(writes[0].body.msc_codes, ['05C50']);

    await page.locator('#pattern-history a[href*="program=' + id + '"]').click();
    await page.locator('#pattern-detail').waitFor();
    assert.equal(new URL(page.url()).searchParams.get('program'), id);
    await page.reload();
    const taskBox = page.locator('#pattern-tasks .program-task').filter({hasText:task.pattern});
    await taskBox.first().waitFor();
    assert.equal(await discovery.getAttribute('aria-pressed'), 'true');
    const seeds = task.source_ids.map(key => program.pattern_sources.find(s => s.id === key));
    for (const seed of seeds) {
      assert.ok(seed);
      await page.locator('#pattern-evidence [data-source-id="' + seed.id + '"]').waitFor({state:'attached'});
      assert.equal(await taskBox.getByRole('link', {name:seed.name, exact:true}).first().getAttribute('href'), seed.url);
      const sourceURL = new URL(seed.url, base);
      assert.equal(sourceURL.origin, new URL(base).origin);
      const evidence = await page.request.get(sourceURL.href);
      assert.equal(evidence.status(), 200, seed.url);
    }
    const continued = ['complete','stalled','budget_exhausted'].includes(program.status);
    if (continued) {
      await page.getByRole('button', {name:'Искать дальше'}).click();
      await page.locator('#pattern-error').filter({hasText:'Тестовая остановка до запуска Astra.'}).waitFor();
      assert.equal(writes.at(-1).path, '/api/research/programs/' + id + '/continue');
      assert.equal(writes.at(-1).body.generation, program.pattern_generation || 0);
      assert.ok(writes.at(-1).body.budget.max_calls > 0);
      assert.ok(writes.at(-1).body.budget.timeout_seconds > 0);
    }
    const child = task.run_id;
    if (child) {
      const childLink = taskBox.locator('a[href*="research=' + child + '"]').first();
      await childLink.click();
      await page.locator('#research-parent-program a').waitFor();
      assert.equal(new URL(await page.locator('#research-parent-program a').getAttribute('href')).searchParams.get('program'), id);
      assert.equal(new URL(page.url()).searchParams.get('research'), child);
      await page.goBack();
      await page.locator('#pattern-detail').waitFor();
      assert.equal(new URL(page.url()).searchParams.get('program'), id);
    }
    await page.locator('[data-tab="problems"]').click();
    await page.locator('#program-form').waitFor();
    const ordinary = await get('/api/research/programs?mode=research');
    assert.ok(ordinary.programs.every(row => row.id !== id && row.mode === 'research'), 'targeted-only API history');
    assert.equal(await page.locator('#program-history a[href*="' + id + '"]').count(), 0);
    await page.locator('#mode-qed').click();
    await page.locator('#qed-form').waitFor();
    await page.locator('[data-tab="research"]').click();
    await page.locator('#guided-research').waitFor();
    assert.equal(new URL(page.url()).searchParams.has('program'), false);
    assert.equal(new URL(page.url()).searchParams.has('workflow'), false);
    await page.setViewportSize({width:390,height:844});
    await page.goto(base + '/?workflow=patterns&program=' + id + '#research');
    await page.locator('#pattern-tasks .program-task').first().waitFor();
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true);
    assert.deepEqual(errors, []);
    console.log(JSON.stringify({program:id, cited_sources:seeds.length, continuation_checked:continued, child_link_checked:Boolean(child),
      model_calls:0, desktop:true, mobile:true, result:'passed'}));
  } finally {
    await browser.close();
  }
}
main().catch(error => {console.error(error); process.exitCode=1;});
