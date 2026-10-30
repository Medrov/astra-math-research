/* Real-browser regression of the local redesign. GET requests only; no mocked API responses. */
const { chromium } = require(process.env.ATLAS_PLAYWRIGHT_MODULE || 'playwright');
const fs = require('fs');
const path = require('path');
const assert = require('node:assert/strict');

(async () => {
  const base = process.env.ATLAS_BASE_URL || 'http://127.0.0.1:8765';
  const run = process.argv[2] || '5f5e45f3fd2c436d9d8e9e81c99006f0';
  const output = path.join(__dirname, 'verification', 'redesign-functional.json');
  const report = {
    checked_at: new Date().toISOString(), base_url: base, analysis_id: run,
    mocked: false, compilation_started: false, checks: [], browser_errors: [],
    unexpected_mutating_requests: [], failed_http_requests: []
  };
  const browser = await chromium.launch({ headless: true });
  const context = await browser.newContext({ viewport: { width: 1500, height: 1100 }, colorScheme: 'dark' });
  const page = await context.newPage();
  page.setDefaultTimeout(8000);
  page.on('pageerror', error => report.browser_errors.push(error.message));
  page.on('request', request => {
    if (request.url().startsWith(base) && request.method() !== 'GET') {
      report.unexpected_mutating_requests.push({ method: request.method(), url: request.url() });
    }
  });
  page.on('response', response => {
    if (response.url().startsWith(base) && response.status() >= 400) {
      report.failed_http_requests.push({ status: response.status(), url: response.url() });
    }
  });
  async function check(name, action) {
    try { const evidence = await action(); report.checks.push({ name, passed: true, evidence }); }
    catch (error) { report.checks.push({ name, passed: false, error: error.message }); }
    console.log((report.checks.at(-1).passed ? 'PASS ' : 'FAIL ') + name);
  }
  async function readyMap() {
    await page.goto(base + '/#map');
    await page.locator('#catalog-list button').first().waitFor();
    await page.locator('#example-select option[value="astra-energy"]').waitFor({ state: 'attached' });
  }
  async function readyRun() {
    await page.goto(base + '/?run=' + run + '#lean');
    // Same-URL goto can be a fragment navigation; force document reload to discard local form edits.
    await page.reload();
    await page.locator('#comparison-story[data-proof-status="verified"]').waitFor();
  }
  async function openDetails(selector) {
    const details = page.locator(selector);
    if (!await details.evaluate(node => node.open)) await details.locator(':scope > summary').click();
  }
  let saved;
  await check('Real saved certificate and graph inventory', async () => {
    const response = await context.request.get(base + '/api/runs/' + run);
    assert.equal(response.status(), 200);
    saved = await response.json();
    assert.equal(saved.verification.success, true);
    assert.equal(saved.verification.status, 'verified');
    assert.equal(saved.verification.target_results[0].both_inputs_participate, true);
    assert.ok(Object.values(saved.verification.target_results[0].selected_target_coverage).every(Boolean));
    const graph = await (await context.request.get(base + '/api/graph')).json();
    assert.equal(graph.nodes.length, 6603);
    return { node_count: graph.nodes.length, edge_count: graph.edges.length, certificate: saved.verification.verification_id, checked_at: saved.verification.checked_at };
  });
  await check('Sidebar example opens exact sources and verified saved story', async () => {
    assert.ok(saved, 'Saved run must be readable');
    await readyMap();
    await page.locator('#featured-example-open').click();
    await page.locator('#comparison-story[data-proof-status="verified"]').waitFor();
    await page.waitForURL(url => url.searchParams.get('run') === run && url.hash === '#lean');
    for (let i = 0; i < 2; i++) {
      assert.equal(await page.locator('#file-content-' + i).inputValue(), saved.input.files[i].content);
      assert.equal(await page.locator('#file-name-' + i).inputValue(), saved.input.files[i].name);
      assert.equal(await page.locator('#target-' + i).inputValue(), saved.input.targets[i]);
    }
    assert.equal(await page.locator('#bridge-source').inputValue(), saved.bridge_source);
    assert.equal(await page.locator('#verification-result .verification-card.success').count(), 1);
    return { restored_files: saved.input.files.map(f => f.name), url: page.url(), proof_status: await page.locator('#comparison-story').getAttribute('data-proof-status') };
  });
  await check('Worked result includes both energies, MSC codes and closed technical details', async () => {
    await readyRun();
    const story = await page.locator('#comparison-story').innerText();
    for (const fragment of ['Энергия ассоциатора', 'Энергия графа', '17C40', '05C50', 'd = [0, 2, 4]', 'f = [1, 0, 1]']) assert.ok(story.includes(fragment), 'Missing story text: ' + fragment);
    const calculations = await page.locator('.numeric-calculations code').allTextContents();
    assert.equal(calculations.length, 2);
    assert.ok(calculations.every(text => /=\s*2\s*$/.test(text)), 'Both numerical energies must equal 2');
    const disclosures = await page.locator('#lean-panel details').evaluateAll(nodes => nodes.map(node => ({ summary: node.querySelector('summary')?.textContent.trim(), open: node.open })));
    assert.ok(disclosures.length > 5);
    assert.ok(disclosures.every(d => !d.open), 'Technical detail unexpectedly open: ' + JSON.stringify(disclosures.filter(d => d.open)));
    return { calculations, disclosure_count: disclosures.length, all_closed: true };
  });
  await check('Map and comparison navigation plus reload retain saved run', async () => {
    await readyRun();
    await page.locator('[data-tab="map"]').click();
    assert.equal(new URL(page.url()).searchParams.get('run'), run);
    assert.equal(new URL(page.url()).hash, '#map');
    await page.reload();
    await page.locator('#comparison-story[data-proof-status="verified"]').waitFor({ state: 'attached' });
    assert.equal(new URL(page.url()).searchParams.get('run'), run);
    const tabAfterMapReload = new URL(page.url()).hash;
    await page.locator('[data-tab="lean"]').click();
    await page.reload();
    await page.locator('#comparison-story[data-proof-status="verified"]').waitFor();
    assert.equal(new URL(page.url()).searchParams.get('run'), run);
    return { map_reload_hash: tabAfterMapReload, lean_reload_hash: new URL(page.url()).hash, run_retained: true };
  });
  await check('Map reload keeps selected tab', async () => {
    await readyRun();
    await page.locator('[data-tab="map"]').click();
    await page.reload();
    await page.locator('#catalog-list button').first().waitFor({ state: 'attached' });
    await page.waitForLoadState('networkidle');
    assert.equal(new URL(page.url()).hash, '#map');
    assert.equal(await page.locator('#map-panel').isVisible(), true);
    return { hash: new URL(page.url()).hash };
  });
  await check('Search 05C50 selects exact category and full inventory remains visible', async () => {
    await readyMap();
    const stats = (await page.locator('#dataset-stats').innerText()).replace(/[\s\u00a0\u202f]/g, '');
    assert.ok(stats.includes('6603'), 'Missing 6603 in dataset inventory');
    await page.locator('#msc-search').fill('05C50');
    await page.locator('#catalog-list button').filter({ hasText: '05C50' }).first().click();
    await page.locator('#category-panel').getByText('Graphs and linear algebra (matrices, eigenvalues, etc.)', { exact: false }).first().waitFor();
    assert.ok((await page.locator('#breadcrumbs').innerText()).includes('05C50'));
    return { stats, category: '05C50', title: await page.locator('#graph-title').innerText() };
  });
  await check('Bridge edit clears comparison success and certificate panel', async () => {
    await readyRun();
    await openDetails('details.proof-source');
    await page.locator('#bridge-source').fill(saved.bridge_source + '\n-- UI regression edit; not submitted\n');
    assert.equal(await page.locator('#comparison-story').getAttribute('data-proof-status'), 'unverified');
    assert.equal(await page.locator('#comparison-story .badge.success').count(), 0);
    assert.equal(await page.locator('#verification-result .verification-card.success').count(), 0);
    assert.ok((await page.locator('#verification-result').innerText()).includes('новая проверка'));
    return { proof_status: 'unverified', prior_certificate_removed: true };
  });
  await check('Input edit marks story stale and disables verification', async () => {
    await readyRun();
    await openDetails('#input-details');
    await page.locator('#file-content-0').fill(saved.input.files[0].content + '\n-- UI regression edit; not submitted\n');
    assert.equal(await page.locator('#comparison-story').getAttribute('data-proof-status'), 'stale');
    assert.equal(await page.locator('#stale-notice').isVisible(), true);
    assert.equal(await page.locator('#verify-button').isDisabled(), true);
    assert.equal(await page.locator('#verification-result .verification-card.success').count(), 0);
    return { proof_status: 'stale', verify_disabled: true };
  });
  await check('Loading example inputs clears saved run and visible success', async () => {
    await readyRun();
    await openDetails('#input-details');
    await page.locator('#example-select').selectOption('astra-energy');
    await page.locator('#load-example').click();
    assert.equal(new URL(page.url()).searchParams.has('run'), false);
    assert.equal(await page.locator('#analysis-section').isVisible(), false);
    assert.equal(await page.locator('#bridge-section').isVisible(), false);
    assert.equal(await page.locator('#verification-result .verification-card.success').count(), 0);
    assert.equal(await page.locator('#comparison-story').isVisible(), false);
    return { run_cleared: true, success_visible: false };
  });
  await check('Dark OS keeps light UI and mobile layouts avoid horizontal overflow', async () => {
    await readyRun();
    const colors = await page.evaluate(() => ({ darkOS: matchMedia('(prefers-color-scheme: dark)').matches, scheme: getComputedStyle(document.documentElement).colorScheme, background: getComputedStyle(document.body).backgroundColor, foreground: getComputedStyle(document.body).color }));
    report.color_scheme = colors;
    assert.equal(colors.darkOS, true);
    assert.ok(colors.scheme.includes('light'));
    assert.equal(colors.background, 'rgb(255, 255, 255)');
    const sizes = [];
    report.mobile_measurements = sizes;
    for (const width of [390, 320]) {
      await page.setViewportSize({ width, height: 900 });
      for (const tab of ['lean', 'map']) {
        await page.locator('[data-tab="' + tab + '"]').click();
        await page.evaluate(() => new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve))));
        const measurement = await page.evaluate(() => ({ width: innerWidth, scrollWidth: document.documentElement.scrollWidth, overflowing: [...document.querySelectorAll('body *')].filter(n => { const r = n.getBoundingClientRect(); return r.width > 0 && (r.right > innerWidth + 1 || r.left < -1); }).slice(0, 8).map(n => n.tagName.toLowerCase() + (n.id ? '#' + n.id : '') + '.' + String(n.className).replace(/\s+/g, '.')) }));
        sizes.push({ tab, ...measurement });
        assert.ok(measurement.scrollWidth <= width, JSON.stringify(measurement));
      }
    }
    return { colors, sizes };
  });
  await check('Read-only code review: curated story verification requires matching Bridge hash', async () => {
    const code = fs.readFileSync(path.join(__dirname, 'web', 'app.js'), 'utf8');
    const guard = code.match(/verified\s*=\s*confirmedBridge\(\)\s*&&\s*\(!story\|\|state\.verification\.source_sha256===story\.bridge\.source_sha256\)/);
    assert.ok(guard, 'Expected story Bridge source hash guard absent; inspect current implementation');
    assert.ok(code.includes("f.sha256===story.bridge.input_sha256[f.name]"), 'Story lacks input-source hash guard');
    return { method: 'read-only source inspection; no fabricated verification results', bridge_guard: guard[0], input_hash_guard: true };
  });
  await check('No browser errors, failing HTTP responses or mutating requests', async () => {
    assert.deepEqual(report.browser_errors, []);
    assert.deepEqual(report.failed_http_requests, []);
    assert.deepEqual(report.unexpected_mutating_requests, []);
    return { browser_errors: 0, failed_http_requests: 0, mutating_requests: 0 };
  });
  report.passed = report.checks.every(check => check.passed);
  report.summary = { total: report.checks.length, passed: report.checks.filter(check => check.passed).length, failed: report.checks.filter(check => !check.passed).length };
  fs.mkdirSync(path.dirname(output), { recursive: true });
  fs.writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify({ output, ...report.summary, failures: report.checks.filter(check => !check.passed) }, null, 2));
  await browser.close();
  process.exitCode = report.passed ? 0 : 1;
})().catch(error => { console.error(error); process.exitCode = 1; });
