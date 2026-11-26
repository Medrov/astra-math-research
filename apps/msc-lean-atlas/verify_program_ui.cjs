/* Verify the visible Lean download/recheck workflow against saved, real programs.
   Does not start Astra. Pass one or more completed program IDs on the command line. */
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const os = require('node:os');
const path = require('node:path');
const {chromium} = require(process.env.ATLAS_PLAYWRIGHT_MODULE || 'playwright');

async function main() {
  const ids = process.argv.slice(2);
  assert.ok(ids.length && ids.every(id => /^[0-9a-f]{32}$/.test(id)), 'Pass completed program IDs');
  const origin = process.env.ATLAS_BASE_URL || 'http://127.0.0.1:8765';
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'amr-program-ui-'));
  const browser = await chromium.launch();
  const errors = [];
  try {
    const page = await browser.newPage({viewport: {width: 1200, height: 860}});
    page.setDefaultTimeout(120000);
    page.on('pageerror', error => errors.push(error.message));
    for (const id of ids) {
      const url = origin + '/?program=' + id + '#problems';
      await page.goto(url);
      const tasks = page.locator('#program-tasks .program-task');
      await tasks.first().waitFor();
      await page.reload();
      const first = tasks.filter({has: page.getByRole('button', {name:'Перепроверить Lean'})}).first();
      const [checked] = await Promise.all([
        page.waitForResponse(response => response.request().method() === 'POST' && response.url().endsWith('/lean/recheck')),
        first.getByRole('button', {name:'Перепроверить Lean'}).click()
      ]);
      assert.ok(checked.ok(), await checked.text());
      assert.equal((await checked.json()).status, 'verified');
      await first.getByText('Тип и доказательство проверены', {exact:true}).waitFor();
      const action = page.locator('#program-actions a');
      const downloadEvent = page.waitForEvent('download');
      await action.click();
      const download = await downloadEvent;
      const name = download.suggestedFilename();
      const file = path.join(dir, name);
      await download.saveAs(file);
      await page.locator('#program-new').click();
      await page.locator('#program-file').setInputFiles(file);
      await page.locator('#program-check-file').click();
      const result = page.locator('#program-inputs .program-file-card').last();
      await result.getByText('Lean скомпилировал исходники', {exact:true}).waitFor();
      const select = result.getByRole('button', {name:/Взять в программу/});
      const members = await select.count();
      if (members) {
        await select.first().click();
        await page.waitForFunction(() => !document.querySelector('#program-inputs').textContent.includes('Взять в программу'));
      }
      await result.getByRole('button', {name:'Убрать'}).click();
      await page.locator('#mode-qed').click();
      await page.locator('#qed-form').waitFor();
      await page.locator('#mode-program').click();
      await page.locator('#program-form').waitFor();
      console.log(JSON.stringify({program:id, file:name, independent_members:members, result:'passed'}));
    }
    await page.setViewportSize({width:390,height:844});
    await page.goto(origin + '/#problems');
    await page.locator('#program-form').waitFor();
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true);
    assert.deepEqual(errors, []);
  } finally {
    await browser.close();
    await fs.rm(dir, {recursive:true, force:true});
  }
}
main().catch(error => { console.error(error); process.exitCode=1; });
