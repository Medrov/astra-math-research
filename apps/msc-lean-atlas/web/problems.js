'use strict';

(() => {
  const $ = id => document.getElementById('qed-' + id);
  const runsURL = '/api/research/runs';
  const runURL = id => runsURL + '/' + encodeURIComponent(id);
  const ongoing = new Set(['queued', 'running', 'cancelling']);
  const statuses = {
    queued: 'В очереди', running: 'В работе', cancelling: 'Останавливается', complete: 'Завершено',
    completed: 'Завершено', cancelled: 'Остановлено', interrupted: 'Прервано', failed: 'Ошибка',
    budget_exhausted: 'Лимит исчерпан', timeout: 'Истекло время', needs_review: 'Требуется проверка'
  };
  const roles = {
    qed_survey: 'Обзор задачи', qed_plan: 'План доказательства', qed_prove: 'Доказательство',
    qed_structural: 'Проверка структуры', qed_verdict: 'Вердикт рецензента',
    qed_detailed: 'Проверка деталей', qed_regulator: 'Выбор исправления', qed_summary: 'Итоги поиска'
  };
  const levels = {Easy: 'простая', Medium: 'средняя', Hard: 'сложная'};
  const reviews = {
    unreviewed: 'Без отдельной рецензии', model_reviewed: 'Прошло рецензию Astra',
    changes_requested: 'У рецензента остались замечания'
  };
  const stageVerdicts = {
    PASS: 'Принято', FAIL: 'Есть замечания', DONE: 'Проверка пройдена', CONTINUE: 'Требуется доработка',
    REVISE_PROOF: 'Исправить доказательство', REVISE_PLAN: 'Уточнить план', REWRITE: 'Сменить подход'
  };
  let visible = false, ready = false, busy = false, generation = 0, timer;
  let cases = [], historyRows = [], run = null, initialized = false;
  const stepElements = new Map();

  function element(tag, text, className) {
    const node = document.createElement(tag);
    if (text !== undefined) node.textContent = text;
    if (className) node.className = className;
    return node;
  }

  async function api(url, body) {
    const response = await fetch(url, body === undefined ? {} : {
      method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body)
    });
    const data = await response.json();
    if (!response.ok) throw new Error(data.error || 'Ошибка сервера ' + response.status);
    return data;
  }

  function error(message = '') {
    $('error').textContent = message;
    $('error').hidden = !message;
  }

  function math(source, display) {
    const span = element('span', source, display ? 'qed-equation' : 'qed-inline-math');
    if (window.katex) {
      try {
        window.katex.render(source, span, {output: 'mathml', displayMode: display, trust: false, maxSize: 20, maxExpand: 500, strict: 'ignore'});
      } catch { span.textContent = source; }
    }
    return span;
  }

  // Build DOM from model text. Only the formula parser produces MathML.
  function inline(node, text) {
    const tokens = /\x60([^\x60\n]+)\x60|\*\*([^\n]+?)\*\*|\\\(([\s\S]*?)\\\)|\$([^$\n]+?)\$/g;
    let previous = 0;
    for (const match of text.matchAll(tokens)) {
      node.append(text.slice(previous, match.index));
      if (match[1] !== undefined) node.append(element('code', match[1]));
      else if (match[2] !== undefined) {
        const strong = element('strong');
        inline(strong, match[2]); node.append(strong);
      } else node.append(math(match[3] ?? match[4], false));
      previous = match.index + match[0].length;
    }
    node.append(text.slice(previous));
  }

  function paragraphs(box, source) {
    let paragraph = [], list;
    const flush = () => {
      if (paragraph.length) {
        const p = element('p'); inline(p, paragraph.join('\n')); box.append(p); paragraph = [];
      }
    };
    for (const line of source.split('\n')) {
      const heading = line.match(/^ {0,3}#{1,6}\s+(.+)$/);
      const item = line.match(/^\s*(?:([-*])|(\d+)[.)])\s+(.+)$/);
      if (heading) {
        flush(); list = null;
        const h = element('h4'); inline(h, heading[1]); box.append(h);
      } else if (item) {
        flush();
        const tag = item[1] ? 'ul' : 'ol';
        if (!list || list.localName !== tag) {
          list = element(tag); if (tag === 'ol') list.start = Number(item[2]); box.append(list);
        }
        const li = element('li'); inline(li, item[3]); list.append(li);
      } else if (!line.trim()) { flush(); list = null; }
      else { list = null; paragraph.push(line); }
    }
    flush();
  }

  function prose(box, value) {
    const source = String(value || '').replace(/\r\n?/g, '\n');
    if (box.proseSource === source) return;
    box.proseSource = source;
    box.replaceChildren();
    const blocks = /(?:^|\n)\x60{3}[^\n]*\n([\s\S]*?)(?:\n\x60{3}|$)|\\\[([\s\S]*?)\\\]|\$\$([\s\S]*?)\$\$/g;
    let previous = 0;
    for (const match of source.matchAll(blocks)) {
      paragraphs(box, source.slice(previous, match.index));
      box.append(match[1] !== undefined ? element('pre', match[1]) : math(match[2] ?? match[3], true));
      previous = match.index + match[0].length;
    }
    paragraphs(box, source.slice(previous));
  }

  function setURL(id) {
    history.replaceState(null, '', programURL('qed', id));
  }

  function toggleControls() {
    $('start').disabled = busy || !ready;
    $('start').textContent = busy ? 'Создаём запуск…' : 'Запустить QED';
    $('new').disabled = busy;
    $('cancel').disabled = busy || run?.cancel_requested;
    $('resume').disabled = busy || !ready;
  }

  function selectCase() {
    const selected = cases.find(item => item.id === $('case').value);
    $('custom').hidden = Boolean(selected);
    $('question').required = !selected;
    $('question').disabled = Boolean(selected);
    $('preset').hidden = !selected;
    if (!selected) return;
    $('claim').textContent = selected.claim;
    const task = selected.agent_task || {};
    $('statement').textContent = [task.context, task.prelude, task.statement].filter(Boolean).join('\n\n');
    $('contract').hidden = !$('statement').textContent;
    $('contract').open = false;
  }

  function renderHistory() {
    const box = $('history');
    box.replaceChildren();
    if (!historyRows.length) box.append(element('p', 'Запусков пока нет.', 'research-hint'));
    for (const row of historyRows) {
      const a = element('a', undefined, 'research-history-item' + (run?.id === row.id ? ' selected' : ''));
      a.href = programURL('qed', row.id).href;
      if (run?.id === row.id) a.setAttribute('aria-current', 'page');
      a.append(element('strong', row.title));
      const date = new Date(row.created_at).toLocaleString('ru-RU', {day:'2-digit',month:'2-digit',hour:'2-digit',minute:'2-digit'});
      const route = row.qed_route || row.contract?.qed_route || 'auto';
      a.append(element('span', [statuses[row.status] || row.status, route === 'full' ? 'С рецензией' : 'По сложности', date].join(' · '), 'research-history-meta'));
      a.onclick = event => {
        if (event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
        event.preventDefault(); if (!busy) openRun(row.id);
      };
      box.append(a);
    }
  }

  function streamText(raw) {
    if (!raw.trimStart().startsWith('{')) return raw;
    const parts = [];
    // Consume whole JSON string tokens so quoted words inside a proof cannot
    // turn into field names. In a partial token keep only complete escapes.
    const tokens = /"((?:[^"\\]|\\.)*)(?:"|$)/gs;
    for (const key of raw.matchAll(tokens)) {
      const start = key.index + key[0].length;
      if (!['body', 'proof', 'decision'].includes(key[1]) || !/^\s*:/.test(raw.slice(start))) continue;
      const value = raw.slice(start).match(/^\s*:\s*"((?:[^"\\]|\\.)*)/s);
      if (!value) continue;
      const complete = value[1].replace(/(^|[^\\])((?:\\\\)*)\\u[\da-f]{0,3}$/i, '$1$2');
      try {
        const decoded = JSON.parse('"' + complete + '"');
        if (decoded) parts.push(decoded);
      } catch { /* Wait for the remainder of a JSON escape. */ }
    }
    return parts.join('\n\n');
  }

  function renderStep(attempt, step) {
    const id = attempt.id;
    let details = stepElements.get(id);
    if (!details) {
      details = element('details', undefined, 'qed-step');
      details.append(element('summary'), element('div', undefined, 'qed-prose'));
      details.open = attempt.status === 'running';
      stepElements.set(id, details); $('steps').append(details);
    }
    const title = step?.title || roles[attempt.role] || attempt.role;
    const verdict = step?.assessment || step?.decision;
    details.querySelector('summary').textContent = title + ' · ' + (stageVerdicts[verdict] || statuses[attempt.status] || attempt.status);
    const body = details.querySelector('.qed-prose');
    const message = step?.body || streamText(attempt.live_text || '');
    prose(body, message || attempt.error || (attempt.status === 'running' ? 'Ожидаем ответ Astra…' : 'Ответ отсутствует.'));
  }

  function render() {
    $('form').hidden = Boolean(run); $('run').hidden = !run; $('new').hidden = !run;
    toggleControls();
    if (!run) { renderHistory(); return; }
    const result = run.result || {}, workflow = run.qed || {}, usage = run.usage || {};
    const difficulty = levels[result.difficulty || workflow.difficulty];
    const status = statuses[run.status] || run.status;
    const phase = ongoing.has(run.status) ? roles[run.phase] : '';
    $('run-title').textContent = run.title;
    $('progress').dataset.state = run.status;
    const route = run.contract?.qed_route === 'full' ? 'С планом и рецензированием' : '';
    $('progress-text').textContent = [status, phase, route, difficulty && ('Сложность — ' + difficulty)].filter(Boolean).join(' · ');
    $('usage').textContent = [`Вызовы ${usage.calls || 0}/${run.budget.max_calls}`, usage.total_tokens ? new Intl.NumberFormat('ru-RU').format(usage.total_tokens) + ' токенов' : ''].filter(Boolean).join(' · ');
    $('cancel').hidden = !ongoing.has(run.status);
    $('show-work').hidden = !(run.attempts || []).length;
    $('resume').hidden = run.can_resume !== true;
    prose($('run-question'), run.contract?.question || run.claim);
    const parent = parentProgramLink(run);
    if (parent) $('run-question').append(parent);
    const proof = result.proof || workflow.proof;
    const answer = result.answer_kind || workflow.answer_kind;
    const final = run.status === 'complete';
    const title = {proof:'Доказательство', counterexample:'Контрпример', inconclusive:'Что удалось установить'}[answer] || 'Решение';
    $('result').hidden = !proof && !result.summary && !run.error;
    $('result-title').textContent = proof ? (final ? title : 'Промежуточное решение') : 'Итог запуска';
    $('review').textContent = proof ? [reviews[result.review || workflow.review], 'Текстовый результат без проверки Lean'].filter(Boolean).join(' · ') : '';
    prose($('proof'), [proof || result.summary, run.error].filter(Boolean).join('\n\n'));
    const steps = new Map((workflow.steps || []).map(step => [step.key, step]));
    for (const attempt of run.attempts || []) renderStep(attempt, steps.get(attempt.id));
    if (!(run.attempts || []).length) $('steps').textContent = 'Ожидаем первый этап…';
    else if ($('steps').firstChild?.nodeType === Node.TEXT_NODE) $('steps').firstChild.remove();
    const events = $('events').querySelector('ol');
    if (events.children.length !== (run.events || []).length) {
      events.replaceChildren();
      for (const item of run.events || []) {
        const time = new Date(item.at).toLocaleTimeString('ru-RU');
        events.append(element('li', time + ' · ' + (item.message || item.phase)));
      }
    }
    $('events').hidden = !events.children.length;
  }

  function clearRun() {
    run = null; clearTimeout(timer); stepElements.clear(); $('steps').replaceChildren();
    $('events').open = false; $('events').querySelector('ol').replaceChildren(); render();
  }

  function record(data) {
    const changed = !run || run.id !== data.id || run.status !== data.status;
    run = data;
    const index = historyRows.findIndex(row => row.id === data.id);
    if (index >= 0) historyRows[index] = data;
    else historyRows.unshift(data);
    render(); if (changed) renderHistory();
    poll();
  }

  function poll() {
    clearTimeout(timer);
    if (!visible || !run || !ongoing.has(run.status)) return;
    const id = run.id, request = generation;
    timer = setTimeout(async () => {
      try {
        const data = await api(runURL(id));
        if (!visible || request !== generation) return;
        error(); record(data.run || data);
      } catch (e) { if (visible && request === generation) { error(e.message); poll(); } }
    }, 1300);
  }

  async function openRun(id) {
    const request = ++generation;
    clearRun(); error();
    try {
      const data = await api(runURL(id)), selected = data.run || data;
      if (!visible || request !== generation) return;
      if (selected.mode !== 'qed') throw new Error('Этот запуск можно открыть в разделе «Исследования».');
      setURL(id); record(selected);
    } catch (e) { if (visible && request === generation) error(e.message); }
  }

  async function availability() {
    try {
      const data = await api('/api/research/status');
      ready = data.codex?.available === true;
      $('connection').textContent = ready ? 'Astra App Server подключён' : (data.codex?.error || 'Astra App Server недоступен');
    } catch (e) { ready = false; $('connection').textContent = 'Astra App Server недоступен. ' + e.message; }
    toggleControls();
  }

  async function historyList() {
    const data = await api(runsURL + '?mode=qed');
    historyRows = (data.runs || []).filter(row => row.mode === 'qed');
    renderHistory();
  }

  async function inputs() {
    const data = await api('/api/research/cases');
    cases = data.cases || [];
    const custom = $('case').querySelector('option[value="custom"]');
    $('case').replaceChildren(...cases.map(c => new Option(c.title, c.id)), custom);
    // Preserve a custom draft while the catalog loads.
    $('case').value = $('question').value || !cases.length ? 'custom' : cases[0].id;
    selectCase(); initialized = true;
  }

  async function reload() {
    const tasks = [historyList(), availability()];
    if (!initialized) tasks.push(inputs());
    const values = await Promise.allSettled(tasks);
    const failed = values.find(value => value.status === 'rejected');
    if (visible && failed) error(failed.reason.message);
  }

  $('form').onsubmit = async event => {
    event.preventDefault();
    if (busy || !ready) return;
    const payload = {mode: 'qed', qed_route: $('route').value, budget: {max_calls: Number($('calls').value), timeout_seconds: Number($('seconds').value)}};
    if ($('case').value === 'custom') {
      payload.question = $('question').value.trim();
      if (payload.question.length < 5) { error('Укажите задачу длиной от 5 символов.'); return; }
    } else payload.case_id = $('case').value;
    const request = ++generation;
    busy = true; toggleControls(); error();
    try {
      const data = await api(runsURL, payload), created = data.run || data;
      if (visible && request === generation) { setURL(created.id); record(created); }
    } catch (e) { if (visible && request === generation) error(e.message); }
    finally { busy = false; toggleControls(); }
  };

  async function action(name) {
    if (busy || !run) return;
    const id = run.id, request = ++generation;
    clearTimeout(timer); busy = true; toggleControls(); error();
    try {
      const data = await api(runURL(id) + '/' + name, {});
      if (visible && request === generation) record(data.run || data);
    } catch (e) { if (visible && request === generation) error(e.message); }
    finally { busy = false; toggleControls(); if (request === generation) poll(); }
  }

  $('case').onchange = selectCase;
  $('new').onclick = () => { ++generation; clearRun(); setURL(null); error(); $('case').focus(); };
  $('refresh').onclick = () => { error(); reload(); };
  $('cancel').onclick = () => action('cancel');
  $('show-work').onclick = () => {
    const heading = $('work-heading');
    heading.focus({preventScroll: true});
    heading.scrollIntoView({block: 'start'});
  };
  $('resume').onclick = () => action('resume');
  window.QEDWorkspace = {
    show() {
      const id = new URL(location.href).searchParams.get('qed');
      if (!visible) { visible = true; reload(); }
      if (id && run?.id !== id) openRun(id);
      else if (!id && run) clearRun();
      else { $('new').hidden = !run; poll(); }
    },
    hide() { if (visible) { visible = false; ++generation; clearTimeout(timer); } },
    currentId() { return run?.id; }
  };
})();
