'use strict';

function programURL(mode, id) {
  const url = new URL(location.pathname, location.origin);
  url.hash = 'problems';
  if (mode === 'patterns') url.searchParams.set('workflow', 'patterns');
  if (mode === 'qed' && !id) url.searchParams.set('workflow', 'qed');
  if (id) url.searchParams.set(mode === 'qed' ? 'qed' : 'program', id);
  return url;
}

function navigateProgram(mode, id) {
  history.pushState(null, '', programURL(mode, id));
  window.MSCAtlas.route();
}

function parentProgramLink(run) {
  const context = run?.contract?.program_context;
  if (!context?.program_id) return null;
  const a = document.createElement('a');
  a.href = programURL(context.mode === 'patterns' ? 'patterns' : 'research', context.program_id);
  a.textContent = context.mode === 'patterns' ? 'Открыть поиск паттернов' : 'Открыть исследовательскую программу';
  return a;
}

function createProgramView(prefix) {
  const discovery = prefix === 'pattern';
  const mode = discovery ? 'patterns' : 'research';
  const $ = id => document.getElementById(prefix + '-' + id);
  const base = '/api/research/programs';
  const files = '/api/research/lean-files';
  const statusText = {
    running: 'В работе', queued: 'В очереди', ready: 'Готова к запуску', pending: 'Ожидает',
    complete: 'Завершена', completed: 'Завершена', paused: 'Приостановлена', interrupted: 'Прервана',
    stalled: 'Нет следующего шага', failed: 'Ошибка', cancelled: 'Остановлена',
    budget_exhausted: 'Лимит исчерпан', proved: 'Доказано', refuted: 'Опровергнуто',
    unknown: 'Остаётся открытым', verified: 'Тип и доказательство проверены', compiled: 'Lean скомпилировал исходники',
    blocked: 'Ожидает основания', open: 'Открыта', active: 'В работе', skipped: 'Пропущена',
    superseded: 'Гипотеза уже проверена'
  };
  const draft = new Map();
  let visible = false, activeId = null, current = null, timer, generation = 0;
  let queueTimer;
  let uploading = false, submitting = false, available = false, availabilityKnown = false;
  let contextSelected = false;
  function node(tag, text, className) {
    const element = document.createElement(tag);
    if (text !== undefined) element.textContent = text;
    if (className) element.className = className;
    return element;
  }
  function button(label, handler) {
    const element = node('button', label, 'button small secondary');
    element.type = 'button'; element.onclick = handler;
    return element;
  }
  function link(text, href) {
    const element = node('a', text); element.href = href; return element;
  }
  async function request(url, body) {
    const options = body === undefined ? {} : {
      method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body)
    };
    const response = await fetch(url, options);
    const data = await response.json();
    if (!response.ok) throw new Error(data.error || 'Не удалось выполнить запрос.');
    return data;
  }
  function error(message = '') {
    $('error').textContent = message; $('error').hidden = !message;
  }
  function controls() {
    $('check-file').disabled = uploading || submitting;
    $('start').disabled = uploading || submitting || !available;
    $('start').textContent = submitting ? 'Создаём запуск…' : (discovery ? 'Начать поиск паттернов' : 'Запустить программу');
    $('connection').textContent = !availabilityKnown ? 'Проверяем Astra…' :
      available ? 'Astra App Server подключён' : 'Astra недоступна. Проверка Lean работает локально.';
  }
  function diagnostics(item) {
    const details = node('details');
    details.append(node('summary', 'Отчёт Lean'));
    const lines = [item.error, ...(item.diagnostics || []).map(d =>
      typeof d === 'string' ? d : [d.file, d.stderr || d.stdout || d.message || (d.exit_code === 0 ? 'OK' : '')].filter(Boolean).join(' · ')
    )].filter(Boolean);
    if (item.target) lines.unshift(item.target + (item.target_preserved ? ' · тип подтверждён' : ''));
    if (item.kernel_recheck) lines.push(kernelCheckLabel(item.kernel_recheck));
    for (const check of item.checks || []) lines.push([check.target, check.target_preserved ? 'тип подтверждён' : check.error].filter(Boolean).join(' · '));
    (item.files || []).forEach(f => lines.push(f.name + ' · ' + f.sha256));
    details.append(node('pre', lines.join('\n') || statusText[item.status] || item.status));
    return details;
  }
  function kernelCheckLabel(check) {
    if (check.status === 'passed') return 'Ядро Lean повторно проверило декларации · ' + check.checked_count;
    if (check.status === 'failed') return 'Повторная проверка ядром Lean завершилась ошибкой';
    return 'Повторная проверка ядром Lean ожидается';
  }
  function leaseLabel(lease) {
    const expires = new Date(lease.expires_at * 1000);
    const until = expires.toLocaleTimeString('ru-RU', {hour:'2-digit', minute:'2-digit', second:'2-digit'});
    return lease.worker_id + ' · аренда до ' + until;
  }
  async function refreshQueue() {
    clearTimeout(queueTimer);
    const version = generation;
    if (!visible || !$('queue').open) return;
    try {
      const {tasks} = await request('/api/research/queue');
      if (version !== generation || !$('queue').open) return;
      const rows = tasks.map(task => {
        const url = programURL(task.mode, task.program_id);
        const a = link('', url);
        a.className = 'research-history-item';
        a.append(node('strong', task.task_id + ' · ' + (task.question || task.title || 'Задача')));
        a.append(node('span', task.worker_id ? leaseLabel(task) : 'Ожидает исполнителя', 'research-history-meta'));
        return a;
      });
      $('queue-rows').replaceChildren(...(rows.length ? rows : [node('p', 'Очередь пуста.', 'research-hint')]));
    } catch (e) {
      if (version === generation) $('queue-rows').replaceChildren(node('p', e.message, 'research-hint'));
    }
    if (version === generation && visible && $('queue').open) queueTimer = setTimeout(refreshQueue, 3500);
  }
  function fileCard(item, removable = false) {
    const card = node('div', undefined, 'program-file-card');
    const name = item.filename || item.name || 'Исходники Lean';
    card.append(link(name, files + '/' + item.id + '/download'));
    const state = node('p', statusText[item.status] || item.status || '', 'research-hint');
    const actions = node('div', undefined, 'program-actions');
    const rerun = button('Перепроверить', async () => {
      rerun.disabled = true; state.textContent = 'Lean повторно проверяет файлы…';
      try {
        const checked = await request(files + '/' + item.id + '/recheck', {});
        if (removable) { draft.set(item.id, checked); renderInputs(); }
        else card.replaceWith(fileCard(checked));
      } catch (e) { state.textContent = e.message; }
      finally { rerun.disabled = false; }
    });
    actions.append(rerun);
    if (removable && item.bundle_format) {
      (item.checks || []).forEach((check, index) => {
        const select = button('Взять в программу: ' + check.target, async () => {
          select.disabled = true; uploading = true; controls();
          try {
            const member = await request(files + '/' + item.id + '/members/' + index, {});
            draft.delete(item.id); draft.set(member.id, member); renderInputs();
          } catch (e) { state.textContent = e.message; }
          finally { uploading = false; select.disabled = false; controls(); }
        });
        actions.append(select);
      });
    }
    if (removable) actions.append(button('Убрать', () => { draft.delete(item.id); renderInputs(); }));
    card.append(state, diagnostics(item), actions);
    return card;
  }
  function renderInputs() { $('inputs').replaceChildren(...Array.from(draft.values(), item => fileCard(item, true))); }
  async function checkFile() {
    const file = $('file').files[0];
    if (!file) { $('file-message').textContent = 'Выберите .lean или .zip.'; return; }
    if (file.size > 2 * 1024 * 1024) { $('file-message').textContent = 'Максимальный размер загрузки — 2 МиБ.'; return; }
    const target = $('target').value.trim(), statement = $('statement').value.trim();
    if (Boolean(target) !== Boolean(statement)) {
      $('file-message').textContent = 'Для сверки укажите и имя теоремы, и её ожидаемый тип.'; return;
    }
    uploading = true; controls(); error(); $('file-message').textContent = 'Lean проверяет исходники…';
    try {
      const content = await new Promise((resolve, reject) => {
        const reader = new FileReader();
        reader.onload = () => resolve(reader.result.split(',')[1]);
        reader.onerror = () => reject(new Error('Не удалось прочитать файл.'));
        reader.readAsDataURL(file);
      });
      const item = await request(files, {filename: file.name, data: content, target, expected_statement: statement});
      draft.set(item.id, item); renderInputs();
      if (['verified','compiled'].includes(item.status) && !contextSelected) {
        $('context').value = '';
        if ($('question').value === $('question').defaultValue) $('question').value = '';
      }
      $('file').value = ''; $('target').value = ''; $('statement').value = '';
      $('file-message').textContent = item.status === 'failed' ? 'Откройте отчёт Lean, чтобы увидеть ошибку.' : '';
    } catch (e) { $('file-message').textContent = e.message; }
    finally { uploading = false; controls(); }
  }
  function taskCard(task) {
    const card = node('div', undefined, 'program-task');
    card.id = prefix + '-card-' + task.id;
    card.tabIndex = -1;
    card.append(node('strong', task.id + ' · ' + (task.question || task.target)));
    const kind = task.counterexample_for ? 'Независимый поиск контрпримера' :
      (task.direction === 'refute' ? 'Поиск опровержения' : 'Доказательство');
    const resolution = task.resolved_by && current.tasks.find(other => other.id === task.resolved_by);
    const outcome = resolution ? (statusText[resolution.outcome] || resolution.outcome) + ' в ' + resolution.id :
      task.status === 'complete' ? (statusText[task.outcome] || task.outcome) : '';
    card.append(node('p', [kind, statusText[task.status] || task.status, outcome].filter(Boolean).join(' · '), 'research-hint'));
    if (task.counterexample_skipped) card.append(node('p', task.counterexample_skipped, 'research-hint'));
    if (task.lease?.worker_id) card.append(node('p', leaseLabel(task.lease), 'research-hint program-task-lease'));
    if (task.kernel_recheck) card.append(node('p', kernelCheckLabel(task.kernel_recheck), 'research-hint'));
    if (discovery && task.pattern) {
      card.append(node('p', task.pattern));
      const basis = node('div', undefined, 'pattern-basis');
      basis.append(node('span', 'Основания гипотезы', 'research-hint'));
      const seeds = new Map((current.pattern_sources || []).map(s => [s.id, s]));
      for (const id of task.source_ids || []) {
        const source = seeds.get(id);
        if (source) basis.append(sourceLink(source));
      }
      card.append(basis);
    }
    if (task.reason && task.reason !== task.pattern) card.append(node('p', task.reason));
    if (task.diagnostics && task.diagnostics !== task.reason) card.append(node('p', task.diagnostics));
    const assessment = task.semantic_review?.reason;
    if (assessment && assessment !== task.diagnostics && assessment !== task.reason) card.append(node('p', assessment));
    if (task.source_check) card.append(node('p', [task.source_check.reason, ...(task.source_check.declarations || [])].filter(Boolean).join(' · ')));
    const details = node('details');
    details.append(node('summary', 'Формальная постановка'), node('pre', [task.target, task.statement].filter(Boolean).join('\n')));
    card.append(details);
    const actions = node('div', undefined, 'program-actions');
    const paired = task.counterexample_for || task.counterexample_task_id;
    if (paired) {
      const label = (task.counterexample_for ? 'Исходная гипотеза ' : 'Попытка опровержения ') + paired;
      actions.append(button(label, () => document.getElementById(prefix + '-card-' + paired)?.focus()));
    }
    if (task.sketch_run_id) actions.append(link('Эскиз QED', '/?qed=' + encodeURIComponent(task.sketch_run_id) + '#problems'));
    if (task.run_id) {
      const runURL = '/api/research/runs/' + encodeURIComponent(task.run_id);
      actions.append(link('Ход попытки', '/?research=' + encodeURIComponent(task.run_id) + '#research'));
      if (['proved','refuted'].includes(task.formal_outcome) || ['proved','refuted'].includes(task.outcome)) {
        actions.append(link('Скачать Lean', runURL + '/lean'));
        const message = node('span', '', 'research-hint');
        const verify = button('Перепроверить Lean', async () => {
          verify.disabled = true; message.textContent = 'Идёт проверка…';
          try {
            const result = await request(runURL + '/lean/recheck', {});
            message.textContent = statusText[result.status] || result.status;
            card.append(diagnostics(result));
          } catch (e) { message.textContent = e.message; }
          finally { verify.disabled = false; }
        });
        actions.append(verify, message);
      }
    }
    card.append(actions);
    for (const dep of task.library_dependencies || []) {
      card.append(node('p', 'Использованная лемма: ' + dep.source));
      if (dep.source_run_id) card.append(link('Исходная попытка', '/?research=' + encodeURIComponent(dep.source_run_id) + '#research'));
    }
    return card;
  }
  function sourceLink(source) {
    const label = source.name || source.id;
    if (typeof source.url === 'string' && source.url.startsWith('/api/research/')) return link(label, source.url);
    if (source.source_run_id) return link(label, '/?research=' + encodeURIComponent(source.source_run_id) + '#research');
    if (source.attachment_id) return link(label, files + '/' + encodeURIComponent(source.attachment_id) + '/download');
    return node('span', label);
  }
  function renderEvidence(items) {
    const box = $('evidence');
    const signature = JSON.stringify(items);
    if (box.dataset.key === signature) return;
    box.dataset.key = signature;
    box.replaceChildren();
    if (!items.length) return;
    box.append(node('h3', 'Исходные утверждения'));
    for (const item of items) {
      const row = node('details', undefined, 'pattern-source');
      row.dataset.sourceId = item.id;
      const summary = node('summary', item.name || item.id);
      const origin = item.kind === 'mathlib' ? ['mathlib',item.module].filter(Boolean).join(' · ') :
        (item.kind === 'archive' ? 'Архив SHAIM' : 'Файл Lean');
      summary.append(node('span', origin, 'pattern-source-kind'));
      row.append(summary, node('pre', item.statement), sourceLink(item));
      box.append(row);
    }
  }
  async function action(name, payload = {}) {
    const id = activeId, version = generation;
    try {
      const data = await request(base + '/' + id + '/' + name, payload);
      if (generation === version) { render(data); poll(); list(); }
    } catch (e) { if (generation === version) error(e.message); }
  }
  function render(data) {
    current = data;
    $('form').hidden = true; $('detail').hidden = false;
    $('title').textContent = data.question || data.title;
    const usage = data.usage || {};
    $('status').textContent = [statusText[data.status] || data.status,
      'Вызовы Astra ' + (usage.calls || 0) + ' / ' + data.budget.max_calls,
      Math.round(usage.elapsed_seconds || 0) + ' с / ' + data.budget.timeout_seconds + ' с'].join(' · ');
    $('reason').textContent = data.reason || '';
    if (discovery) renderEvidence(data.pattern_sources || []);
    const tasks = data.tasks || [];
    // A heartbeat only changes the lease clock. Keep open details and keyboard focus.
    const signature = JSON.stringify(tasks, (key, value) => key === 'expires_at' ? undefined : value);
    if ($('tasks').dataset.signature !== signature) {
      $('tasks').replaceChildren(...(tasks.length ? tasks.map(taskCard) : [node('p', 'Координатор выбирает следующую задачу.', 'research-hint')]));
      $('tasks').dataset.signature = signature;
    } else {
      for (const task of tasks) {
        const lease = document.getElementById(prefix + '-card-' + task.id)?.querySelector('.program-task-lease');
        if (lease && task.lease) lease.textContent = leaseLabel(task.lease);
      }
    }
    $('actions').replaceChildren();
    if (['running','queued'].includes(data.status)) $('actions').append(button('Остановить', () => action('cancel')));
    if (['paused','interrupted'].includes(data.status)) $('actions').append(button('Продолжить', () => action('resume')));
    if (discovery && ['complete','stalled','budget_exhausted'].includes(data.status)) {
      const next = button('Искать дальше', () => {
        next.disabled = true;
        action('continue', {generation:data.pattern_generation || 0, budget:{max_calls:12,timeout_seconds:600}})
          .finally(() => { next.disabled = false; });
      });
      $('actions').append(next, node('span', 'Ещё две гипотезы · до 12 вызовов Astra и 10 минут', 'research-hint'));
    }
    const accepted = tasks.filter(t => ['proved','refuted'].includes(t.formal_outcome));
    if (accepted.length) {
      const archive = accepted.length > 1 || accepted.some(t => ['verified','unrelated'].includes(t.source_check?.status));
      $('actions').append(link(archive ? 'Скачать исходники ZIP' : 'Скачать исходник .lean', base + '/' + data.id + '/lean'));
    }
    $('log').querySelector('ol').replaceChildren(...(data.events || []).map(e =>
      node('li', e.task_id ? e.task_id + ' · ' + e.message : e.message)));
    const sources = data.sources || [], srcKey = JSON.stringify(sources.map(s => s.id));
    if ($('sources').dataset.key !== srcKey) {
      $('sources').replaceChildren();
      if (sources.length) $('sources').append(node('h3', 'Исходные файлы'), ...sources.map(s => fileCard(s)));
      $('sources').dataset.key = srcKey;
    }
  }
  function poll() {
    clearTimeout(timer);
    if (!visible || !activeId || (current && !['queued','running'].includes(current.status))) return;
    const id = activeId, version = generation;
    timer = setTimeout(async () => {
      try {
        const detail = await request(base + '/' + id);
        if (generation !== version) return;
        render(detail);
        if (!['queued','running'].includes(detail.status)) list();
      } catch (e) { if (generation === version) error(e.message); }
      if (generation === version) poll();
    }, 1400);
  }
  async function list() {
    const version = generation;
    try {
      const {programs} = await request(base + '?mode=' + mode);
      if (version !== generation) return;
      const rows = programs.filter(p => (p.mode || 'research') === mode).map(p => {
        const a = link('', programURL(mode, p.id)); a.className = 'research-history-item' + (p.id === activeId ? ' selected' : '');
        a.append(node('strong', p.title || p.question), node('span', statusText[p.status] || p.status, 'research-history-meta'));
        a.onclick = e => { if (e.metaKey || e.ctrlKey || e.shiftKey) return; e.preventDefault(); navigateProgram(mode, p.id); };
        return a;
      });
      $('history').replaceChildren(...(rows.length ? rows : [node('p', 'Запусков пока нет.', 'research-hint')]));
    } catch (e) { if (generation === version) error(e.message); }
  }
  async function open(id) {
    const version = generation;
    error(); $('detail').hidden = true; $('form').hidden = Boolean(id);
    if (!id) return;
    try {
      const data = await request(base + '/' + id);
      if (version === generation) {
        if ((data.mode || 'research') !== mode) {
          location.replace(programURL(data.mode === 'patterns' ? 'patterns' : 'research', id));
          return;
        }
        render(data); poll();
      }
    } catch (e) { if (version === generation) { error(e.message); $('form').hidden = false; } }
  }
  function show(id) {
    if (visible && id === activeId) return;
    visible = true; activeId = id; ++generation; clearTimeout(timer); current = null;
    open(id); list(); controls(); refreshQueue();
    request('/api/research/status').then(s => { available = s.codex?.available === true; })
      .catch(() => { available = false; }).finally(() => { availabilityKnown = true; controls(); });
  }
  $('form').onsubmit = async event => {
    event.preventDefault(); if (submitting || uploading || !available) return;
    if ($('file').files.length) { error('Сначала нажмите «Проверить файл» для выбранного исходника.'); return; }
    if ([...draft.values()].some(s => !['verified','compiled'].includes(s.status))) { error('Уберите исходники с ошибками перед запуском.'); return; }
    if (draft.size && [...draft.values()].every(s => s.bundle_format)) { error('Выберите результат архива кнопкой «Взять в программу».'); return; }
    const version = generation; submitting = true; controls(); error();
    try {
      const payload = {
        question: $('question').value.trim(), context_case_id: $('context').value || null,
        use_qed: $('qed').checked, counterexample_search: $('counterexample').checked, attachment_ids: [...draft.keys()],
        budget: {max_calls: Number($('calls').value), timeout_seconds: Number($('seconds').value)}
      };
      if (discovery) {
        payload.mode = mode;
        payload.msc_codes = $('msc').value.toUpperCase().split(/[\s,;]+/).filter(Boolean);
      }
      const program = await request(base, payload);
      if (generation === version) { draft.clear(); renderInputs(); navigateProgram(mode, program.id); }
    } catch (e) { if (generation === version) error(e.message); }
    finally { submitting = false; controls(); }
  };
  $('new').onclick = () => navigateProgram(mode, null);
  $('context').onchange = () => { contextSelected = true; };
  $('check-file').onclick = checkFile;
  $('queue').ontoggle = refreshQueue;
  if (discovery) {
    for (const field of [$('msc'), $('question')]) field.oninput = () => {
      if (!contextSelected && field.value.trim()) $('context').value = '';
    };
  }
  return {show, currentId() { return activeId; }, hide() {
    if (visible) { visible = false; ++generation; clearTimeout(timer); clearTimeout(queueTimer); }
  }};
}

(() => {
  const element = id => document.getElementById(id);
  // Both views use the same run controls, Lean attachments and task detail.
  // Each instance owns its draft and polling state when the user switches modes.
  const layout = element('program-workspace').cloneNode(true);
  layout.id = 'pattern-workspace';
  for (const child of layout.querySelectorAll('[id],[for]')) {
    for (const attr of ['id','for']) {
      if (child.hasAttribute(attr)) child.setAttribute(attr, child.getAttribute(attr).replace(/^program-/, 'pattern-'));
    }
  }
  layout.querySelector('.program-focus-fields').replaceChildren(element('pattern-fields').content.cloneNode(true));
  const evidence = document.createElement('section');
  evidence.id = 'pattern-evidence';
  layout.querySelector('#pattern-sources').before(evidence);
  layout.querySelector('#pattern-detail section h3').textContent = 'Предложенные гипотезы';
  layout.querySelector('.program-history-title h2').textContent = 'История поисков';
  layout.querySelector('#pattern-new').textContent = '＋ Новый поиск';
  element('pattern-slot').append(layout);

  const research = createProgramView('program'), patterns = createProgramView('pattern');
  element('mode-program').onclick = () => navigateProgram('research', research.currentId());
  element('mode-qed').onclick = () => navigateProgram('qed', window.QEDWorkspace.currentId());
  element('mode-pattern-discovery').onclick = () => navigateProgram('patterns', patterns.currentId());
  window.ProgramWorkspace = {
    show(tab) {
      const query = new URL(location.href).searchParams;
      const isPatterns = tab === 'problems' && (query.get('workflow') === 'patterns' || query.has('pattern'));
      const isQED = tab === 'problems' && (query.has('qed') || query.get('workflow') === 'qed');
      const isResearch = tab === 'problems' && !isQED && !isPatterns;
      element('pattern-slot').hidden = !isPatterns;
      element('program-workspace').hidden = !isResearch;
      element('qed-workspace').hidden = !isQED;
      for (const [id, active] of [['program',isResearch],['qed',isQED],['pattern-discovery',isPatterns]]) {
        element('mode-' + id).setAttribute('aria-pressed',String(active));
      }
      if (isPatterns) patterns.show(query.get('program') || query.get('pattern')); else patterns.hide();
      if (isResearch) research.show(query.get('program')); else research.hide();
      if (isQED) window.QEDWorkspace.show();
      else {
        window.QEDWorkspace.hide(); element('qed-error').hidden = true; element('qed-new').hidden = true;
      }
    }
  };
})();
