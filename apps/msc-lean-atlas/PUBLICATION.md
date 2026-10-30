# Состав публикации и воспроизведение

Лаборатория находится в `apps/msc-lean-atlas/` того же репозитория
`Medrov/astra-math-research`. Это переносимое локальное приложение с Python-сервером,
готовыми frontend-ресурсами, полной выгрузкой MSC2020, импортом arXiv, графами
объектов/лемм и отдельной проверкой Lean.

## Два основных примера

| ID | Источник и область |
|---|---|
| `arxiv_2610_38474_graph_subtraction` | A. S. Frolov, I. S. Dorofeev, [arXiv:2610.38474v1](https://arxiv.org/abs/2610.38474v1), заключительный шаг §9.1. В [examples/arxiv_graph_subtraction](examples/arxiv_graph_subtraction/README.md) находятся исходник, граф объектов и явные ограничения. |
| `published_associator_laplacian` | Наш ранее опубликованный [препринт v1.5](../../docs/Preprint.pdf), связь энергии диагонального ассоциатора и лапласиана в рациональной координатной модели. [PublishedAssociator.lean](research_fixtures/PublishedAssociator.lean) сохраняет два адаптера из [examples/astra_energy](examples/astra_energy/) и использует точную существующую теорему `associatorDirichlet_graphLaplacian`. |

Основной интерфейс предлагает эти два примера. Прежние учебные и отрицательные
контроли остаются во внутренних тестах. Исторический комплект `MathResearch`
из 11 исходников и 149 деклараций сохранён отдельно; его три исследовательские
ветви не переименованы в два новых результата.

## Что включено и что создаётся локально

В Git входят исходники приложения, документация, MSC с атрибуцией, закреплённые
списки зависимостей, готовая сборка графовых библиотек, Lean-примеры, тесты и
выбранные переносимые отчёты. Для установки следуйте
[корневому README](../../README.md) или [README приложения](README.md).

`research_data/`, `.venv/`, `node_modules/`, рабочие `runs/` и `verification/`
создаются на компьютере пользователя и не публикуются. В репозиторий не входят
учётные данные, Codex session IDs, локальные SQLite-базы, полный HTML импортированных
статей и журналы модельных диалогов. arXiv импортируется по явной ссылке после
клонирования; ссылки, версии, локаторы и хеши в переносимых отчётах позволяют
сверить происхождение материала.

Приложение использует существующую авторизацию установленного Codex через App Server.
Просмотр карты, импорт статьи и локальный пилот не вызывают модель. Агентный запуск
отправляет выбранную постановку и подготовленные источники в точную модель
`gpt-6-astra`; автоматическая подмена модели отсутствует.

## Версии и установка

Lean **4.19.0** закреплён в корневом `lean-toolchain`, mathlib — на коммите
**`c44e0c8ee63ca166450922a373c7409c5d26b00b`** в `lakefile.toml`/`lake-manifest.json`.
Python-пакеты закреплены в `requirements-research.lock`, включая LangGraph
**1.2.18** и SQLite checkpoint backend **3.1.2**. JavaScript-зависимости закреплены
в `package-lock.json`: `cytoscape` **3.34.4**, `cytoscape-dagre` **4.0.1**,
`cytoscape-fcose` **2.2.0**.

Проверенная локальная среда: Python **3.12.10**, Node **24.15.0** и Codex CLI
**0.165.0-alpha.1.2**. Эти исполняемые файлы устанавливаются отдельно и не
закреплены репозиторием. Node нужен для тестов и пересборки; готовая графовая
сборка позволяет запустить приложение без установки `node_modules`.

После `lake update` и `lake exe cache get` установите Python-зависимости и
запустите `start.ps1` на Windows либо `start.sh` на Linux/macOS по README.
Внешние кэши mathlib используются повторно. Для примера ассоциатора
`research_project_library.prepare_library` заново компилирует четыре нужных
модуля проекта внутри каталога конкретного запуска:
`MinimalAInfinity → AlbertObstruction → AlbertMatrix → AlbertSpectralGeometry`.
Хеши исходников и результатов фиксируются в `project-library.json`; прежний
корневой `.olean` не заменяет эту проверку.

## Отчёты и команды проверки

Текущий переносимый итог — [checks/release-summary.json](checks/release-summary.json).
Разбор статьи и границы выбранной формализации —
[checks/arxiv-study.json](checks/arxiv-study.json). Числа успешных тестов следует
брать из этих отчётов вместе с датой, областью проверки и результатами Lean.
Само наличие исторического сертификата не подтверждает новый запуск.

Из папки приложения на Windows:

```powershell
$env:PYTHONUTF8 = '1'
$env:ATLAS_LEAN = (& elan which lean).Trim()
.\.venv\Scripts\python.exe -m unittest discover -s tests -v
npm.cmd run test:graph
npm.cmd run test:objects
```

На Linux/macOS:

```sh
export PYTHONUTF8=1
export ATLAS_LEAN="$(elan which lean)"
.venv/bin/python -m unittest discover -s tests -v
npm run test:graph
npm run test:objects
```

Lean-тестам нужны подготовленные реальные зависимости; пропуски сообщаются отдельно.
Модельные ответы в unit/integration-тестах заменены явно обозначенными тестовыми
данными. Для frontend-пересборки выполните `npm ci --ignore-scripts` и
`npm run build:graph-bundle`.

Браузерные сценарии требуют Playwright; использовалась версия **1.62.1**:

```sh
npm install --no-save --package-lock=false playwright@1.62.1
npx playwright install chromium
```

Можно задать `ATLAS_PLAYWRIGHT_MODULE`. Сценарии, которым нужны готовые исследования,
должны получать реальные результаты соответствующего сервера; отсутствие результата
не заменяется вымышленным успехом. `evaluate_research.py` выполняет настоящие
вызовы Astra, поэтому не входит в обычный тестовый запуск.

## Исторические свидетельства

Публикация от 30 октября содержала 105 Python-тестов, 17 тестов графа и 8 HTTP-сценариев;
её три пилота и пример ядра энергии были проверены отдельно. Сохраняются
[publication-lean.json](checks/publication-lean.json),
[publication-python-tests.log](checks/publication-python-tests.log) и
[publication-api.json](checks/publication-api.json). Это результаты прошлого этапа,
а не числа текущего выпуска. Тогда полная компиляция исходного `MathResearch`
заново не выполнялась; проверка лаборатории не подменяет её.

`examples/energy_kernel/Proof.lean` сохраняет исторический исследовательский результат:
при строго положительных весах энергия равна нулю тогда и только тогда, когда
значения совпадают на концах каждого ребра. Он не является третьим основным примером
нынешнего интерфейса. Исторические материалы и контрольные исходники не удалены.

GitHub Pages показывает статические документы. Исследования, Codex App Server,
локальные базы и Lean запускаются Python-сервером на компьютере пользователя.
