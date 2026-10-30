# Обновление материалов репозитория

Репозиторий `Medrov/astra-math-research` содержит локальный инструмент с двумя
основными примерами: шаг из статьи Frolov–Dorofeev и связь ассоциатора с энергией
лапласиана из нашего препринта. Читатель начинает с [README](README.md) и
[установки приложения](apps/msc-lean-atlas/README.md). Исходный набор из трёх
математических задач сохранён отдельно; его повторение описано в
[WALKTHROUGH.md](WALKTHROUGH.md).

## Подготовить обновление

1. Зафиксируйте, какая постановка или какой файл изменился. Не ослабляйте утверждение ради успешной компиляции без явного пояснения.
2. После изменения корневых Lean-исходников выполните `python3 scripts/check.py`.
   Изменения приложения проверяйте по [его инструкции](apps/msc-lean-atlas/PUBLICATION.md).
   Проверьте код завершения, новый отчёт, полный список файлов и хеши.
3. Обновите переносимый результат и журналы в `checks/`, чтобы они соответствовали публикуемым исходникам. Машинные пути из локального `verification/verification.json` в публичный экспорт не включаются.
4. Сверьте README, промпты, препринт и визуализацию с текущими утверждениями. После изменений PDF и DOCX просмотрите все страницы.
5. Перед коммитом проверьте состав файлов. `.lake/`, `verification/`, `runs/` и локальные результаты поисков должны оставаться вне Git.

Команды для уже настроенного клона:

```sh
git status --short
git add README.md REPRODUCE.md WALKTHROUGH.md AGENTS.md prompts MathResearch MathResearch.lean scripts experiments docs checks lean-toolchain lakefile.toml
git diff --cached --stat
git commit -m "Update research pipeline and checked examples"
git push
```

Список `git add` корректируйте под фактический состав обновления. Не публикуйте сохранённый успех после изменения доказательств без повторной проверки. Выбор лицензии остаётся за владельцем; сам факт публикации не означает предоставление произвольных прав на повторное использование.

Официальная инструкция: [добавление локального проекта на GitHub](https://docs.github.com/en/migrations/importing-source-code/using-the-command-line-to-import-source-code/adding-locally-hosted-code-to-github).
