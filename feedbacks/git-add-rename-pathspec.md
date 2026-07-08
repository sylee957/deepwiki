# Git add pathspec failure can leave a partial commit

- **Date:** 2026-07-08
- **Tool/step:** migration-loop commit step
- **Expected:** staging a moved file by listing the old and new paths would either stage the whole intended change or stop before committing.
- **Actual:** `git add ... DeepWiki/SymbolicIntegration/SpecialNormalCoprime.lean ...` reported `fatal: pathspec ... did not match any files`, but the following `git commit` still ran and committed only the already-staged rename.
- **Why it's a limitation:** a multi-command commit step can proceed after a failed staging command if the index already contains part of the change.
- **Workaround used:** inspected `git status` and amended the remaining import rewires, plan doc, and feedback note into the same commit.
- **Suggested fix:** use `git add -A -- <moved-tree-or-topic-root> <docs-plan>` or check status after staging before running commit.
- **Status:** open
