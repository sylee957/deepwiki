# `git mv` reports source missing when target directory is missing

- **Date:** 2026-07-08
- **Tool/step:** migration-loop module move
- **Expected:** moving files into a new subdirectory would either create the target directory or clearly report that the target directory is missing.
- **Actual:** `git mv DeepWiki/SymbolicIntegration/Core/Differential/GcdDeriv.lean DeepWiki/SymbolicIntegration/Core/Differential/Gcd/Derivative.lean` failed with `fatal: renaming ... failed: No such file or directory`.
- **Why it's a limitation:** Git does not create intermediate directories for `git mv`, and the error text can make it look as if the source path is missing.
- **Workaround used:** ran `mkdir -p DeepWiki/SymbolicIntegration/Core/Differential/Gcd` before retrying `git mv`.
- **Suggested fix:** mention the `mkdir -p` pre-step in the migration-loop plan template for moves into new subdirectories.
- **Status:** open
