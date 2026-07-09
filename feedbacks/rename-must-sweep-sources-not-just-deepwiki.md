# Codebase-wide decl/type renames must sweep `Sources/`, not just `DeepWiki/`

- **Date:** 2026-07-09
- **Tool/step:** manual find-replace refactor (e.g. inlining a type alias) + scripts/check.sh
- **Expected:** `grep -rl 'CPolyQ' DeepWiki/` gives the files to edit for renaming/inlining a
  declaration.
- **Actual:** it misses the `Sources/` catalogs, which `import` and reference `DeepWiki` declarations
  (worked examples like `Sources/Doi_10_1007_b138171/Exercise22.lean` use `CPolyQ`, and
  `Sources/Hdl_1721_1_15391/IntegrateFull.lean` used `AlgIntegralResultQ`). Editing only `DeepWiki/`
  leaves the `Sources/` references dangling → the gate fails on `Unknown identifier` (plus a cascade of
  `native_decide … uses sorry` from the failed elaboration) only after a full ~5-min build cycle.
- **Why it's a limitation:** the two-layer architecture (book-number-free `DeepWiki/` library +
  DOI-keyed `Sources/` catalogs) means catalog files depend on library names. A rename/inline of any
  `DeepWiki` decl or type that appears in a worked example or `alias`/`abbrev` must touch both trees.
- **Workaround used:** re-ran the replacement over `Sources/` too (`grep -rl … Sources/`), rebuilt.
- **Suggested fix:** when scripting a rename, always target **both** roots:
  `grep -rl '<name>' DeepWiki/ Sources/`. (Optionally a `scripts/` helper that greps both.)
- **Status:** open
