# CPoly marker inversion — generic becomes the unmarked default

**Goal.** Invert the generic-vs-concrete naming: the *generic* engine (the primary implementation, ~5.6k
refs) takes the clean unmarked names; the *concrete ℚ reference layer* `Compute` (the minority, book
native_decide examples) carries an explicit `Q` marker. Replaces the earlier "keep G" verdict — the user's
call: the primary deserves the clean name.

Today: generic `CPolyG α`/`CPolyG.caddG`/`CPolyG.toPolyG`; concrete `Compute.CPoly = CPolyG ℚ`/
`Compute.cadd`/`Compute.toPoly`. Target: generic `CPoly α`/`CPoly.cadd`/`CPoly.toPoly`; concrete
`Compute.CPolyQ`/`Compute.caddQ`/`Compute.toPolyQ`.

**Ordering is mandatory** (relift concrete to free a name *before* the generic takes it) and renames are
**word-boundary** (`\bCPoly\b` excludes `CPolyG`; `\bcadd\b` excludes `caddG`). Each phase is one atomic
gate-green commit (a rename must be atomic — the intermediate state doesn't compile).

## Hazards
- **Overloaded op names.** `cderiv` also = `CDiffField.cderiv` (the abstract derivation, used everywhere in
  the generic engine); `toPoly` also = an unrelated `PolynomialIrreducibility.toPoly`. A blind `\bcderiv\b`
  / `\btoPoly\b` rename would corrupt these. The concrete versions must be renamed **namespace-aware**
  (only `Compute.`-scoped / Compute-file-local occurrences), never globally.
- `CPoly` is a substring of `CPolyG`; `cadd` of `caddG`; `toPoly` of `toPolyG` — always use `\b…\b` with the
  trailing boundary so the `G`-suffixed generic name is *not* matched.
- `BPoly := List CPoly` (bivariate concrete) rides along — its def body updates to `List CPolyQ`.

## Phases
- **P1 — relift concrete TYPE `CPoly → CPolyQ`** (~495 refs, word-boundary; `BPoly` def follows). Free of
  overloads. Concrete type is now `CPolyQ`, generic still `CPolyG`.
- **P2 — move generic TYPE/namespace `CPolyG → CPoly`** (~5.6k refs). Now `CPoly` = generic, `CPolyQ` =
  concrete; generic ops still `CPoly.caddG`, bridge still `CPoly.toPolyG` (op-`G` dropped later).
- **P3 — bridge `toPolyG → toPoly`** (~5.2k): first relift concrete `Compute.toPoly → toPolyQ`
  (namespace-aware; leave the unrelated `PolynomialIrreducibility.toPoly`), then `\btoPolyG\b → toPoly`.
- **P4 — drop op-`G`** (~155 ops, ~thousands of refs): relift concrete `Compute.cX → cXQ` (namespace-aware,
  handle `cderiv`), then `\bcXG\b → cX` per op. Do in op-family batches; `amG`/`QFunNZG` are a *separate*
  decision (different concept — the fraction-field tower — not the `CPoly` op layer).

## Status
- P1: in progress.
