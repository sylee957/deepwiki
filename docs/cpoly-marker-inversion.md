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
- **P1 DONE** (commit): concrete `CPoly → CPolyQ`, 495 occ. Gate PASS.
- **P2 DONE** (commit): generic `CPolyG → CPoly`, 5667 occ. Gate PASS. **The type inversion — the stated
  goal — is complete: generic is `CPoly α`, concrete is `CPolyQ`.**
- **P4 DONE** (Step A `git` + Step B `git`): the CPoly engine is fully de-`G`'d. **Generic ops now
  carry clean unmarked names** — `caddG→cadd`, `cmulG→cmul`, `toPolyG→toPoly`, `cSubresultantG→cSubresultant`,
  `cDetG→cDet`, `checkIdentityG→checkIdentity`, `cRatG→cRat`, … (88 ops, 12596 occ). The KEY INSIGHT that
  unblocked it: **de-`G` (`\bcXG\b → cX`) is text-safe** — it matches only the `G`-suffixed generic name,
  never a struct field (`.clead`), class method (`CDiffField.cderiv`), or the concrete `Compute.cX` twin
  (different namespace; Compute/ files reference the generic *qualified* and never `open CPoly`). So the
  concrete ops did NOT need relifting. The only scope work (Step A) was lifting the 3 root-namespace/
  always-in-scope conflicts — algebraic `toPoly→listToPoly`, `commonDenom→commonDenomQ`,
  `cinterpTerm→cinterpTermQ` — and dropping the 2 vestigial `open Compute` (Parametric, LaurentSpecialSoundness).
  One struct-field clash fixed: `IsProperSpecialPart.clead → lc_nz`. `amG`/`QFunNZG`/`fieldFrac` kept
  (separate fraction-field-tower layer, not the CPoly op layer). Residual: `cgcdExtG`/`cdivmodG`/`cresultantG`
  are stale doc-comment mentions of deleted fuel ops (harmless prose).

### (superseded) earlier assessment: P3/P4 seemed blocked by overloads
  - `toPoly` exists THREE ways in overlapping scopes — `Compute.toPoly` (concrete bridge), the top-level
    `DeepWiki.SymbolicIntegration.toPoly` (the algebraic/Zassenhaus `List R → R[X]` helper, used across
    ~10 `Engine/Algebraic/` files), and the would-be generic (from `toPolyG`). ~150 files `open CPoly`, so a
    generic `CPoly.toPoly` would clash pervasively with the always-in-scope top-level algebraic `toPoly`.
    Dropping the bridge-`G` therefore needs BOTH other `toPoly` families disambiguated first — high-risk,
    unrelated churn.
  - `cderiv` (op-`G` phase) = `CDiffField.cderiv`, the abstract derivation used throughout the engine; a
    bare rename corrupts it.
  - **Residual inconsistency (accepted):** generic ops/bridge keep `G` (`CPoly.caddG`, `toPolyG`) while the
    generic *type* is unmarked `CPoly`. The `G` now reads as "generic-engine op." Completing P3/P4 to remove
    it requires the multi-way `toPoly`/`cderiv` disambiguation above — a separate, larger effort, deferred.
