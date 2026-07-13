# Refactor: integrand fractions as `DenseFrac`, not `(num, den)` + `den ≠ 0`

**Goal.** Across the Risch integrator, where a *fraction being integrated* is passed as two polynomials
`(a d : DensePoly α)` with a separately-threaded `toPoly d ≠ 0` hypothesis (duplicated ~130× across 62
files), carry it as a single **`DenseFrac α`** — the proof-carrying `CFrac` structure that *bundles the
nonzero-denominator invariant* (`FracReprDense.lean`: `structure DenseFrac` with a `den_nonzero` field).
The `den ≠ 0` obligation then lives once, in the fraction, instead of at every call site and in every
soundness/completeness lemma's hypotheses.

## Why it's feasible (verified 2026-07-13)

- `DenseFrac α` already exists and bundles `num`/`den`/`den_nonzero` (`CFrac`/`LawfulCFrac` interface,
  `ComputableAlgebra/FracRepr.lean` + `FracReprDense.lean`). `CFrac.num`/`.den`/`.ofFraction` are the API.
- **The RDE layer already uses `DenseFrac`** (`crischDESolveSoundWf (f g : DenseFrac β)`, the
  `*ResidualWf (f g : DenseFrac β)` structs) and it is **`native_decide`-safe** — catalog examples
  construct `DenseFrac` via `CFrac.ofFraction [..] [..] (by cfrac_nonzero)` and `native_decide` through
  them (`Sources/…/Chapter6.lean:69`, `RischDE/SolveSoundWf.lean:204`). So the pattern is proven, not
  speculative.
- The duplication is concentrated in the integrator **core interface** (`Engine/RischLevel.lean`:
  `CRischLevel.integrate : ℕ → P α → P α → P α → Option …`, the `LawfulCRischLevel`/`CompleteCRischLevel`
  methods all re-thread `CPoly.toPoly d ≠ 0`) and the LRT/Hermite reduction chain
  (`RischTowerLrt`, `RischTowerPrimitiveLrt`, `Hermite/ValuationTower`, `NormalReduction`, …).

## Risk / caution

- **`native_decide` reduction.** `DenseFrac` is a `structure` (not a `List` synonym); the RDE precedent
  shows it reduces, but each converted computational def must keep its native_decide examples green.
- **Catalog examples** (`Sources/…`) construct integrands; converting a cataloged entry's input type
  changes those examples. Handle per-chapter, keep them green.
- **Two-poly is sometimes genuine.** Not every `(a, d)` pair is one fraction (e.g. a numerator paired
  with an independently-computed denominator, or `Dt` the monomial derivative which is a *polynomial*,
  not a fraction). Convert ONLY the true fraction-integrand `(a, d)` pairs; leave genuine
  separate-polynomial arguments alone. `Dt` stays a `DensePoly` (it is a derivative, not a fraction).

## Approach — spike first, then fan out

**Spike (P0).** Pick ONE self-contained theorem cluster whose `(a, d)` is unambiguously one integrand
fraction, convert it to take a `DenseFrac`, measure: does it type-check, does native_decide survive, how
many call sites break, does the `den ≠ 0` hypothesis actually disappear? Decide go/no-go and the true
per-cluster cost from the spike. Do NOT fan out before the spike is gate-green.

**Fan-out phases (P1…), leaf-first**, each its own gate-green commit:
1. The generic interface `Engine/RischLevel.lean` (`CRischLevel.integrate` + the Lawful/Complete
   contracts) — the highest-leverage change; everything downstream inherits the frac-typed integrand.
2. The LRT track (`RischTowerLrt`, `RischTowerPrimitiveLrt`, `LrtAssembly`, `LrtIntegrate`,
   `LrtSoundness`).
3. The Hermite/canonical reduction chain (`Hermite/ValuationTower`, `NormalReduction`,
   `CanonicalReconstructionCharZero`, `Yun*`).
4. The hyperexp/tangent levels + their tower-depth capstones.
5. The `Sources/` catalog examples, per chapter.

## Status (2026-07-13)

**Done — the API-surface frac conversion** (the safe, high-value tier): frac-integrand forms added for
the whole transcendental sound-and-complete decision-procedure family, each `den ≠ 0`-free (the
fraction carries it via `CFrac.toPoly_den_ne_zero_generic`), all axiom-clean, gate PASS:
- `rischLevel_succeeds_iff_integrable_frac` (generic), `hyperexpRischLevel_succeeds_iff_integrable_frac`
  (§5.9), `tangentRischLevel_succeeds_iff_integrable_frac` (§5.10),
  `hyperexpRischLevel_succeeds_iff_integrable_tower_frac` + `denseTangentTower_soundAndComplete_frac`
  (whole-tower), `lrtSolver_soundAndComplete_on_tower_frac` (primitive capstone).

So downstream / user-facing code has den≠0-free entry points across the decision-procedure API.

**Deliberately NOT converted (the honest scope boundary):**
- **The computational core** (`cHermiteReduceTower`, `cIntegrateReducedLrt`, `integrate`, the canonical
  representation) takes `(a, d)` as two polynomials — this is native_decide-validated at concrete `ℚ`,
  and the reduction defs are `noncomputable` (abstract `toPoly` bridge), so they are not native_decide
  targets to reshape and their two-poly form is structural.
- **The reduction-chain / LRT-contract soundness theorems** (`Hermite/ValuationTower`, `NormalReduction`,
  `RischTowerLrt`/`RischTowerPrimitiveLrt` class fields `specialSound`/`reducedSoundLrt`, `Yun*`) thread
  `toPoly d ≠ 0` as a **load-bearing hypothesis in the abstract correctness proofs**, not mere
  bookkeeping. Converting the `LawfulCRischLevelLrt`/`CRischLevel` contract fields to a frac integrand
  would cascade to every instance and every soundness proof — a large invasive rewrite of the *verified*
  sound-and-complete arc for marginal duplication reduction. Left intact; the API-tier frac forms give
  the ergonomic win without that risk.

**Verdict.** The `den ≠ 0` duplication the user saw is genuinely reduced at the API surface (the places
callers touch); the remaining sites are load-bearing soundness hypotheses / native_decide-constrained
core, where the two-poly form is structural and converting it would endanger the verified engine.

## Invariants

- Gate with `scripts/check.sh` (GATE: PASS, warning-/sorry-free) per phase; keep `native_decide`
  examples green.
- `Dt` (monomial derivative) stays `DensePoly` — it is not a fraction.
- Convert only genuine integrand fractions; leave real separate-polynomial args.
- Rebuild the wiki graph and re-audit call sites before each conversion; the sound-and-complete
  theorems' *statements* may change shape (frac arg instead of `a d + den≠0`) but their content must be
  preserved — restate as `example`s if a book-facing statement changes.
