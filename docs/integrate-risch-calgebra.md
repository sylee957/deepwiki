# IntegrateRisch: transcendental integration in the CAlgebra rewrite

**GOAL**: a verified Risch integrator for transcendental towers `ℚ(x)(t₁)…(tₙ)`
(`tᵢ` primitive / hyperexponential / hypertangent monomials) in the hex-style
CAlgebra engine — canonical carriers, computable `.deriv`, data-level
`*_sound`/`*_complete` primary specs with `toRatFunc`-style squares, invariants
carried as record fields.

**Home**: everything new lives in `DeepWiki/CAlgebra/IntegrateRisch/` (aggregator
`DeepWiki/CAlgebra/IntegrateRisch.lean`, wired into `DeepWiki/CAlgebra.lean`).
The rational pipeline `DeepWiki/CAlgebra/Integrate/` is **complete and frozen** —
IntegrateRisch imports it but does not modify it. If the rational stages turn out
to be instances of the derivation-generic ones, subsumption is reconsidered *after*
the tower works (a dedicated cleanup phase, not now).

## Settled design decisions

- **Carrier**: one generic level. Level 0 is `DenseFrac ℚ` (= `ℚ(x)`, `D = d/dx`);
  a level over `K` is `DenseFrac K`. No `n`-indexed tower family: towers are chains
  of `extend*` applications. Per-level instances are threaded explicitly (resolution
  cannot recurse on depth — old-engine lesson).
- **Monomials**: three separate structures, no kind enum, no indexed `GenuineCond`
  family — `MonomialPrimitive` (`Dt = η`), `MonomialHyperexp` (`Dt = η·t`),
  `MonomialHypertangent` (`Dt = η·(1+t²)`), each with its own named Bronstein
  genuineness `Prop` fields (transcribed by OCR from `references/10.1007_b138171.pdf`,
  PDF page ≈ book + 11 → + 9 by Ch. 6) and a computed `Dt : DensePoly K` reading.
  A wrapping `inductive Monomial` sum is added only if a tower-as-data type is ever
  needed (frontend), not before.
- **Differential-structure tier (`DenseDiffRing`)**: the derivation core
  `(d, IsDerivation d)` bundled as `DenseDiffRing K` (`IntegrateRisch/DiffRing.lean`),
  with `.base` (zero derivation) and `.extend F Dt : DenseDiffRing (DenseFrac K)` —
  the derivation-level tower step (= `isDerivation_extendDeriv` named). Stages that need
  only the derivation (Hermite P3, log part P4) take `DenseDiffRing K` (+ `Dt`); it is
  the weakest sufficient input, sits strictly below `RischLevel` (which is *built from*
  those stages — feeding a `RischLevel` into Hermite would be a dependency cycle), and
  **`RischLevel extends DenseDiffRing`** (done). **Discipline: parameterize by the
  minimal thing the type actually uses.** `ResultRisch`/`ResultHermiteD`/`IsNormal`/
  `RischOracles` use only `d` (in `mapCoeffs d`/`extendDeriv d Dt`), never the
  `isDerivation` proof — so they stay on the bare `d`; bundling `DenseDiffRing` there
  would carry a dead proof field (NOT a defeq issue — proof irrelevance + structure-eta
  make `DenseDiffRing`-indexing defeq to `d`-indexing; it's minimal-dependency +
  goal-readability). `RischLevel` genuinely bundles `(d, isDerivation)` — `isDerivation`
  is carried for the downstream `extend` step, so it extends `DenseDiffRing`; pass
  `L.toDenseDiffRing` to the derivation-only stages.
- **Level packs, laws bundled**: single records in the `DensePolyGcd`/
  `DensePolyResultant` house pattern (ops + contracts in one structure; no
  `Lawful` companion — concrete carriers need no Prop-erasure). Two records so
  depth-1 doesn't owe depth-2's obligations:
  - `RischLevel K`: the derivation `D`, `integrate`, derivation laws, and the
    data-level contracts (`integrate_sound` on the produced record's computable
    `.deriv`; `integrate_complete` = `none → ¬ elementary`).
  - `RischOracles K`: `limitedIntegrate`, `rdeSolve` (+ their contracts) — the
    sub-level services the *next* extension consumes. `extend*` has signature
    `RischLevel K → RischOracles K → Monomial* → RischLevel (DenseFrac K)`;
    producing `RischOracles (DenseFrac K)` is its own later phase (needed only
    for depth ≥ 2).
- **Sharing**: case-independent machinery (extension derivation, Hermite, log
  part, residue constancy) is parametrized by `Dt : DensePoly K` alone — it never
  imports the monomial structures.
- **Specs**: primary statements are data-level equations between canonical
  carriers (the `ratIntegrate_sound` pattern); `RatFunc`-side meaning enters
  through per-level squares. Genuineness/properness/constancy conditions ride as
  record invariant fields, never as re-proved hypotheses.
- **Old engine** (`DeepWiki/SymbolicIntegration/`): reference implementation and
  spec oracle only — no file ports. Its Layer-0 abstract theorems (Liouville
  keystones, `IsElementary`, monomial case analyses) are shared where
  carrier-independent.

## Phases (each `/goal`-able, gate-green, review-before-commit)

### P1 — Extension derivations — DONE (2026-07-22, 48581d10)
`IntegrateRisch/DerivationExtend.lean`.
- `IsDerivation (d : K → K)` Prop record (add + Leibniz) with satellites
  (`map_zero/one/neg/sub/sum`) and the Mathlib bundling `IsDerivation.toDifferential`
  (applies as `d` by `rfl`).
- Computable extensions: `DensePoly.mapCoeffs`/`DensePoly.extendDeriv d Dt`
  (coefficient-wise `d` + `Dt ·` formal derivative; laws proven coefficientwise,
  `extendDeriv_C`/`extendDeriv_X` defining properties,
  `isDerivation_extendDeriv` packaging) and `DenseFrac.extendDeriv` by the quotient
  rule (laws by `toRatFunc_injective` transport; `isDerivation_extendDeriv` is the
  tower-composability keystone; `extendDeriv_ofPoly` compatibility).
- Squares: `toPolynomial_extendDeriv` lands on Mathlib's
  `Differential.implicitDeriv`; `toRatFunc_extendDeriv` lands on its fraction-field
  extension (`SymbolicIntegration.PolynomialFractionDeriv.fracDeriv`, reused as-is) —
  stated parametrically over any `[Differential K]` agreeing with `d`.
- Homing en route: `coeff_ofList_map` hoisted to `Poly/Dense.lean` (public);
  `deriv_C`/`deriv_X` added to `Diff/Derivative.lean` (PolyPart's local `deriv_C`
  duplicate removed).
- Lessons: on `RatFunc`, avoid `Derivation.leibniz`-style fresh-synthesis lemmas
  (ℤ-algebra diamond `RatFunc.instAlgebraOfPolynomial` vs `Ring.toIntAlgebra`) — use
  the plain-function `fracDerivFun_add/mul` lemmas; inside `namespace DenseFrac`,
  `fracDeriv` must stay fully qualified (shadowed by the formal-derivative one).
- Deferred to P2+: per-tower `′`-notation (`Differential` instances are per concrete
  level, constructed with `RischLevel`, not scoped globally).

### P2 — Monomial structures, result record, level packs — DONE (2026-07-22, 9c6ef752)
`IntegrateRisch/Monomial.lean`, `Results.lean`, `Level.lean`.
- `MonomialPrimitive` (`η ∉ d(K)`), `MonomialHyperexp` (no `n ≠ 0`, `u ≠ 0` with
  `n·η·u = d u`), `MonomialHypertangent` (`√−1·η` not a log-derivative of a
  `K(√−1)`-radical, encoded componentwise: no `n ≠ 0`, `(a,b) ≠ 0` with
  `d a = −n·η·b ∧ d b = n·η·a`) — genuineness OCR'd from the book (§5.1 monomial
  criteria, §5.10 hypertangent); `.Dt` readings (`C η` / `[0,η]` / `[η,0,η]`) and
  `η_ne_zero` satellites (genuineness forces `η ≠ 0` in all three cases).
- `ResultRisch K d`: `principal : DenseFrac K` + RootSum `terms` with invariants
  `fst_squarefree` and `fst_constant` (residue constancy as `mapCoeffs d Q = 0`);
  computable `ResultRisch.deriv Dt` via `bivDeriv` (P1's extension at the bivariate
  carrier: `z` constant, coefficients by `d`, `Dt·∂t`) and the derivation-parametric
  deformation `rootSumDerivD`; base bridges `bivDeriv_zero_one`,
  `rootSumDerivD_zero_one`, `ResultRisch.ofRatIntegral(_deriv)`.
- `RischLevel K` (d, Dt, `IsDerivation`, integrate + data-level sound and
  record-shape complete) and `RischOracles d Dt` (limitedIntegrate, rdeSolve +
  contracts over `DenseFrac.extendDeriv d Dt`).
- `baseLevel : RischLevel R` — `R(x)` presented as the level `(d = 0, Dt = 1)` over
  the coefficient field, integrate = `ratIntegrate`, soundness from
  `ratIntegrate_sound`, completeness vacuous. **Deviation from the original endpoint**:
  stated over a generic `[CharZero R] [IsAlgClosed R]` coefficient field, not `ℚ` —
  the rational pipeline's theorems live over closed fields; the ℚ-instance descent
  (engine ops commute with coefficient embedding) is a known separate frontier, as in
  the old engine.
- Homing en route: `C_zero` hoisted to `Poly/Dense.lean` (DerivDataSpec's private
  copy removed); `fracDeriv_ofPoly` added to `Diff/Frac.lean`; `isDerivation_zero`,
  `mapCoeffs_eq_zero`, `extendDeriv_zero_one` (poly + frac) added to
  `DerivationExtend.lean`.

### P3 — Derivation-generic Hermite reduction — DONE (2026-07-22)
`IntegrateRisch/Special.lean`, `IntegrateRisch/Hermite.lean`.
- **Special.lean**: `IsNormal`/`IsSpecial` predicates over an arbitrary polynomial
  derivation `D`; the squarefree-factor split `normalPart`/`specialPart` via
  `gcd(p, Dp)` with its correctness quartet (product, coprimality, normality,
  speciality — all pure divisibility algebra, no UFD transport); closure lemmas
  `IsNormal.of_dvd`/`IsNormal.mul` (coprime products), `IsSpecial.mul`/`.pow`,
  `isCoprime_of_squarefree_mul`.
- **Hermite.lean**: power-sum vocabulary (`powSumDesc`/`powSumAsc`/`powSumFrom` with
  reverse/shift bridges and the `invPowSum` denotation); the data-level Hermite step
  (`c/facⁿ⁺² = D(−t/((n+1)facⁿ⁺¹)) + …` proven entirely in the field `DenseFrac K`
  via the new `IsDerivation` calculus — `map_div`, `map_pow_succ`, `map_natCast`,
  `map_inv_of_map_zero`, `map_list_sum` in DerivationExtend); the sweep
  `hermiteFactorAuxD` + spec (functional induction); the per-factor normal/special
  numerator split `splitNumers` + spec; `hermiteFactorD` (sweep the normal side,
  division-reduce the residual, pass specials through) + spec; the record
  `ResultHermiteD` (invariants: `simple_den_squarefree`, `simple_den_normal`,
  `reduced_den_special` as an ∃-witness) and **`hermiteReduceD` +
  `hermiteReduceD_sound`** — the data-level identity
  `f = D(rational) + simple + reduced`, hypothesis-free given `IsDerivation d`.
- Homing en route: `ofPoly` hom satellites (`add/mul/neg/zero/one/ne_zero`) in
  `Frac/Basic.lean`; `ofPoly_pow`, `den_ofPoly_div_dvd` in `Frac/Field.lean`
  (division lives there); `isCoprime_of_squarefree_mul` in Special.
- Lessons: WF-recursive defs (`termination_by`) are not `rfl`-reducible — never
  `show`-unfold them (whnf spin); unfold with `rw [defName]` (once) + `simp only []`
  for zeta, and mind that `.induct` exposes `let`-bound values as extra case binders.
  `rw [h] at`-style with `h : f = …` wrecks goals containing `f.num`-projections —
  use `conv_lhs`.
- **Deferred (P4-prep)**: the `simple_isProper` properness export (the sweep residues
  are `%`-reduced already, so the size chain is set up; the `RatFunc.IsProper`
  sum-closure argument mirrors the rational `logsum_isProper`). P4's LRT feed needs
  it and should start there.

### P4 — Log part at a tower level: LRT + residue constancy — DONE to the honest frontier (2026-07-22)
`IntegrateRisch/LogPart.lean` (tower discharge of the frontier = P4b).
- **Key math finding**: the Rothstein–Trager resultant uses the **field** derivation
  `D q` (= `extendDeriv d Dt q`), not the formal `dq/dt` — confirmed by the old engine's
  `rtResultantGen … B` with `B` built from `implicitDeriv` (`LrtSoundness.lean`). At the
  base `D = d/dx` coincides with the formal derivative of a polynomial in `x`, which is
  why the rational `rtResultant` uses `d′`; the tower replaces it with `extendDeriv d Dt`.
- **P4a landed (this session, gate-green, sound at its level)**: `rtResultantD` /
  `lrtLogTermsD` (the LRT construction with the field derivation) + the base-compat
  `rtResultantD_zero_one` (= rational `rtResultant` at `(d=0,Dt=1)`, so the base inherits
  the rational LRT soundness); structural soundness `lrtLogTermsD_fst_squarefree`; the
  **residue-constancy test** `IsResidueConstant d Q := mapCoeffs d Q = 0` (+ `Decidable`
  instances, `AllResiduesConstant`, `allResiduesConstant_iff` = the `ResultRisch.fst_constant`
  invariant). Also the deferred-from-P3 `ResultHermiteD.simple_isProper` (via
  `isProper_ofPoly_mod_div` — the sweep residues are `%`-reduced) is now a record field.
- **The sound direction, generic + frontier-isolated (this session)**: `ResidueCriterion
  d Dt` — the named Bronstein condition (§5.6): for every valid simple part `g`, the field
  derivative `∑ᵢ ∑_{Qᵢ(α)=0} α·D(log Sᵢ)` (= `(lrtLogTermsD …).map (rootSumDerivD …)`)
  recovers `g`. This IS the log-part stage's soundness. **Discharged UNCONDITIONALLY at the
  base** (`residueCriterion_zero_one`, via `lrtLogTermsD_baseSound` → `rtResultantD_zero_one`
  + `rootSumDerivD_zero_one` → the rational `lrtIntegrate_sound`; axiom-clean). This is the
  project's frontier-as-hypothesis pattern (the criterion is real content, base case proven,
  deep case isolated) — exactly as the old engine's `LawfulRischLevelLrt`/`PrimitiveFrontier`.
- **P4b remaining (its own arc)**: discharge `ResidueCriterion d Dt` for **tower** levels
  (`d ≠ 0`) — the general-monomial residue criterion the old engine spends ~1600 lines on
  (`LrtGeneralDerivation.lean` + `LrtSoundness.lean`); the CAlgebra path is to bridge to
  those verified `_gen` theorems through the `toRatFunc` denotation + `F.toDifferential`,
  or re-prove derivation-generically. The non-constant-residue non-elementarity certificate
  is P11.
**Endpoint**: LRT construction + residue-constancy test done generically; the sound
direction is the named `ResidueCriterion` frontier, proven unconditionally at the base and
isolated for tower levels (P4b).

### P5 — Base limited integration
`IntegrateRisch/BaseLimited.lean`.
- Limited integration over `ℚ(x)`, `D = d/dx` (Bronstein's parametric problem —
  the service the primitive case's coefficient recursion consumes): algorithm +
  data-level sound + complete.
- Fill `baseOracles.limitedIntegrate`.
**Endpoint**: `baseOracles : RischOracles (DenseFrac ℚ)` with `rdeSolve` still
stubbed as a separate record or deferred field — if the record split makes this
awkward, split `RischOracles` into `LimitedOracle`/`RdeOracle` here.

### P6 — Primitive case, depth 1 end-to-end
`IntegrateRisch/PolyPrimitive.lean`, `ExtendPrimitive.lean`.
- Primitive polynomial-part integration with **full coefficient recursion**
  (top-down `D(bᵢ) = aᵢ − (i+1)·η·bᵢ₊₁`, via the sub-level oracle — closing the
  old engine's constant-coefficient-only gap).
- `RischLevel.extendPrimitive` assembling Hermite (P3) + log part (P4) + poly
  part; contracts discharged from the pieces.
- Validation: `∫` over `ℚ(x)(log x)` — e.g. `∫ log x`, `∫ 1/(x·log x)`,
  `∫ log²x/x` as concrete examples.
**Endpoint**: `(baseLevel.extendPrimitive baseOracles M).integrate` sound +
complete at depth 1; examples restated against book expectations.

### P7 — Base Risch differential equation
`IntegrateRisch/BaseRde.lean` (split into a subdirectory only if it outgrows one
file; flat first).
- `D y + f·y = g` over `ℚ(x)`: weak normalization, denominator bound, degree
  bound, SPDE / polynomial RDE — sound + complete (none ⇒ no solution).
- Fill `baseOracles.rdeSolve`.
**Endpoint**: rational RDE decision procedure, both directions.

### P8 — Hyperexponential case, depth 1
`IntegrateRisch/PolyHyperexp.lean`, `ExtendHyperexp.lean`.
- Hyperexp polynomial(-Laurent) part via the RDE oracle; `extendHyperexp`.
- Validation over `ℚ(x)(eˣ)`: `∫ eˣ`, `∫ x·eˣ`, and a non-elementary witness
  (`∫ e^{x²}` refused — completeness direction exercised).
**Endpoint**: depth-1 hyperexp sound + complete.

### P9 — Hypertangent case, depth 1
`IntegrateRisch/PolyHypertangent.lean`, `ExtendHypertangent.lean`.
- The coupled 2×2 system for the tangent case; `extendHypertangent`.
- Validation over `ℚ(x)(tan x)`.
**Endpoint**: depth-1 tangent sound + complete.

### P10 — Oracles at extended levels; depth ≥ 2
`IntegrateRisch/ExtendOracles.lean`.
- `extendOracles* : … → RischOracles (DenseFrac K)` — limited integration and
  RDE *at* a monomial extension (the recursive versions), so packs compose.
- Depth-2 validation: `ℚ(x)(log x)(log (log x))`, `ℚ(x)(eˣ)(e^{eˣ})`-style
  examples; confirm instance threading stays explicit and builds stay tame.
**Endpoint**: `extend*` chains compose to arbitrary depth; depth-2 examples green.

### P11 — Completeness capstone: the decision procedure
`IntegrateRisch/Complete.lean` (+ Liouville bridging).
- The `none ⇒ ¬ IsElementary` direction assembled from the per-stage certificates
  (residue non-constancy, RDE unsolvability, coefficient-recursion failure),
  stated against the CAlgebra Elementary/Liouville layer; share the old engine's
  Layer-0 keystones where they apply.
- Capstone statement: for genuine towers, `integrate` is a **decision procedure**
  for elementary integrability, sound and complete, axiom-clean.
**Endpoint**: capstone proven; document the (provably necessary) genuineness
frontier exactly as the old arc did.

### P12 — Frontend and polish
- `Expr` atoms `log`/`exp`/`tan`(as needed), elaboration of an expression into a
  tower + monomial structures (genuineness obligations surfaced explicitly),
  `IntegralExpr` extension, CLI command.
- Sweep: satellite homing, naming audit, docstring audit; decide whether any
  rational-pipeline stage should now be subsumed by the derivation-generic one
  (separate decision, separate commit).

## Standing rules for every phase

Gate `scripts/check.sh` green, no `sorry`, warnings are errors; restate new
theorems as `example`s against the book's wording; OCR statements — never text
extraction; commit only after user review; durable adjudications to memory,
mechanical status to this file (mark phases DONE with date + commit).
