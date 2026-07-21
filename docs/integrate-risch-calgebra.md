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

### P2 — Monomial structures, result record, level packs
`IntegrateRisch/Monomial.lean`, `Results.lean`, `Level.lean`.
- `MonomialPrimitive`/`MonomialHyperexp`/`MonomialHypertangent` with OCR-faithful
  genuineness fields and `.Dt` readings (+ trivial satellites: `Dt_*` coefficient
  lemmas, degree facts).
- `ResultRisch K`: principal part in `K`, RootSum log data with **constant**-
  coefficient `Q` (residue-constancy as invariant field), computable
  `ResultRisch.deriv (D)`.
- `RischLevel K` and `RischOracles K` records as above; `baseLevel`'s `D` and
  `integrate` wired from the rational pipeline (contracts from
  `ratIntegrate_sound`/`_complete`).
**Endpoint**: records compile; `baseLevel : RischLevel (DenseFrac ℚ)` exists
(oracle-free); no `sorry`.

### P3 — Derivation-generic Hermite reduction
`IntegrateRisch/Hermite.lean`.
- Hermite reduction over `(K, D, Dt)` on `DenseFrac (…)`-fractions in `t`:
  rational part + proper log-part remainder with squarefree denominator, exports
  as invariant fields (the `ResultHermite` pattern, derivation-parametric).
- Data-level soundness through the extension derivation.
**Endpoint**: `hermiteReduceD` + sound; exports mirror the rational record's.

### P4 — Log part at a tower level: LRT + residue constancy
`IntegrateRisch/LogPart.lean` (+ `LogPartSpec.lean`).
- Reuse the generic `lrtIntegrate` machinery at coefficient field `K`; add the
  **residue-constancy test** (produced `Qᵢ` coefficients are `D`-constants —
  decidable: `D c = 0` checks) with the dichotomy: constant residues → elementary
  log part with its sound square; a non-constant residue → non-elementarity
  certificate (statement against the abstract Liouville layer may be deferred to
  P11; here the computable test + the sound direction).
**Endpoint**: log-part stage of `stepIntegrate` done generically, sound.

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
