import DeepWiki.SymbolicIntegration.Engine.RischTowerLrt
import DeepWiki.SymbolicIntegration.Engine.RischSolverTowerLrt
import DeepWiki.SymbolicIntegration.Engine.RischTowerLrtGrounding
import DeepWiki.SymbolicIntegration.Engine.PrimitiveLrtDecision

/-! # The primitive-case Risch algorithm — a reading guide over the computable definitions

This module is the **narrative entry point** for the primitive case of the transcendental Risch
integration algorithm as implemented here. It defines nothing new; it names, in algorithm order, the
*computable* definitions that make up the integrator and points at where each step's correctness proof
lives. Read the definitions here for the algorithm; the sub-theorems (soundness, frontier discharge) are
proved in the cited files and rendered in the API docs.

## What "primitive case" means

A tower `K(x)(t₁)…(tₙ)` is built by adjoining monomials. `t` is a **primitive** monomial when its
derivative lands in the field below — `Dt = θ ∈ K(x)(…)` — equivalently `D(t)` is a *constant* with
respect to `t`. (The canonical primitive is `t` with `Dt = 1`, e.g. `t = log u`.) The primitive case
integrates `f = a/d ∈ K(x)(…)(t)` when `t` is primitive.

## The carrier and the recursion

* **Carrier.** The tower is the iterated computable fraction field `CFrac` over the computable field
  `CField` / polynomial `DensePoly` (see `ComputableAlgebra.PolyReprDense`). Level `n` is
  `DensePoly (CFracGⁿ K)`. Everything is `native_decide`-executable.
* **The solver interface** is the class `LawfulRischLevelLrt` (`RischTowerLrt`). It bundles the
  per-level computable case hook (`case : CMonomialCase DensePoly`) with its soundness fields. `LawfulX`/`X` idiom:
  the computable half reduces; the abstract soundness lives in the lawful half.
* **The recursion** is two instances: `instLawfulRischLevelLrtPrimitive` (the base — constant-coefficient
  polynomials over `ℚ(x)`) and `instLawfulRischLevelLrtTower` (the step — given a solver for the
  coefficient field `β`, build one for `(DenseFrac β)(t)`). Together they resolve the solver at every tower
  depth by instance search.

## The algorithm, one level (`cIntegrateCaseLrt`, `LrtAssembly`)

Given `a/d`:

1. **Canonical split** — `canonicalRepresentationFast` (`OneShotAssembly`) writes `a/d` as
   `polynomial part fₚ  +  special part b/ds  +  normal part cₙ/dₙ`.
2. **Special / polynomial part** — the case hook `towerPrimitiveCaseLrt.integrateSpecial`
   (`RischSolverTowerLrt`). Under the computable guard `b = 0 ∧ Dt = 1`, it integrates the polynomial
   `fₚ` coefficient-by-coefficient:
   * `towerPolyIntegrateLrt` runs the degree-raising primitive-polynomial recursion
     `cIntegratePrimPolyDegRaise` (`LimitedIntegrateSingle`);
   * each coefficient is integrated by recursing into the level-below solver's **log-free** integrator
     `LawfulRischLevelLrt.integrateRationalLrt` — this is where the tower recursion happens.
3. **Reduced / normal part** — `cIntegrateReducedLrt` (`LrtIntegrate`): the **root-free**
   Lazard–Rioboo–Trager reduced integrator. Hermite reduction gives the rational part; the LRT step
   emits **symbolic algebraic-residue logs** `Σ_{Rᵢ(c)=0} c · log Sᵢ(c,t)` — no root-finding, so residues
   that are algebraic over the constants are kept symbolic.
4. **Assemble** — `combineSNLrt` (`Assemble`) combines the two into an `LrtResult`: a rational part plus
   the symbolic log terms. The top entry is `LawfulRischLevelLrt.integrate`.

## Soundness (proofs — behind the API docs)

`LawfulRischLevelLrt.soundFormalLrt`: any successful run satisfies `IsIntegralResultLrt` — over **every**
algebraically-closed differential extension `E`, `D_E(rational) + Σ residue-logs = a/d`. It is assembled
from the two `LawfulRischLevelLrt` soundness fields:

* `specialSound` — the polynomial-part identity, proved once for base and tower by the shared
  `primitiveSpecialSoundCore` (`RischTowerPrimitive`), via `canonicalReconstruction_of_charZero`.
* `reducedSoundLrt` — the reduced-part identity, the field `PrimitiveFrontierLrt.hreducedLrt`
  (`RischTowerPrimitiveLrt`).

## The three genuine frontiers (real mathematics, not bookkeeping)

The a-priori soundness rests on exactly three honest obligations — necessary Bronstein conditions a
properly-built tower satisfies, not provable from the computable data alone:

* `PrimitiveFrontierLrt` — reduced-part soundness, closed down to the bundled `LrtReducedGenuineData`
  (Rothstein–Trager residue data + tower nondegeneracy) by `hreducedLrt_of_genuineAll`.
* `CgcdBCorrect cgcdFFCoreWf` — correctness of the fraction-free gcd at each tower level.
* `LrtLiouvilleFrontier` — the Liouville/completeness obligation.

## Decision procedure (`PrimitiveLrtDecision`)

With the Liouville frontier, `primitiveLrtDecides` turns the integrator into a **decision procedure**:
`IsElementaryIntegrableGenuineLrt Dt a d ↔ cResidueConstantGuard Dt a d = true` — a computable guard that
certifies genuine algebraic-residue elementary integrability (and its negation is a non-integrability
certificate, `not_isElementaryIntegrable_reduced`).

## Status

Complete as a **recursive, tower-general, `native_decide`-validated computable integrator** with a-priori
soundness modulo the three genuine frontiers above; the recursion is validated at depth 2 by instance
resolution (`RischTowerLrtGrounding`). The base LRT track replaced the earlier rational
`LawfulRischLevel`/`PrimitiveFrontier`, whose rational reduced soundness (`IsIntegralResult`) is *not*
universally dischargeable — it forces the reduced denominator to split over `K`, false for algebraic
residues; the root-free LRT reduced frontier is the dischargeable analogue. -/
