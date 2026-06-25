import DeepWiki.SymbolicIntegration.ComputableIntegrate
import DeepWiki.SymbolicIntegration.ComputableCanonicalRepCorrect
import DeepWiki.SymbolicIntegration.ComputableHermiteTowerCorrect
import DeepWiki.SymbolicIntegration.ComputablePolyPartTowerCorrect
import DeepWiki.SymbolicIntegration.ComputableLogPartTowerCorrect

/-! # Abstract correctness of the end-to-end transcendental integrator `cIntegrate` (Bronstein Ch. 5)
The capstone `cIntegrate` (`ComputableIntegrate`) assembles the whole transcendental Risch integration
loop — canonical split `f = fₚ + fₛ + fₙ` (§3.5), Hermite rational part of `fₙ` (§5.3), the
Rothstein–Trager rational-residue logarithmic part (§5.6), and the primitive polynomial integration of
`fₚ` (§5.8) — into the elementary antiderivative `∫ f = g + ∑ᵢ cᵢ·log(vᵢ)`. It is validated *pointwise*
by `native_decide` (`integrate_example`, the exact `IntegralResult.checkIdentity` cleared identity
`D(∫f) = f` on Bronstein's Example 5.6.2).

This file proves the **abstract** correctness — for ALL inputs, axiom-clean (no `native_decide`) — the
*field-level* antiderivative identity `D(g + ∑ᵢ cᵢ·log(vᵢ)) = f` over the genuine tower fraction field
`RatFunc (RatFunc ℚ)`, with `D = towerFractionFieldDeriv Dt` the keystone derivation (extending the
monomial derivation `Δ = implicitDeriv (toPolyG Dt)` by the quotient rule), in the **primitive regime**
`toPolyG Dt = C w₀` (`Dt ∈ k = ℚ(x)`, e.g. Example 5.6.2's `Dt = 1/x`). The hyperexponential regime
(`Dt ∉ k`) is out of scope — the §5.6 residue match only holds for primitive `Dt`.

**The composition.** Writing `cIntegrate` as `g + (the log sum)` and `f = fₚ + fₛ + fₙ`, the identity
`D(g + ∑ cᵢ log vᵢ) = f` is `D(g_rat) + D(∑ cᵢ log vᵢ) = f`, split by the linearity of the derivation
(`map_add`) into three composing sub-identities, each from a proven sub-piece:

* **The rational (Hermite + poly) part** `D(g_rat) = fₚ + (fₙ − hₛ)` — the integrated piece — from the
  cleared Hermite identity `cHermiteReduceTower_cleared_identity` and the polynomial reductions
  `cPrimitivePolyIntegrate_cleared_identity`, both read at the **field level** through `toPolyG` and the
  quotient rule for `towerFractionFieldDeriv`.
* **The logarithmic part** `D(∑ᵢ cᵢ log vᵢ) = hₛ` — the simple residual of `fₙ` — from
  `towerLogPart_eq_div_of_const_seed` (the §5.6 Rothstein–Trager log-part identity in the primitive
  regime). Here `hₛ = ∑ᵢ cᵢ·(Δvᵢ)/vᵢ` is the residue sum; matching it to the concrete `cLogPart` output
  of the Hermite simple residual is the **documented bridge gap** (the concrete-`cLogArgTower`-to-abstract-
  `Lagrange.nodal` residue match), taken here as the named hypothesis `hLog`.
* **The split** `fₚ + fₛ + fₙ = f` — from `canonicalRepFast_reconstructs` (§3.5).

The field-level identity is the all-inputs generalization of `checkIdentity`'s `cisZeroG` check (which
clears the same fractions over `(RatFunc ℚ)[X]`); the `checkIdentity ↔ field-identity` clearing bridge is
recorded for the rational part. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-- The engine carrier `CFieldSpec.K QFunNZ` is `RatFunc ℚ`, a `ℚ`-algebra. Re-declared as a local
instance (matching the keystone's) so this file synthesizes the **same** `Algebra ℚ` as
`towerFractionFieldDeriv`/`towerLogPart_*`, avoiding an instance-mismatch detour. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-! ### Field-level reading of the proven cleared identities

Each proven sub-piece is the cleared polynomial identity over `(RatFunc ℚ)[X]` (e.g. Hermite's
`(D(gnum)·gden − gnum·D(gden))·Dstar + hNum·gden²)·d = a·(gden²·Dstar)`). Dividing through the nonzero
common denominator lands the **field** identity over the tower fraction field `RatFunc (RatFunc ℚ)`,
where the monomial derivation reads as `towerFractionFieldDeriv Dt` via the quotient rule. We use the
abbreviation `A := algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))` throughout (the embedding of the
tower polynomial ring into its fraction field). -/

/-- Shorthand: the embedding `(RatFunc ℚ)[X] → RatFunc (RatFunc ℚ)` of the tower polynomial ring into
its fraction field — the carrier on which the field-level antiderivative identity lives. -/
noncomputable abbrev towerAlg : (CFieldSpec.K QFunNZ)[X] →+* RatFunc (CFieldSpec.K QFunNZ) :=
  algebraMap (CFieldSpec.K QFunNZ)[X] (RatFunc (CFieldSpec.K QFunNZ))

/-- `towerAlg p ≠ 0` for `p ≠ 0` (the tower polynomial-ring embedding is injective). -/
theorem towerAlg_ne_zero {p : (CFieldSpec.K QFunNZ)[X]} (hp : p ≠ 0) : towerAlg p ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).mpr hp

/-- **Quotient-rule reading of `D(gnum/gden)` over the tower field**: with `g = towerAlg(gnum)/towerAlg(gden)`
(`gden ≠ 0`), `towerFractionFieldDeriv Dt g = (towerAlg(Δ gnum)·towerAlg(gden) − towerAlg(gnum)·towerAlg(Δ gden))
/ (towerAlg(gden))²` where `Δ = implicitDeriv (toPolyG Dt)`. The quotient rule for the keystone derivation,
applied to a fraction of polynomial images. -/
theorem towerFractionFieldDeriv_div (Dt : CPolyG QFunNZ) (gnum gden : (CFieldSpec.K QFunNZ)[X]) :
    towerFractionFieldDeriv Dt (towerAlg gnum / towerAlg gden)
      = (towerAlg (Differential.implicitDeriv (toPolyG Dt) gnum) * towerAlg gden
          - towerAlg gnum * towerAlg (Differential.implicitDeriv (toPolyG Dt) gden))
        / (towerAlg gden) ^ 2 := by
  rw [← RatFunc.mk_eq_div, towerFractionFieldDeriv_mk, RatFunc.mk_eq_div, map_sub, map_mul, map_mul,
    map_pow]

/-! ### The rational part — field-level Hermite + primitive-poly reconstruction

`cIntegrate`'s rational output is `g = gnum/gden` with `gnum = (nrm.rational.1·1) + (pq·nrm.rational.2)`,
`gden = nrm.rational.2` — combining the Hermite rational part `nrm.rational = (gnum_H, gden_H)` of the
normal part with the primitive polynomial quotient `pq` over the common denominator `gden_H`. Its
derivative reconstructs `fₚ + (fₙ − hₛ)`: the polynomial part `fₚ` plus the Hermite-integrated piece of
the normal part. -/

end DeepWiki.SymbolicIntegration
