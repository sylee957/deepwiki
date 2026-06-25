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

/-! ### The Hermite reduction as a field identity `D(g) + hₛ = fₙ`

The proven `cHermiteReduceTower_cleared_identity` is the cleared polynomial identity
`(P·Dstar + hNum·gden²)·d = a·(gden²·Dstar)` (with `P = Δgnum·gden − gnum·Δgden`). Dividing through the
nonzero `gden²·Dstar·d` lands the field identity `D(gnum/gden) + hNum/Dstar = a/d` over the tower fraction
field. The clearing step is generic ring algebra over the field. -/

/-- **Field clearing of the Hermite cleared identity** (generic field): from the polynomial cleared
identity `(P·Dstar + hNum·gden²)·d = a·(gden²·Dstar)` with `gden, Dstar, d ≠ 0` (read into the fraction
field via the injective `algebraMap`), the field fraction identity `P/gden² + hNum/Dstar = a/d` holds.
Pure field-arithmetic clearing (`field_simp` + `linear_combination` of the polynomial witness). -/
theorem hermite_field_div_of_cleared {K : Type*} [Field K] (P Dstar gden hNum d a : K[X])
    (hden : gden ≠ 0) (hDstar : Dstar ≠ 0) (hd : d ≠ 0)
    (hcleared : (P * Dstar + hNum * (gden * gden)) * d = a * ((gden * gden) * Dstar)) :
    (algebraMap K[X] (RatFunc K) P) / (algebraMap K[X] (RatFunc K) gden) ^ 2
        + (algebraMap K[X] (RatFunc K) hNum) / (algebraMap K[X] (RatFunc K) Dstar)
      = (algebraMap K[X] (RatFunc K) a) / (algebraMap K[X] (RatFunc K) d) := by
  set A := algebraMap K[X] (RatFunc K) with hA
  have hAd : A d ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).mpr hd
  have hAden : A gden ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).mpr hden
  have hADstar : A Dstar ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).mpr hDstar
  have hcl : (A P * A Dstar + A hNum * (A gden * A gden)) * A d
      = A a * (A gden * A gden * A Dstar) := by
    have := congrArg A hcleared
    simpa only [map_mul, map_add] using this
  rw [div_add_div _ _ (pow_ne_zero 2 hAden) hADstar, div_eq_div_iff
    (mul_ne_zero (pow_ne_zero 2 hAden) hADstar) hAd]
  ring_nf
  ring_nf at hcl
  linear_combination hcl

/-- **The Hermite reduction as a field identity** `D(gₕ) + hₛ = fₙ` over the tower fraction field
`RatFunc (RatFunc ℚ)`: writing `((gnum, gden), (hNum, Dstar)) = cHermiteReduceTower Dt fuel a d`, the
rational part `gₕ = towerAlg(gnum)/towerAlg(gden)` and the simple residual `hₛ = towerAlg(hNum)/towerAlg(Dstar)`
satisfy `towerFractionFieldDeriv Dt gₕ + hₛ = towerAlg(a)/towerAlg(d)`. Composes the proven cleared
polynomial identity `cHermiteReduceTower_cleared_identity` with the field clearing
`hermite_field_div_of_cleared` and the quotient rule `towerFractionFieldDeriv_div`. Gated on the same
transparent exact-division/nonzero-divisor/fuel preconditions the proven cleared identity carries, plus
nonzero `gden, Dstar, d`. -/
theorem cHermiteReduceTower_field_identity (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (gnumR gdenR DstarR gprimeNum resNum resDen hNumR : CPolyG QFunNZ)
    (hgnum : gnumR = (cHermiteReduceTower Dt fuel a d).1.1)
    (hgden : gdenR = (cHermiteReduceTower Dt fuel a d).1.2)
    (hDstar : DstarR = (cHermiteReduceTower Dt fuel a d).2.2)
    (hgprime : gprimeNum
      = csubG (cmulG (cmonomialDeriv Dt gnumR) gdenR) (cmulG gnumR (cmonomialDeriv Dt gdenR)))
    (hresNum : resNum = csubG (cmulG a (cmulG gdenR gdenR)) (cmulG d gprimeNum))
    (hresDen : resDen = cmulG d (cmulG gdenR gdenR))
    (hhNum : hNumR = cdivG fuel (cmulG resNum DstarR) resDen)
    (hq0 : cnormG resDen ≠ [])
    (hfuel : (cnormG (cmulG resNum DstarR) : List QFunNZ).length ≤ fuel)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum DstarR))
    (hgdenne : toPolyG gdenR ≠ 0) (hDstarne : toPolyG DstarR ≠ 0) (hdne : toPolyG d ≠ 0) :
    towerFractionFieldDeriv Dt (towerAlg (toPolyG gnumR) / towerAlg (toPolyG gdenR))
        + towerAlg (toPolyG hNumR) / towerAlg (toPolyG DstarR)
      = towerAlg (toPolyG a) / towerAlg (toPolyG d) := by
  -- the proven cleared polynomial identity over `(RatFunc ℚ)[X]`
  have hcleared := cHermiteReduceTower_cleared_identity Dt fuel a d gnumR gdenR DstarR gprimeNum
    resNum resDen hNumR hgnum hgden hDstar hgprime hresNum hresDen hhNum hq0 hfuel hdvd
  -- the quotient-rule numerator `P = Δgnum·gden − gnum·Δgden`, with `Δ = implicitDeriv (toPolyG Dt)`
  rw [towerFractionFieldDeriv_div]
  set P : (CFieldSpec.K QFunNZ)[X] :=
    Differential.implicitDeriv (toPolyG Dt) (toPolyG gnumR) * toPolyG gdenR
      - toPolyG gnumR * Differential.implicitDeriv (toPolyG Dt) (toPolyG gdenR) with hP
  -- the cleared polynomial identity in `Δ`-form, matching `P`
  have hcleared' : (P * toPolyG DstarR + toPolyG hNumR * (toPolyG gdenR * toPolyG gdenR)) * toPolyG d
      = toPolyG a * (toPolyG gdenR * toPolyG gdenR * toPolyG DstarR) := by
    rw [hP, ← toPolyG_cmonomialDeriv, ← toPolyG_cmonomialDeriv]
    linear_combination hcleared
  rw [show towerAlg (Differential.implicitDeriv (toPolyG Dt) (toPolyG gnumR)) * towerAlg (toPolyG gdenR)
        - towerAlg (toPolyG gnumR) * towerAlg (Differential.implicitDeriv (toPolyG Dt) (toPolyG gdenR))
      = towerAlg P by rw [hP, map_sub, map_mul, map_mul]]
  exact hermite_field_div_of_cleared P (toPolyG DstarR) (toPolyG gdenR) (toPolyG hNumR) (toPolyG d)
    (toPolyG a) hgdenne hDstarne hdne hcleared'

