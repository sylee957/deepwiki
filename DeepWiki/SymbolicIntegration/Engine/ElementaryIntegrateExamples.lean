import DeepWiki.SymbolicIntegration.Engine.ElementaryIntegrate
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalOverTower

/-! # Elementary integration examples over a transcendental tower

Concrete `native_decide` round-trip validation for
`∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` over `ℚ(x)(eˣ)`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

/-! ### Round-trip validation: `∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` over ℚ(x)(eˣ) -/

/-- The rational part `v = 2√(eˣ+1) = 2y` as the `RadElem Lvl2` `[0, 2]` over ℚ(x)(eˣ). -/
def elemRatPart : RadElem Lvl2 := [CCommRing.zero, CCommRing.add CCommRing.one CCommRing.one]

/-- The log argument `u = (y−1)/(y+1) = ((θ+2)−2y)/θ ∈ ℚ(x)(eˣ)[y]/(y²−ρ)`, the `RadElem`
`[(θ+2)/θ, −2/θ]`. -/
def elemLogArg : RadElem Lvl2 :=
  [CField.div (CCommRing.add expTheta (CCommRing.add CCommRing.one CCommRing.one)) expTheta,
   CField.div (CCommRing.neg (CCommRing.add CCommRing.one CCommRing.one)) expTheta]

/-- The combined antiderivative `F = 2y + log((y−1)/(y+1))` over ℚ(x)(eˣ): `elemRatPart` plus one
log term `(1, elemLogArg)`. -/
def elemF : AlgIntegralResult Lvl2 := ⟨elemRatPart, [(CCommRing.one, elemLogArg)]⟩

/-- The combined integrand `algDeriv F` over ℚ(x)(eˣ) with the exp-tower derivation, equal to
`√(eˣ+1) = y`. -/
def elemIntegrand : RadElem Lvl2 := @algDeriv _ _ expTowerDiff expRadicand elemF

/-- The combined integrand equals the radical generator `y`: `DensePoly.cisZero (elemIntegrand − radGen)`. -/
theorem elemIntegrand_eq_radGen :
    DensePoly.cisZero (DensePoly.csub elemIntegrand (radGen : RadElem Lvl2)) = true := by native_decide

/-- The log residual `1/√(eˣ+1) = 1/y` lifted to `[0, 1/ρ]` over ℚ(x)(eˣ) (`ρ = eˣ+1`). -/
def elemLogResidual : RadElem Lvl2 := radInvYLift expRadicand CCommRing.one

/-- The log residual equals `elemIntegrand − radDeriv(2y)` under the exp-tower derivation. -/
theorem elemLogResidual_eq_integrand_sub_ratDeriv :
    DensePoly.cisZero (DensePoly.csub elemLogResidual
      (DensePoly.csub elemIntegrand (@radDeriv _ _ expTowerDiff 2 expRadicand elemRatPart))) = true := by
  native_decide

/-- The log-solve denominator `D = θ = eˣ` as the `DensePoly (DenseFrac ℚ)` `[0, 1]`. -/
def elemDenTheta : DensePoly (DenseFrac ℚ) := [CCommRing.zero, CCommRing.one]

/-- The recovered result `F' = cIntegrateElementary ρ (2y) residual 1 θ 1` over ℚ(x)(eˣ). -/
def elemRecovered : AlgIntegralResult Lvl2 :=
  letI : CDiffField Lvl2 := expTowerDiff
  cIntegrateElementary expRadicand elemRatPart elemLogResidual CCommRing.one elemDenTheta 1

/-- Round-trip `algDeriv F' = elemIntegrand` over ℚ(x)(eˣ): `DensePoly.cisZero (algDeriv F' − integrand)`. -/
theorem rt_elementary_combined :
    DensePoly.cisZero
      (DensePoly.csub (@algDeriv _ _ expTowerDiff expRadicand elemRecovered) elemIntegrand) = true := by
  native_decide

/-- The recovered result has nonzero rational part and exactly one log term:
`(DensePoly.cisZero F'.ratPart, F'.logTerms.length) = (false, 1)`. -/
theorem rt_elementary_combined_shape :
    (DensePoly.cisZero elemRecovered.ratPart, elemRecovered.logTerms.length) = (false, 1) := by native_decide

/-- The recovered log argument `u = [a₀, a₁]` has `a₁ ≠ 0` and `a₀·(−2) = a₁·(θ+2)`, i.e. it is a
nonzero constant multiple of `(θ+2) − 2y`. -/
theorem elemRecovered_logArg_matches_closed_form :
    (elemRecovered.logTerms.headD (CCommRing.one, []) |>.2 |> fun u =>
      let a0 := u.getD 0 CCommRing.zero
      let a1 := u.getD 1 CCommRing.zero
      (CCommRing.isZero a1 == false) &&
      CCommRing.isZero (CField.sub (CCommRing.mul a0 (CCommRing.neg (CCommRing.add CCommRing.one CCommRing.one)))
        (CCommRing.mul a1 (CCommRing.add expTheta (CCommRing.add CCommRing.one CCommRing.one))))) = true := by
  native_decide

end DeepWiki.SymbolicIntegration
