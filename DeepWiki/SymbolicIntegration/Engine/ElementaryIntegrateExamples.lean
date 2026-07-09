import DeepWiki.SymbolicIntegration.Engine.ElementaryIntegrate
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalOverTower

/-! # Elementary integration examples over a transcendental tower

Concrete `native_decide` round-trip validation for
`∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` over `ℚ(x)(eˣ)`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPoly

/-! ### Round-trip validation: `∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` over ℚ(x)(eˣ) -/

/-- The round-trip radicand `ρ = θ+1 = eˣ+1 ∈ ℚ(x)(eˣ)` (same value as `expRadicand`). -/
def elemRho : Lvl2 := expRadicand

/-- The rational part `v = 2√(eˣ+1) = 2y` as the `RadElem Lvl2` `[0, 2]` over ℚ(x)(eˣ). -/
def elemRatPart : RadElem Lvl2 := [CField.zero, CField.add CField.one CField.one]

/-- The log argument `u = (y−1)/(y+1) = ((θ+2)−2y)/θ ∈ ℚ(x)(eˣ)[y]/(y²−ρ)`, the `RadElem`
`[(θ+2)/θ, −2/θ]`. -/
def elemLogArg : RadElem Lvl2 :=
  [CField.div (CField.add expTheta (CField.add CField.one CField.one)) expTheta,
   CField.div (CField.neg (CField.add CField.one CField.one)) expTheta]

/-- The combined antiderivative `F = 2y + log((y−1)/(y+1))` over ℚ(x)(eˣ): `elemRatPart` plus one
log term `(1, elemLogArg)`. -/
def elemF : AlgIntegralResult Lvl2 := ⟨elemRatPart, [(CField.one, elemLogArg)]⟩

/-- The combined integrand `algDeriv F` over ℚ(x)(eˣ) with the exp-tower derivation, equal to
`√(eˣ+1) = y`. -/
def elemIntegrand : RadElem Lvl2 := @algDeriv _ _ expTowerDiff elemRho elemF

/-- The combined integrand equals the radical generator `y`: `radIsZero (elemIntegrand − radGen)`. -/
theorem elemIntegrand_eq_radGen :
    radIsZero (radSub elemIntegrand (radGen : RadElem Lvl2)) = true := by native_decide

/-- The log residual `1/√(eˣ+1) = 1/y` lifted to `[0, 1/ρ]` over ℚ(x)(eˣ) (`ρ = eˣ+1`). -/
def elemLogResidual : RadElem Lvl2 := radInvYLift elemRho CField.one

/-- The log residual equals `elemIntegrand − radDeriv(2y)` under the exp-tower derivation. -/
theorem elemLogResidual_eq_integrand_sub_ratDeriv :
    radIsZero (radSub elemLogResidual
      (radSub elemIntegrand (@radDeriv _ _ expTowerDiff 2 elemRho elemRatPart))) = true := by
  native_decide

/-- The log-solve denominator `D = θ = eˣ` as the `CPoly (QFunNZ ℚ)` `[0, 1]`. -/
def elemDenTheta : CPoly (QFunNZ ℚ) := [CField.zero, CField.one]

/-- The recovered result `F' = cIntegrateElementary ρ (2y) residual 1 θ 1` over ℚ(x)(eˣ). -/
def elemRecovered : AlgIntegralResult Lvl2 :=
  @cIntegrateElementary _ _ _ expTowerDiff elemRho elemRatPart elemLogResidual CField.one elemDenTheta 1

/-- Round-trip `algDeriv F' = elemIntegrand` over ℚ(x)(eˣ): `radIsZero (algDeriv F' − integrand)`. -/
theorem rt_elementary_combined :
    radIsZero (radSub (@algDeriv _ _ expTowerDiff elemRho elemRecovered) elemIntegrand) = true := by
  native_decide

/-- The recovered result has nonzero rational part and exactly one log term:
`(radIsZero F'.ratPart, F'.logTerms.length) = (false, 1)`. -/
theorem rt_elementary_combined_shape :
    (radIsZero elemRecovered.ratPart, elemRecovered.logTerms.length) = (false, 1) := by native_decide

/-- The recovered log argument `u = [a₀, a₁]` has `a₁ ≠ 0` and `a₀·(−2) = a₁·(θ+2)`, i.e. it is a
nonzero constant multiple of `(θ+2) − 2y`. -/
theorem elemRecovered_logArg_matches_closed_form :
    (elemRecovered.logTerms.headD (CField.one, []) |>.2 |> fun u =>
      let a0 := u.getD 0 CField.zero
      let a1 := u.getD 1 CField.zero
      (CField.isZero a1 == false) &&
      CField.isZero (CField.sub (CField.mul a0 (CField.neg (CField.add CField.one CField.one)))
        (CField.mul a1 (CField.add expTheta (CField.add CField.one CField.one))))) = true := by
  native_decide

end DeepWiki.SymbolicIntegration
