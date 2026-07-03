import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalAssembly
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalOverTower
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalLogArgGeneric

/-! # Unified elementary integration over a transcendental tower.

The carrier `AlgIntegralResultG` (`∫ = v + Σ cᵢ log uᵢ`), its derivative `algDerivG`, and the
driver `cIntegrateElementaryG` over a tower base `α = QFunNZG β`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

/-! ### `AlgIntegralResultG` and its derivative -/

/-- Tower-generic elementary integral `∫ = v + Σ cᵢ log uᵢ`: rational part `v : RadElem α` plus
log terms `[(cᵢ, uᵢ)]` (`cᵢ ∈ α`, `uᵢ ∈ α[y]/(y² − ρ)`). -/
structure AlgIntegralResultG (α : Type*) [CField α] where
  /-- The rational part `v` of `∫ = v + Σ cᵢ log uᵢ` (a `RadElem α`). -/
  ratPart : RadElem α
  /-- The log terms `[(cᵢ, uᵢ)]` (`cᵢ ∈ α`, `uᵢ : RadElem α`). -/
  logTerms : List (α × RadElem α)

/-- Derivative `algDerivG ρ F = radDeriv v + Σ cᵢ · radLogDeriv uᵢ` in `α[y]/(y² − ρ)`, using the
tower's `CDiffField.cderiv` as base derivation. -/
def algDerivG {α : Type*} [CField α] [CDiffField α] (ρ : α) (F : AlgIntegralResultG α) : RadElem α :=
  F.logTerms.foldl
    (fun acc (c, u) => radAdd acc (radScale c (radLogDeriv ρ u)))
    (radDeriv 2 ρ F.ratPart)

/-! ### `cIntegrateElementaryG` — the driver over a tower base `α = QFunNZG β` -/

/-- Elementary integrator `cIntegrateElementaryG ρ v residual c D degBound` over `α = QFunNZG β`,
`y² = ρ`: supplied rational part `v`, log argument from `radLogArgSolveG ρ residual D degBound`.
On `some N` packs the log term `(c, N/D)`; on `none` returns `⟨v, []⟩`. -/
def cIntegrateElementaryG {β : Type*} [CField β] [CFieldDomain β] [CDiffField (QFunNZG β)]
    (ρ : QFunNZG β) (v : RadElem (QFunNZG β)) (residual : RadElem (QFunNZG β)) (c : QFunNZG β)
    (D : CPolyG β) (degBound : ℕ) : AlgIntegralResultG (QFunNZG β) :=
  match radLogArgSolveG ρ residual D degBound with
  | none => ⟨v, []⟩
  | some N =>
    let Dq : QFunNZG β := qOfNumG D
    let u : RadElem (QFunNZG β) := N.map (fun z => CField.div z Dq)   -- u = N/D
    ⟨v, [(c, u)]⟩

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
def elemF : AlgIntegralResultG Lvl2 := ⟨elemRatPart, [(CField.one, elemLogArg)]⟩

/-- The combined integrand `algDerivG F` over ℚ(x)(eˣ) with the exp-tower derivation, equal to
`√(eˣ+1) = y`. -/
def elemIntegrand : RadElem Lvl2 := @algDerivG _ _ expTowerDiff elemRho elemF

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

/-- The log-solve denominator `D = θ = eˣ` as the `CPolyG (QFunNZG ℚ)` `[0, 1]`. -/
def elemDenTheta : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- The recovered result `F' = cIntegrateElementaryG ρ (2y) residual 1 θ 1` over ℚ(x)(eˣ). -/
def elemRecovered : AlgIntegralResultG Lvl2 :=
  @cIntegrateElementaryG _ _ _ expTowerDiff elemRho elemRatPart elemLogResidual CField.one elemDenTheta 1

/-- Round-trip `algDerivG F' = elemIntegrand` over ℚ(x)(eˣ): `radIsZero (algDerivG F' − integrand)`. -/
theorem rt_elementary_combined :
    radIsZero (radSub (@algDerivG _ _ expTowerDiff elemRho elemRecovered) elemIntegrand) = true := by
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
