import DeepWiki.SymbolicIntegration.ComputableRadicalAssembly
import DeepWiki.SymbolicIntegration.ComputableRadicalOverTower
import DeepWiki.SymbolicIntegration.ComputableRadicalLogArgGeneric

/-! # Unified elementary integration over a transcendental tower

The tower-generic elementary-integral carrier `AlgIntegralResultG` (`∫ = v + Σ cᵢ log uᵢ`), its
actual-derivation derivative `algDerivG`, and the unified driver `cIntegrateElementaryG` over a
tower base `α = QFunNZG β`, validated by the round-trip
`∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` over `ℚ(x)(eˣ)` with the exponential derivation. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

/-! ### `AlgIntegralResultG` and its actual-derivation derivative

The generic analogue of `AlgIntegralResult` (`ComputableRadicalAssembly`, pinned to `QFunNZG ℚ`):
a rational part `v` plus log terms `(cᵢ, uᵢ)` over an arbitrary base field `α`. The derivative
`algDerivG` consumes the tower's `[CDiffField α]`, so the base-field derivation is the genuine
tower derivation (`θ = eˣ ⇒ θ' = θ`), not the formal `θ' = 1`. -/

/-- Tower-generic full elementary integral `∫ = v + Σ cᵢ log uᵢ` — the rational part `v` (a
`RadElem α`) plus the log terms `logs = [(c₁, u₁), …]` (coefficient `cᵢ ∈ α`, argument
`uᵢ ∈ α[y]/(y² − ρ)`). The output of `cIntegrateElementaryG`, differentiated by `algDerivG`. -/
structure AlgIntegralResultG (α : Type*) [CField α] where
  /-- The rational part `v` of `∫ = v + Σ cᵢ log uᵢ` (a radical-extension element over `α`). -/
  ratPart : RadElem α
  /-- The log terms `[(c₁, u₁), …]`: each a coefficient `cᵢ ∈ α` and an argument `uᵢ` (a `RadElem α`). -/
  logTerms : List (α × RadElem α)

/-- Derivative of a tower-generic elementary integral `algDerivG ρ F = radDeriv v + Σ cᵢ ·
radLogDeriv uᵢ` in `α[y]/(y² − ρ)`, with the base derivation the tower's `CDiffField.cderiv` (not
the formal `cderivG`). Each log term contributes `cᵢ · (uᵢ'/uᵢ)` via `radScale`/`radLogDeriv`
(division by the generic `radInv2`), summed onto `radDeriv v`. Over `α = ℚ(x)(eˣ)` with
`expTowerDiff` it is the genuine exp-tower derivative (`θ' = θ`). -/
def algDerivG {α : Type*} [CField α] [CDiffField α] (ρ : α) (F : AlgIntegralResultG α) : RadElem α :=
  F.logTerms.foldl
    (fun acc (c, u) => radAdd acc (radScale c (radLogDeriv ρ u)))
    (radDeriv 2 ρ F.ratPart)

/-! ### `cIntegrateElementaryG` — the unified driver over a tower base `α = QFunNZG β`

The rational part `v` is supplied: the Hermite rational-part dispatch `radIntegrateRational` runs
with the independent-θ derivation (`θ' = 1`), which is the wrong derivation for `θ = eˣ`;
reconstructing `v` under the actual tower derivation would need a radicand-level reduction layer
not built here. The log half is computed by `radLogArgSolveG` over the tower field `β` with the
actual tower derivation. -/

/-- Unified elementary integrator over a tower base `cIntegrateElementaryG ρ v residual c D
degBound` over `α = QFunNZG β`, `y² = ρ` — produces `∫ = v + c·log(N/D)` in the principal case.
The rational part `v` is supplied; the log argument is computed on the `residual` integrand by
`radLogArgSolveG ρ residual D degBound` (the principal-case linear solve with the actual tower
derivation). On `some N` packs the log term `(c, N/D)` (`u = N.map (·/Dq)`, `Dq = qOfNumG D` the
lift of `D` to `α`); on `none` (non-principal / torsion boundary) returns the rational-only partial
`⟨v, []⟩`. Needs `[CField β] [CFieldDomain β] [CDiffField (QFunNZG β)]` (the latter the actual
tower derivation fed to the solve). -/
def cIntegrateElementaryG {β : Type*} [CField β] [CFieldDomain β] [CDiffField (QFunNZG β)]
    (ρ : QFunNZG β) (v : RadElem (QFunNZG β)) (residual : RadElem (QFunNZG β)) (c : QFunNZG β)
    (D : CPolyG β) (degBound : ℕ) : AlgIntegralResultG (QFunNZG β) :=
  match radLogArgSolveG ρ residual D degBound with
  | none => ⟨v, []⟩
  | some N =>
    let Dq : QFunNZG β := qOfNumG D
    let u : RadElem (QFunNZG β) := N.map (fun z => CField.div z Dq)   -- u = N/D
    ⟨v, [(c, u)]⟩

/-! ### Round-trip validation: `∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` over ℚ(x)(eˣ)

`β = ℚ(x) = QFunNZG ℚ`, `α = QFunNZG β = ℚ(x)(eˣ) = Lvl2`, `θ = eˣ`, `ρ = θ+1`, `y² = ρ`,
exponential derivation `expTowerDiff` (`t₁' = t₁`). The integrand `√(eˣ+1) = y` splits as a
rational part `v = 2y` (`(2y)' = (θ/(θ+1))·y = eˣ/√(eˣ+1)`) plus a log part `log u`,
`u = (y−1)/(y+1) = ((θ+2)−2y)/θ` (`(log u)' = 1/√(eˣ+1)`). -/

/-- The round-trip radicand `ρ = θ+1 = eˣ+1 ∈ ℚ(x)(eˣ)` — the same carrier value as `expRadicand`
(`ComputableRadicalOverTower`). -/
def elemRho : Lvl2 := expRadicand

/-- The rational part `v = 2√(eˣ+1) = 2y` as the `RadElem Lvl2` `[0, 2]` over ℚ(x)(eˣ) — supplied
to the driver (see the scope note on `cIntegrateElementaryG`). Its actual-derivation derivative is
`(θ/(θ+1))·y = eˣ/√(eˣ+1)`. -/
def elemRatPart : RadElem Lvl2 := [CField.zero, CField.add CField.one CField.one]

/-- The expected log argument `u = (y−1)/(y+1) = ((θ+2)−2y)/θ ∈ ℚ(x)(eˣ)[y]/(y²−ρ)`, the `RadElem`
`[(θ+2)/θ, −2/θ]`. Used to build the starting antiderivative `F`; the driver re-computes it (up to
a scalar) from the residual via `radLogArgSolveG`. -/
def elemLogArg : RadElem Lvl2 :=
  [CField.div (CField.add expTheta (CField.add CField.one CField.one)) expTheta,
   CField.div (CField.neg (CField.add CField.one CField.one)) expTheta]

/-- The starting combined antiderivative `F = 2y + 1·log((y−1)/(y+1))` over ℚ(x)(eˣ) — rational
part `elemRatPart`, one log term `(1, elemLogArg)`. -/
def elemF : AlgIntegralResultG Lvl2 := ⟨elemRatPart, [(CField.one, elemLogArg)]⟩

/-- The combined integrand `algDerivG F` over ℚ(x)(eˣ) with the exp-tower derivation
`expTowerDiff`: `radDeriv(2y) + radLogDeriv(u) = eˣ/√(eˣ+1) + 1/√(eˣ+1) = √(eˣ+1) = y`. -/
def elemIntegrand : RadElem Lvl2 := @algDerivG _ _ expTowerDiff elemRho elemF

/-- The combined integrand is `√(eˣ+1) = y`: the exp-tower derivative of
`F = 2y + log((y−1)/(y+1))` is the radical generator `y = [0,1]` (checked by `radIsZero` of
`integrand − y`), so both halves contribute:
`eˣ/√(eˣ+1) + 1/√(eˣ+1) = (eˣ+1)/√(eˣ+1) = √(eˣ+1)`. -/
theorem elemIntegrand_eq_radGen :
    radIsZero (radSub elemIntegrand (radGen : RadElem Lvl2)) = true := by native_decide

/-- The log residual the solve must absorb, `1/√(eˣ+1) = 1/y` lifted to `[0, 1/ρ]` over ℚ(x)(eˣ)
(`ρ = eˣ+1`) — the log-derivative half of the combined integrand (the same value as
`expArgIntegrand`, `ComputableRadicalLogArgGeneric`). -/
def elemLogResidual : RadElem Lvl2 := radInvYLift elemRho CField.one

/-- The residual equals `integrand − radDeriv(2y)`: the log residual `1/√(eˣ+1)` fed to the log
solve is exactly the combined integrand minus the rational-part derivative (both under the
exp-tower derivation) — the rational/log split of the integrand is exact:
`√(eˣ+1) − eˣ/√(eˣ+1) = 1/√(eˣ+1)`. -/
theorem elemLogResidual_eq_integrand_sub_ratDeriv :
    radIsZero (radSub elemLogResidual
      (radSub elemIntegrand (@radDeriv _ _ expTowerDiff 2 elemRho elemRatPart))) = true := by
  native_decide

/-- The fixed log-solve denominator `D = θ = eˣ` as a `CPolyG (QFunNZG ℚ)` (`β = ℚ(x)`): the
polynomial `t₁`, i.e. `[0, 1]` — the same value as `expDenTheta`
(`ComputableRadicalLogArgGeneric`), the denominator of `u = ((θ+2)−2y)/θ`. -/
def elemDenTheta : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- The recovered combined result `F' = cIntegrateElementaryG ρ (2y) residual 1 θ 1` over
ℚ(x)(eˣ): the rational part `2y` is supplied, and the log argument is computed from the residual
`[0, 1/ρ]` by `radLogArgSolveG` (the exp derivation `expTowerDiff`, `D = θ`, degree `1`) —
`u = N/θ` with `N` a kernel vector over `β = ℚ(x)`. -/
def elemRecovered : AlgIntegralResultG Lvl2 :=
  @cIntegrateElementaryG _ _ _ expTowerDiff elemRho elemRatPart elemLogResidual CField.one elemDenTheta 1

/-- Combined round-trip `algDerivG F' = integrand` over ℚ(x)(eˣ): differentiating the recovered
`F' = ⟨2y, [(1, u)]⟩` (rational part supplied, log half computed by `radLogArgSolveG`) under the
exp-tower derivation gives back the integrand `√(eˣ+1) = y` — so
`∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` is validated over the tower through the real radical
derivation. Checked by `radIsZero` of `algDerivG F' − integrand`. -/
theorem rt_elementary_combined :
    radIsZero (radSub (@algDerivG _ _ expTowerDiff elemRho elemRecovered) elemIntegrand) = true := by
  native_decide

/-- The recovered result has nonzero rational part and exactly one log term — the structural
signature of a genuine combined elementary integral `∫ = v + c·log u`. Checked on
`(radIsZero F'.ratPart, F'.logTerms.length) = (false, 1)`. -/
theorem rt_elementary_combined_shape :
    (radIsZero elemRecovered.ratPart, elemRecovered.logTerms.length) = (false, 1) := by native_decide

/-- The computed tower log argument is a nonzero constant multiple of `(θ+2) − 2y`: the recovered
`u = N/θ = [a₀, a₁]` has `a₁ ≠ 0` and `a₀·(−2) = a₁·(θ+2)`, i.e. `N = c·((θ+2) − 2y)` for a
nonzero `c` — matching the closed form `u = (y−1)/(y+1)` up to the log argument's scalar
freedom. -/
theorem elemRecovered_logArg_matches_closed_form :
    (elemRecovered.logTerms.headD (CField.one, []) |>.2 |> fun u =>
      let a0 := u.getD 0 CField.zero
      let a1 := u.getD 1 CField.zero
      (CField.isZero a1 == false) &&
      CField.isZero (CField.sub (CField.mul a0 (CField.neg (CField.add CField.one CField.one)))
        (CField.mul a1 (CField.add expTheta (CField.add CField.one CField.one))))) = true := by
  native_decide

end DeepWiki.SymbolicIntegration
