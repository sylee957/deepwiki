import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalExtension
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalWellFounded
import DeepWiki.SymbolicIntegration.Computable.Tower.Field
import DeepWiki.SymbolicIntegration.Computable.Tower.Deriv
import DeepWiki.SymbolicIntegration.Computable.Tower.GcdFFCore

/-! # Simple radicals over a transcendental tower

Instantiating the radical extension `RadExt` at a transcendental tower level `α = ℚ(x)(eˣ)` (or
`ℚ(x)(log x)`), so the radicand `ρ` is a genuine field element of the tower and the algebraic
arc (`radDeriv`, `radMul`) runs over the exponential/logarithmic engine. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem

/-! ### The exponential tower base `α = ℚ(x)(eˣ) = QFunNZG (QFunNZG ℚ)`

`Lvl2 = QFunNZG (QFunNZG ℚ)` is the field `ℚ(x)(t₁)`. To make `t₁ = eˣ` its `CDiffField` derivation
becomes `towerDerivQFunNZG [t₁]` (so `t₁' = t₁`) instead of the default `t₁' = 1`. -/

/-- A level-2 scalar `c ∈ Lvl2 = ℚ(x)(t₁)` from a numerator `CPolyG (QFunNZG ℚ)` over denominator `1`;
the level-2 analogue of `qxOfNum`. -/
def lvl2OfNum (num : CPolyG (QFunNZG ℚ)) : Lvl2 :=
  ⟨(num, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- The exponential monomial `θ = t₁ = eˣ ∈ ℚ(x)(t₁)` (numerator `[0, 1]`, denominator `[1]`). -/
def expTheta : Lvl2 := lvl2OfNum [(CField.zero : QFunNZG ℚ), CField.one]

/-- The radicand `ρ = θ + 1 = eˣ + 1 ∈ ℚ(x)(t₁)` (numerator `[1, 1]`), the element with `y² = ρ`. -/
def expRadicand : Lvl2 := lvl2OfNum [(CField.one : QFunNZG ℚ), CField.one]

/-- The new-monomial derivative `Dt₁ = t₁ = [0, 1] ∈ CPolyG (QFunNZG ℚ)` making `t₁` exponential
(`t₁' = t₁`), fed to `towerDerivQFunNZG`. -/
def expDt1 : CPolyG (QFunNZG ℚ) := [(CField.zero : QFunNZG ℚ), CField.one]

/-- The exponential `CDiffField Lvl2` instance `cderiv := towerDerivQFunNZG [t₁]` (so `t₁' = t₁`, `t₁ = eˣ`).
A local `def` passed to the radical ops via `@`, leaving the default `t₁' = 1` derivation untouched. -/
@[reducible] def expTowerDiff : CDiffField Lvl2 where
  cderiv := QFunNZG.towerDerivQFunNZG expDt1

/-- `D(t₁) = t₁` under `expTowerDiff`: the derivation sends `t₁` to itself. -/
theorem expTheta_deriv_eq_self :
    CField.isZero (CField.sub (@CDiffField.cderiv _ _ expTowerDiff expTheta) expTheta)
      = true := by native_decide

/-- `D(t₁+1) = t₁`: the radicand derivative `ρ' = (t₁+1)' = t₁`, the numerator `ρ'` of `y' = ρ'/(2y)`. -/
theorem expRadicand_deriv_eq_theta :
    CField.isZero (CField.sub (@CDiffField.cderiv _ _ expTowerDiff expRadicand) expTheta)
      = true := by native_decide

/-! ### The radical `y² = eˣ+1` over the exponential tower

Over `α = ℚ(x)(eˣ)` with `n = 2`, `ρ = eˣ+1`: the defining relation `y·y = ρ` and the diagonal
derivation `D(y) = (ρ'/(2ρ))·y = (θ/(2(θ+1)))·y`. -/

/-- The diagonal multiplier `ℓ = ρ'/(2ρ) = θ/(2(θ+1)) ∈ ℚ(x)(eˣ)` for `D(y) = ℓ·y` at `expTowerDiff`. -/
def expRadLogDer : Lvl2 := @logDerRadicand _ _ expTowerDiff 2 expRadicand

/-- `y·y = eˣ+1`: the square of `y = √(eˣ+1)` reduces via the `y² → ρ` fold to `ρ = eˣ+1`. -/
theorem expRadGen_sq_eq_radicand :
    radIsZero (radSub (radMul 2 expRadicand (radGen : RadElem Lvl2) radGen) [expRadicand])
      = true := by native_decide

/-- `D(y) = (θ/(2(θ+1)))·y`: the diagonal radical derivation of `y = √(eˣ+1)` with the exponential
base derivation is `ℓ·y`, `ℓ = ρ'/(2ρ)`. -/
theorem expRadDeriv_radGen_eq :
    radIsZero (radSub (@radDeriv _ _ expTowerDiff 2 expRadicand (radGen : RadElem Lvl2))
        [CField.zero, expRadLogDer]) = true := by native_decide

/-! ### `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` over ℚ(x)(eˣ)

Integrand `eˣ/√(eˣ+1) = θ/y = [0, θ/(θ+1)]`, antiderivative `2√(eˣ+1) = 2y = [0, 2]`, validated
through `radDeriv [0, 2] = integrand`. -/

/-- The integrand `eˣ/√(eˣ+1) = θ/y` as the pure-`y` `RadElem` `[0, θ/(θ+1)]` over ℚ(x)(eˣ). -/
def expIntegrand : RadElem Lvl2 :=
  [CField.zero, CField.div expTheta expRadicand]

/-- The antiderivative `2√(eˣ+1) = 2y` as the `RadElem` `[0, 2]` over ℚ(x)(eˣ). -/
def expAntideriv : RadElem Lvl2 :=
  [CField.zero, CField.add CField.one CField.one]

/-- `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)`: `radDeriv` of the antiderivative `2y = [0, 2]` equals the integrand
`θ/y = [0, θ/(θ+1)]` over the transcendental tower. -/
theorem expIntegral_eq :
    radIsZero (radSub (@radDeriv _ _ expTowerDiff 2 expRadicand expAntideriv) expIntegrand)
      = true := by native_decide

/-! ### The `log` companion: `∫ dx/(x√(log x)) = 2√(log x)` over ℚ(x)(log x)

The same arc with a logarithmic monomial `θ = log x` (`θ' = 1/x`), radicand `ρ = log x`. -/

/-- The level-2 element `1/x ∈ ℚ(x) ⊂ ℚ(x)(log x)` as a `Lvl2` value (numerator `[1/x]`, denominator `[1]`). -/
def lvl2OneOverX : Lvl2 :=
  lvl2OfNum [qxOfFrac [1] [0, 1] (by decide)]

/-- The logarithmic monomial `θ = t₁ = log x ∈ ℚ(x)(log x)` (numerator `[0, 1]`, denominator `[1]`). -/
def logTheta : Lvl2 := lvl2OfNum [(CField.zero : QFunNZG ℚ), CField.one]

/-- The radicand `ρ = θ = log x ∈ ℚ(x)(log x)` (`y² = log x`), numerator `[0, 1]`, denominator `[1]`. -/
def logRadicandT : Lvl2 := lvl2OfNum [(CField.zero : QFunNZG ℚ), CField.one]

/-- The new-monomial derivative `Dt₁ = θ' = 1/x ∈ CPolyG (QFunNZG ℚ)` making `t₁` logarithmic (`t₁' = 1/x`). -/
def logDt1 : CPolyG (QFunNZG ℚ) := [qxOfFrac [1] [0, 1] (by decide)]

/-- The logarithmic `CDiffField Lvl2` instance `cderiv := towerDerivQFunNZG [1/x]` (so `t₁' = 1/x`,
`t₁ = log x`). A local `def` supplied via `@`. -/
@[reducible] def logTowerDiff : CDiffField Lvl2 where
  cderiv := QFunNZG.towerDerivQFunNZG logDt1

/-- `D(t₁) = 1/x` under `logTowerDiff`: the derivation sends `t₁ = log x` to `1/x`. -/
theorem logTheta_deriv_eq_oneOverX :
    CField.isZero (CField.sub (@CDiffField.cderiv _ _ logTowerDiff logTheta) lvl2OneOverX)
      = true := by native_decide

/-- The diagonal multiplier `ℓ = ρ'/(2ρ) = (1/x)/(2·log x) ∈ ℚ(x)(log x)` for `D(y) = ℓ·y` at
`logTowerDiff`. -/
def logRadLogDer : Lvl2 := @logDerRadicand _ _ logTowerDiff 2 logRadicandT

/-- `y·y = log x`: the square of `y = √(log x)` reduces via the `y² → ρ` fold to `ρ = log x`. -/
theorem logRadGen_sq_eq_radicand :
    radIsZero (radSub (radMul 2 logRadicandT (radGen : RadElem Lvl2) radGen) [logRadicandT])
      = true := by native_decide

/-- The integrand `1/(x√(log x)) = (1/x)/y` as the pure-`y` `RadElem` `[0, (1/x)/(log x)]` over ℚ(x)(log x). -/
def logIntegrand : RadElem Lvl2 :=
  [CField.zero, CField.div lvl2OneOverX logRadicandT]

/-- The antiderivative `2√(log x) = 2y` as the `RadElem` `[0, 2]` over ℚ(x)(log x). -/
def logAntideriv : RadElem Lvl2 :=
  [CField.zero, CField.add CField.one CField.one]

/-- `∫ dx/(x√(log x)) = 2√(log x)`: `radDeriv` of `2y = [0, 2]` equals the integrand
`(1/x)/y = [0, (1/x)/(log x)]` over the logarithmic tower. -/
theorem logIntegral_eq :
    radIsZero (radSub (@radDeriv _ _ logTowerDiff 2 logRadicandT logAntideriv) logIntegrand)
      = true := by native_decide

/-! ### The generic rational-part driver over a tower base

The multi-case rational-part drivers (`radIntegrateCase2Wf` / `radIntegrateRationalWf`) instantiate at
`α = QFunNZG ℚ ≅ ℚ(x)`, giving the stacked extension `(ℚ(x)(t₁))[y]/(y² − ρ)`. Example: radicand
`ρ = θ³ − θ`, `W = θ`, integrand `1/(θ²·√(θ³−θ))`, validated through `radDeriv 2` at level 2. -/

open CPolyG

/-- Radicand `ρ = θ³ − θ = θ(θ−1)(θ+1) ∈ ℚ(x)[θ]` (`y² = ρ`, squarefree), `[0, −1, 0, 1]`. -/
def drvRho : CPolyG (QFunNZG ℚ) := [CField.zero, qxOfNum [-1], CField.zero, qxOfNum [1]]

/-- Squarefree factor `W = θ ∈ ℚ(x)[θ]` (a branch place, `W ∣ ρ`), `[0, 1]`. -/
def drvW : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- Numerator `C₀ = 1 ∈ ℚ(x)[θ]` (integrand `1/(θ²·√(θ³−θ))`), `[1]`. -/
def drvC : CPolyG (QFunNZG ℚ) := [CField.one]

/-- The Case-2 driver run `radIntegrateCase2Wf W ρ 2 C = (Crem, vNum)` on `∫ 1/(θ²·√(θ³−θ))` over
`α = ℚ(x)`, returning the `k = 1` residual and the rational-part numerator over `W² = θ²`. -/
def drvRun : CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ) := radIntegrateCase2Wf drvW drvRho 2 drvC

/-- The radicand `ρ = θ³ − θ` lifted to a level-2 scalar `ρ ∈ ℚ(x)(t₁) = Lvl2`. -/
def drvRhoLvl2 : Lvl2 := lvl2OfNum drvRho

/-- The common-denominator power `W² = θ²` over `ℚ(x)[θ]`, `cpowG W 2`. -/
def drvW2 : CPolyG (QFunNZG ℚ) := cpowG drvW 2

/-- The rational part `v = vNum/(W²·y)` lifted to `RadElem Lvl2` as `[0, vNum/(W²·ρ)]`. -/
def drvVlift : RadElem Lvl2 :=
  [CField.zero, CField.div (lvl2OfNum drvRun.2) (lvl2OfNum (cmulG drvW2 drvRho))]

/-- The integrand's rational part `C₀/(W²y) − Crem/(Wy)` lifted to `RadElem Lvl2`. -/
def drvRatLift : RadElem Lvl2 :=
  [CField.zero,
    CField.sub (CField.div (lvl2OfNum drvC) (lvl2OfNum (cmulG drvW2 drvRho)))
      (CField.div (lvl2OfNum drvRun.1) (lvl2OfNum (cmulG drvW drvRho)))]

/-- The Case-2 driver integrates over the tower base: `radDeriv 2` of the rational part `v = vNum/(θ²√ρ)`
equals `1/(θ²√ρ) − Crem/(θ√ρ)`, the rational part of `1/(θ²·√(θ³−θ))`, at level 2. -/
theorem drvDriver_integrates :
    radIsZero (radSub (radDeriv 2 drvRhoLvl2 drvVlift) drvRatLift) = true := by native_decide

/-- Full-driver denominator `B = θ² ∈ ℚ(x)[θ]`, `[0, 0, 1]`. -/
def drvB : CPolyG (QFunNZG ℚ) := [CField.zero, CField.zero, CField.one]

/-- The full multi-case driver run `radIntegrateRationalWf ρ R B` on `∫ 1/(θ²·√(θ³−θ))` over `α = ℚ(x)`:
squarefree-decomposes `B = θ²`, classifies `θ` as a `W`-factor, dispatches to Case-2. Returns one
per-factor record. -/
def drvFullRun :
    List (Bool × CPolyG (QFunNZG ℚ) × ℕ × CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ)) :=
  radIntegrateRationalWf drvRho drvC drvB

/-- The full multi-case driver computes over the tower base, producing one per-factor record. -/
theorem drvFullRun_length : drvFullRun.length = 1 := by native_decide

/-! ### `#print axioms` — the over-tower results -/

-- Exponential tower base: `t₁' = t₁`, radicand `ρ = eˣ+1`:
#print axioms expTheta_deriv_eq_self
#print axioms expRadGen_sq_eq_radicand
#print axioms expRadDeriv_radGen_eq

-- Exponential tower integral: `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` over ℚ(x)(eˣ).
#print axioms expIntegral_eq

-- Logarithmic tower integral: `t₁' = 1/x`, `∫ dx/(x√(log x)) = 2√(log x)` over ℚ(x)(log x).
#print axioms logTheta_deriv_eq_oneOverX
#print axioms logIntegral_eq

-- Generic rational-part driver over the tower base ℚ(x): the run and its derivative identity.
#print axioms drvDriver_integrates
#print axioms drvFullRun_length

end DeepWiki.SymbolicIntegration
