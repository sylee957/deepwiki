import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension
import DeepWiki.ComputableAlgebra.FracLinearAlgebra
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalWellFounded
import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCore

/-! # Simple radicals over a transcendental tower

Instantiating the radical extension `RadExt` at a transcendental tower level `α = ℚ(x)(eˣ)` (or
`ℚ(x)(log x)`), so the radicand `ρ` is a genuine field element of the tower and the algebraic
arc (`radDeriv`, `radMul`) runs over the exponential/logarithmic engine. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem

/-! ### The exponential tower base `α = ℚ(x)(eˣ) = DenseFrac (DenseFrac ℚ)`

`Lvl2 = DenseFrac (DenseFrac ℚ)` is the field `ℚ(x)(t₁)`. To make `t₁ = eˣ` its `CDiffField` derivation
becomes `towerDerivCFrac [t₁]` (so `t₁' = t₁`) instead of the default `t₁' = 1`. -/

/-- The exponential monomial `θ = t₁ = eˣ ∈ ℚ(x)(t₁)` (numerator `[0, 1]`, denominator `[1]`). -/
def expTheta : Lvl2 := CFrac.ofPoly [(CCommRing.zero : DenseFrac ℚ), CCommRing.one]

/-- The radicand `ρ = θ + 1 = eˣ + 1 ∈ ℚ(x)(t₁)` (numerator `[1, 1]`), the element with `y² = ρ`. -/
def expRadicand : Lvl2 := CFrac.ofPoly [(CCommRing.one : DenseFrac ℚ), CCommRing.one]

/-- The new-monomial derivative `Dt₁ = t₁ = [0, 1] ∈ DensePoly (DenseFrac ℚ)` making `t₁` exponential
(`t₁' = t₁`), fed to `towerDerivCFrac`. -/
def expDt1 : DensePoly (DenseFrac ℚ) := [(CCommRing.zero : DenseFrac ℚ), CCommRing.one]

/-- The exponential `CDiffField Lvl2` instance `cderiv := towerDerivCFrac [t₁]` (so `t₁' = t₁`, `t₁ = eˣ`).
A local `def` passed to the radical ops via `@`, leaving the default `t₁' = 1` derivation untouched. -/
@[reducible] def expTowerDiff : CDiffField Lvl2 where
  cderiv := CFrac.towerDerivCFrac expDt1

/-- `D(t₁) = t₁` under `expTowerDiff`: the derivation sends `t₁` to itself. -/
theorem expTheta_deriv_eq_self :
    CCommRing.isZero (CField.sub (@CDiffField.cderiv _ _ expTowerDiff expTheta) expTheta)
      = true := by native_decide

/-- `D(t₁+1) = t₁`: the radicand derivative `ρ' = (t₁+1)' = t₁`, the numerator `ρ'` of `y' = ρ'/(2y)`. -/
theorem expRadicand_deriv_eq_theta :
    CCommRing.isZero (CField.sub (@CDiffField.cderiv _ _ expTowerDiff expRadicand) expTheta)
      = true := by native_decide

/-! ### The radical `y² = eˣ+1` over the exponential tower

Over `α = ℚ(x)(eˣ)` with `n = 2`, `ρ = eˣ+1`: the defining relation `y·y = ρ` and the diagonal
derivation `D(y) = (ρ'/(2ρ))·y = (θ/(2(θ+1)))·y`. -/

/-- The diagonal multiplier `ℓ = ρ'/(2ρ) = θ/(2(θ+1)) ∈ ℚ(x)(eˣ)` for `D(y) = ℓ·y` at `expTowerDiff`. -/
def expRadLogDer : Lvl2 := @logDerRadicand _ _ expTowerDiff 2 expRadicand

/-- `y·y = eˣ+1`: the square of `y = √(eˣ+1)` reduces via the `y² → ρ` fold to `ρ = eˣ+1`. -/
theorem expRadGen_sq_eq_radicand :
    DensePoly.cisZero (DensePoly.csub (radMul 2 expRadicand (radGen : RadElem Lvl2) radGen) [expRadicand])
      = true := by native_decide

/-- `D(y) = (θ/(2(θ+1)))·y`: the diagonal radical derivation of `y = √(eˣ+1)` with the exponential
base derivation is `ℓ·y`, `ℓ = ρ'/(2ρ)`. -/
theorem expRadDeriv_radGen_eq :
    DensePoly.cisZero (DensePoly.csub (@radDeriv _ _ expTowerDiff 2 expRadicand (radGen : RadElem Lvl2))
        [CCommRing.zero, expRadLogDer]) = true := by native_decide

/-! ### `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` over ℚ(x)(eˣ)

Integrand `eˣ/√(eˣ+1) = θ/y = [0, θ/(θ+1)]`, antiderivative `2√(eˣ+1) = 2y = [0, 2]`, validated
through `radDeriv [0, 2] = integrand`. -/

/-- The integrand `eˣ/√(eˣ+1) = θ/y` as the pure-`y` `RadElem` `[0, θ/(θ+1)]` over ℚ(x)(eˣ). -/
def expIntegrand : RadElem Lvl2 :=
  [CCommRing.zero, CField.div expTheta expRadicand]

/-- The antiderivative `2√(eˣ+1) = 2y` as the `RadElem` `[0, 2]` over ℚ(x)(eˣ). -/
def expAntideriv : RadElem Lvl2 :=
  [CCommRing.zero, CCommRing.add CCommRing.one CCommRing.one]

/-- `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)`: `radDeriv` of the antiderivative `2y = [0, 2]` equals the integrand
`θ/y = [0, θ/(θ+1)]` over the transcendental tower. -/
theorem expIntegral_eq :
    DensePoly.cisZero (DensePoly.csub (@radDeriv _ _ expTowerDiff 2 expRadicand expAntideriv) expIntegrand)
      = true := by native_decide

/-! ### The `log` companion: `∫ dx/(x√(log x)) = 2√(log x)` over ℚ(x)(log x)

The same arc with a logarithmic monomial `θ = log x` (`θ' = 1/x`), radicand `ρ = log x`. -/

/-- The level-2 element `1/x ∈ ℚ(x) ⊂ ℚ(x)(log x)` as a `Lvl2` value (numerator `[1/x]`, denominator `[1]`). -/
def lvl2OneOverX : Lvl2 :=
  CFrac.ofPoly [CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)]

/-- The logarithmic monomial `θ = t₁ = log x ∈ ℚ(x)(log x)` (numerator `[0, 1]`, denominator `[1]`). -/
def logTheta : Lvl2 := CFrac.ofPoly [(CCommRing.zero : DenseFrac ℚ), CCommRing.one]

/-- The radicand `ρ = θ = log x ∈ ℚ(x)(log x)` (`y² = log x`), numerator `[0, 1]`, denominator `[1]`. -/
def logRadicandT : Lvl2 := CFrac.ofPoly [(CCommRing.zero : DenseFrac ℚ), CCommRing.one]

/-- The new-monomial derivative `Dt₁ = θ' = 1/x ∈ DensePoly (DenseFrac ℚ)` making `t₁` logarithmic (`t₁' = 1/x`). -/
def logDt1 : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)]

/-- The logarithmic `CDiffField Lvl2` instance `cderiv := towerDerivCFrac [1/x]` (so `t₁' = 1/x`,
`t₁ = log x`). A local `def` supplied via `@`. -/
@[reducible] def logTowerDiff : CDiffField Lvl2 where
  cderiv := CFrac.towerDerivCFrac logDt1

/-- `D(t₁) = 1/x` under `logTowerDiff`: the derivation sends `t₁ = log x` to `1/x`. -/
theorem logTheta_deriv_eq_oneOverX :
    CCommRing.isZero (CField.sub (@CDiffField.cderiv _ _ logTowerDiff logTheta) lvl2OneOverX)
      = true := by native_decide

/-- The diagonal multiplier `ℓ = ρ'/(2ρ) = (1/x)/(2·log x) ∈ ℚ(x)(log x)` for `D(y) = ℓ·y` at
`logTowerDiff`. -/
def logRadLogDer : Lvl2 := @logDerRadicand _ _ logTowerDiff 2 logRadicandT

/-- `y·y = log x`: the square of `y = √(log x)` reduces via the `y² → ρ` fold to `ρ = log x`. -/
theorem logRadGen_sq_eq_radicand :
    DensePoly.cisZero (DensePoly.csub (radMul 2 logRadicandT (radGen : RadElem Lvl2) radGen) [logRadicandT])
      = true := by native_decide

/-- The integrand `1/(x√(log x)) = (1/x)/y` as the pure-`y` `RadElem` `[0, (1/x)/(log x)]` over ℚ(x)(log x). -/
def logIntegrand : RadElem Lvl2 :=
  [CCommRing.zero, CField.div lvl2OneOverX logRadicandT]

/-- The antiderivative `2√(log x) = 2y` as the `RadElem` `[0, 2]` over ℚ(x)(log x). -/
def logAntideriv : RadElem Lvl2 :=
  [CCommRing.zero, CCommRing.add CCommRing.one CCommRing.one]

/-- `∫ dx/(x√(log x)) = 2√(log x)`: `radDeriv` of `2y = [0, 2]` equals the integrand
`(1/x)/y = [0, (1/x)/(log x)]` over the logarithmic tower. -/
theorem logIntegral_eq :
    DensePoly.cisZero (DensePoly.csub (@radDeriv _ _ logTowerDiff 2 logRadicandT logAntideriv) logIntegrand)
      = true := by native_decide

/-! ### The generic rational-part driver over a tower base

The multi-case rational-part drivers (`radIntegrateCase2Wf` / `radIntegrateRationalWf`) instantiate at
`α = DenseFrac ℚ ≅ ℚ(x)`, giving the stacked extension `(ℚ(x)(t₁))[y]/(y² − ρ)`. Example: radicand
`ρ = θ³ − θ`, `W = θ`, integrand `1/(θ²·√(θ³−θ))`, validated through `radDeriv 2` at level 2. -/

open DensePoly

/-- Radicand `ρ = θ³ − θ = θ(θ−1)(θ+1) ∈ ℚ(x)[θ]` (`y² = ρ`, squarefree), `[0, −1, 0, 1]`. -/
def drvRho : DensePoly (DenseFrac ℚ) := [CCommRing.zero, CFrac.ofPoly [-1], CCommRing.zero, CFrac.ofPoly [1]]

/-- Squarefree factor `W = θ ∈ ℚ(x)[θ]` (a branch place, `W ∣ ρ`), `[0, 1]`. -/
def drvW : DensePoly (DenseFrac ℚ) := [CCommRing.zero, CCommRing.one]

/-- Numerator `C₀ = 1 ∈ ℚ(x)[θ]` (integrand `1/(θ²·√(θ³−θ))`), `[1]`. -/
def drvC : DensePoly (DenseFrac ℚ) := [CCommRing.one]

/-- The Case-2 driver run `radIntegrateCase2Wf W ρ 2 C = (Crem, vNum)` on `∫ 1/(θ²·√(θ³−θ))` over
`α = ℚ(x)`, returning the `k = 1` residual and the rational-part numerator over `W² = θ²`. -/
def drvRun : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ) := radIntegrateCase2Wf drvW drvRho 2 drvC

/-- The radicand `ρ = θ³ − θ` lifted to a level-2 scalar `ρ ∈ ℚ(x)(t₁) = Lvl2`. -/
def drvRhoLvl2 : Lvl2 := CFrac.ofPoly drvRho

/-- The common-denominator power `W² = θ²` over `ℚ(x)[θ]`, `cpow W 2`. -/
def drvW2 : DensePoly (DenseFrac ℚ) := cpow drvW 2

/-- The rational part `v = vNum/(W²·y)` lifted to `RadElem Lvl2` as `[0, vNum/(W²·ρ)]`. -/
def drvVlift : RadElem Lvl2 :=
  [CCommRing.zero, CField.div (CFrac.ofPoly drvRun.2) (CFrac.ofPoly (cmul drvW2 drvRho))]

/-- The integrand's rational part `C₀/(W²y) − Crem/(Wy)` lifted to `RadElem Lvl2`. -/
def drvRatLift : RadElem Lvl2 :=
  [CCommRing.zero,
    CField.sub (CField.div (CFrac.ofPoly drvC) (CFrac.ofPoly (cmul drvW2 drvRho)))
      (CField.div (CFrac.ofPoly drvRun.1) (CFrac.ofPoly (cmul drvW drvRho)))]

/-- The Case-2 driver integrates over the tower base: `radDeriv 2` of the rational part `v = vNum/(θ²√ρ)`
equals `1/(θ²√ρ) − Crem/(θ√ρ)`, the rational part of `1/(θ²·√(θ³−θ))`, at level 2. -/
theorem drvDriver_integrates :
    DensePoly.cisZero (DensePoly.csub (radDeriv 2 drvRhoLvl2 drvVlift) drvRatLift) = true := by native_decide

/-- Full-driver denominator `B = θ² ∈ ℚ(x)[θ]`, `[0, 0, 1]`. -/
def drvB : DensePoly (DenseFrac ℚ) := [CCommRing.zero, CCommRing.zero, CCommRing.one]

/-- The full multi-case driver run `radIntegrateRationalWf ρ R B` on `∫ 1/(θ²·√(θ³−θ))` over `α = ℚ(x)`:
squarefree-decomposes `B = θ²`, classifies `θ` as a `W`-factor, dispatches to Case-2. Returns one
per-factor record. -/
def drvFullRun :
    List (Bool × DensePoly (DenseFrac ℚ) × ℕ × DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)) :=
  radIntegrateRationalWf drvRho drvC drvB

/-- The full multi-case driver computes over the tower base, producing one per-factor record. -/
theorem drvFullRun_length : drvFullRun.length = 1 := by native_decide

end DeepWiki.SymbolicIntegration
