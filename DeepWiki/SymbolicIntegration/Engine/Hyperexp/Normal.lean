import DeepWiki.SymbolicIntegration.Engine.Hyperexp.Special
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.NormalCore
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.ExampleData

/-! # The hyperexponential normal part via residual feedback

Worked examples of the residual-feedback hyperexponential integrators `cIntegrateHyperexpNormal` /
`cIntegrateHyperexpFull`, e.g. `∫ 1/(exp x − 1) = log(exp x − 1) − x`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration


/-! ### Examples: `∫ 1/(exp x − 1) dx = log(exp x − 1) − x`

Over `ℚ(x)[t]` (`t = exp x`, `Dt = η·t`, `η = 1`), `f = 1/(t−1)` has log part `log(t−1)` overshooting by
`R = 1`; the feedback subtracts `∫R = x`. -/

open DensePoly

/-- Hyperexponential monomial derivative `Dt = η·t = [0, 1]` over `DensePoly Lvl1 = ℚ(x)[t]` (`t = exp x`,
`η = 1`). -/
def nHyperexpDt : DensePoly Lvl1 := [CCommRing.zero, CCommRing.one]

/-- The integrand numerator `a = 1` over `DensePoly Lvl1 = ℚ(x)[t]` for `f = 1/(t−1) = 1/(exp x − 1)`. -/
def nNormInvA : DensePoly Lvl1 := [CCommRing.one]

/-- The integrand denominator `d = t − 1 = [−1, 1]` over `DensePoly Lvl1 = ℚ(x)[t]` for
`f = 1/(t−1) = 1/(exp x − 1)` (a normal factor: `gcd(t−1, Dt) = 1`). -/
def nNormInvD : DensePoly Lvl1 := [CCommRing.neg CCommRing.one, CCommRing.one]

/-- Residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for `1/(exp x − 1)` (genuine residue
`1`). -/
def nNormInvCands : List Lvl1 := [CCommRing.zero, CCommRing.one, CCommRing.neg CCommRing.one]

/-- The hyperexponential residual `R = 1` on `f = 1/(exp x − 1)`: `cHyperexpResidual` of the reduced
capstone's logs equals `1`. -/
theorem nNormInv_residual_eq_one :
    CCommRing.isZero (CField.sub
      (cHyperexpResidual (cExpEta nHyperexpDt)
        (cIntegrateReduced nHyperexpDt nNormInvA nNormInvD nNormInvCands).logs)
      (CCommRing.one : Lvl1)) = true := by native_decide

/-- The base residual integral `∫R = ∫1 = x`: `crischDESolve 0 1` over `ℚ(x)` recovers `y = x`. -/
theorem nNormInv_baseIntegral_eq_x :
    (match CRischField.crischDESolve (CCommRing.zero : Lvl1) (CCommRing.one : Lvl1) with
      | some y => CCommRing.isZero (CField.sub y nLvl1X)
      | none => false) = true := by native_decide

/-- The plain reduced driver overshoots on `f = 1/(exp x − 1)`: `cIntegrateReduced` returns `log(t−1)`,
which overshoots by `R = 1`, so `checkIdentity = false`. -/
theorem nNormInv_reduced_overshoots :
    CPoly.checkIdentity nHyperexpDt
      (cIntegrateReduced nHyperexpDt nNormInvA nNormInvD nNormInvCands)
      nNormInvA nNormInvD = false := by native_decide

/-- The residual-feedback driver lands `∫ 1/(exp x − 1) = log(exp x − 1) − x` with `D(∫f) = f`:
`cIntegrateHyperexpNormal` returns `some res` satisfying `checkIdentity`. -/
theorem nNormInv_landsNormalPart :
    (match DensePoly.cIntegrateHyperexpNormal nHyperexpDt nNormInvA nNormInvD nNormInvCands with
      | some res => CPoly.checkIdentity nHyperexpDt res nNormInvA nNormInvD
      | none => false) = true := by native_decide

/-- The driver's result on `f = 1/(exp x − 1)` is exactly `log(t−1) − x`: rational part `−x` and a single
log with argument `t − 1`. Pins the shape, not just the derivative identity. -/
theorem nNormInv_result_is_logTMinus1_minus_x :
    (match DensePoly.cIntegrateHyperexpNormal nHyperexpDt nNormInvA nNormInvD nNormInvCands with
      | some res =>
        DensePoly.cisZero (DensePoly.csub res.rational.1 [CCommRing.neg nLvl1X])
          && res.logs.length == 1
          && (res.logs.all (fun cv => DensePoly.cisZero (DensePoly.csub cv.2 nNormInvD)))
      | none => false) = true := by native_decide

/-! ### The special + normal mix: `∫ (1/exp + 1/(exp−1)) = −1/exp + log(exp−1) − x`

The combined driver on `f = 1/t + 1/(t−1) = (2t−1)/(t²−t)` over `ℚ(x)[t]` (`t = exp`, `η = 1`): the special
part lands `−1/t`, the normal part `log(t−1) − x`, so `∫f = −1/t + log(t−1) − x`, satisfying
`D(∫f) = f`. -/

/-- Integrand numerator `a = 2t − 1` for `f = (2t−1)/(t²−t) = 1/t + 1/(t−1)` over `DensePoly Lvl1`. -/
def nSpecNormA : DensePoly Lvl1 := [CCommRing.neg CCommRing.one, CCommRing.add CCommRing.one CCommRing.one]

/-- Integrand denominator `d = t² − t = t(t−1)` for `f = (2t−1)/(t²−t)` over `DensePoly Lvl1` (special factor
`t`, normal factor `t−1`). -/
def nSpecNormD : DensePoly Lvl1 := [CCommRing.zero, CCommRing.neg CCommRing.one, CCommRing.one]

/-- Residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for the special+normal mix. -/
def nSpecNormCands : List Lvl1 := [CCommRing.zero, CCommRing.one, CCommRing.neg CCommRing.one]

/-- The special-part-only driver still overshoots on the special+normal mix: `cIntegrateHyperexp` returns
`some` but its normal log part overshoots by `R = 1`, so `checkIdentity = false`. -/
theorem nSpecNorm_specialOnly_overshoots :
    (match DensePoly.cIntegrateHyperexp nHyperexpDt nSpecNormA nSpecNormD nSpecNormCands with
      | some res => CPoly.checkIdentity nHyperexpDt res nSpecNormA nSpecNormD
      | none => false) = false := by native_decide

/-- The full driver lands `∫ (1/exp + 1/(exp−1)) = −1/exp + log(exp−1) − x` with `D(∫f) = f`:
`cIntegrateHyperexpFull` integrates the special part to `−1/t` and the normal part to `log(t−1) − x`,
returning `some res` satisfying `checkIdentity`. -/
theorem nSpecNorm_full_lands :
    (match DensePoly.cIntegrateHyperexpFull nHyperexpDt nSpecNormA nSpecNormD nSpecNormCands with
      | some res => CPoly.checkIdentity nHyperexpDt res nSpecNormA nSpecNormD
      | none => false) = true := by native_decide

/-! ### A non-constant base residual: `∫ 2x/(exp(x²) − 1) = log(exp(x²) − 1) − x²`

Take `t = exp(x²)`, so `Dt = η·t` with `η = 2x` non-constant, over `ℚ(x)[t]`, and `fₙ = 2x/(t−1)`. The
residue is the constant `1`, the log part overshoots by `R = 2x` (non-constant), and the feedback
integrates `∫R = x²`, landing `log(t−1) − x²`. -/

/-- Hyperexponential monomial derivative `Dt = η·t = [0, 2x]` over `DensePoly Lvl1 = ℚ(x)[t]`
(`t = exp(x²)`, non-constant `η = 2x ∈ ℚ(x)`). -/
def nVarDt : DensePoly Lvl1 := [CCommRing.zero, nLvl1TwoX]

/-- Integrand numerator `a = 2x` over `DensePoly Lvl1` for `f = 2x/(t−1) = 2x/(exp(x²) − 1)`, so the residue
`2x/(η·1) = 1` is constant. -/
def nVarNormA : DensePoly Lvl1 := [nLvl1TwoX]

/-- Integrand denominator `d = t − 1` over `DensePoly Lvl1` for `f = 2x/(t−1)` (normal: `gcd(t−1, Dt) =
1`). -/
def nVarNormD : DensePoly Lvl1 := [CCommRing.neg CCommRing.one, CCommRing.one]

/-- Residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for `2x/(exp(x²) − 1)` (residue `1`). -/
def nVarNormCands : List Lvl1 := [CCommRing.zero, CCommRing.one, CCommRing.neg CCommRing.one]

/-- The non-constant base residual `R = 2x` on `f = 2x/(exp(x²) − 1)`: `cHyperexpResidual` equals `2x`, a
non-constant rational function of `x`. -/
theorem nVarNorm_residual_eq_twoX :
    CCommRing.isZero (CField.sub
      (cHyperexpResidual (cExpEta nVarDt)
        (cIntegrateReduced nVarDt nVarNormA nVarNormD nVarNormCands).logs)
      nLvl1TwoX) = true := by native_decide

/-- The non-constant base residual integral `∫R = ∫2x = x²`: `crischDESolve 0 (2x)` over `ℚ(x)` recovers
`y = x²`. -/
theorem nVarNorm_baseIntegral_eq_xSq :
    (match CRischField.crischDESolve (CCommRing.zero : Lvl1) nLvl1TwoX with
      | some y => CCommRing.isZero (CField.sub y nLvl1XSq)
      | none => false) = true := by native_decide

/-- The driver lands `∫ 2x/(exp(x²) − 1) = log(exp(x²) − 1) − x²` with `D(∫f) = f`:
`cIntegrateHyperexpNormal` reads the non-constant residual `R = 2x`, integrates `∫R = x²`, and returns
`log(t−1) − x²` (rational part `−x²`, one log) satisfying `checkIdentity`. -/
theorem nVarNorm_landsNormalPart :
    (match DensePoly.cIntegrateHyperexpNormal nVarDt nVarNormA nVarNormD nVarNormCands with
      | some res =>
        CPoly.checkIdentity nVarDt res nVarNormA nVarNormD
          && DensePoly.cisZero (DensePoly.csub res.rational.1 [CCommRing.neg nLvl1XSq])
          && res.logs.length == 1
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
