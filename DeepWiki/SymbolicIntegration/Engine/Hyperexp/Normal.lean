import DeepWiki.SymbolicIntegration.Engine.Hyperexp.Special
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.NormalCore
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.ExampleData

/-! # The hyperexponential normal part via residual feedback

Worked examples of the residual-feedback hyperexponential integrators `cIntegrateHyperexpNormalGWf` /
`cIntegrateHyperexpFullGWf`, e.g. `∫ 1/(exp x − 1) = log(exp x − 1) − x`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ### Examples: `∫ 1/(exp x − 1) dx = log(exp x − 1) − x`

Over `ℚ(x)[t]` (`t = exp x`, `Dt = η·t`, `η = 1`), `f = 1/(t−1)` has log part `log(t−1)` overshooting by
`R = 1`; the feedback subtracts `∫R = x`. -/

open CPolyG

/-- Hyperexponential monomial derivative `Dt = η·t = [0, 1]` over `CPolyG NLvl1 = ℚ(x)[t]` (`t = exp x`,
`η = 1`). -/
def nHyperexpDt : CPolyG NLvl1 := [CField.zero, CField.one]

/-- The integrand numerator `a = 1` over `CPolyG NLvl1 = ℚ(x)[t]` for `f = 1/(t−1) = 1/(exp x − 1)`. -/
def nNormInvA : CPolyG NLvl1 := [CField.one]

/-- The integrand denominator `d = t − 1 = [−1, 1]` over `CPolyG NLvl1 = ℚ(x)[t]` for
`f = 1/(t−1) = 1/(exp x − 1)` (a normal factor: `gcd(t−1, Dt) = 1`). -/
def nNormInvD : CPolyG NLvl1 := [CField.neg CField.one, CField.one]

/-- Residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for `1/(exp x − 1)` (genuine residue
`1`). -/
def nNormInvCands : List NLvl1 := [CField.zero, CField.one, CField.neg CField.one]

/-- The hyperexponential residual `R = 1` on `f = 1/(exp x − 1)`: `cHyperexpResidualG` of the reduced
capstone's logs equals `1`. -/
theorem nNormInv_residual_eq_one :
    CField.isZero (CField.sub
      (cHyperexpResidualG (cExpEtaG nHyperexpDt)
        (cIntegrateReducedGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands).logs)
      (CField.one : NLvl1)) = true := by native_decide

/-- The base residual integral `∫R = ∫1 = x`: `crischDESolve 0 1` over `ℚ(x)` recovers `y = x`. -/
theorem nNormInv_baseIntegral_eq_x :
    (match CRischField.crischDESolve (CField.zero : NLvl1) (CField.one : NLvl1) with
      | some y => CField.isZero (CField.sub y nLvl1X)
      | none => false) = true := by native_decide

/-- The plain reduced driver overshoots on `f = 1/(exp x − 1)`: `cIntegrateReducedGWf` returns `log(t−1)`,
which overshoots by `R = 1`, so `checkIdentityG = false`. -/
theorem nNormInv_reduced_overshoots :
    CPolyG.checkIdentityG nHyperexpDt
      (cIntegrateReducedGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands)
      nNormInvA nNormInvD = false := by native_decide

/-- The residual-feedback driver lands `∫ 1/(exp x − 1) = log(exp x − 1) − x` with `D(∫f) = f`:
`cIntegrateHyperexpNormalGWf` returns `some res` satisfying `checkIdentityG`. -/
theorem nNormInv_landsNormalPart :
    (match CPolyG.cIntegrateHyperexpNormalGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands with
      | some res => CPolyG.checkIdentityG nHyperexpDt res nNormInvA nNormInvD
      | none => false) = true := by native_decide

/-- The driver's result on `f = 1/(exp x − 1)` is exactly `log(t−1) − x`: rational part `−x` and a single
log with argument `t − 1`. Pins the shape, not just the derivative identity. -/
theorem nNormInv_result_is_logTMinus1_minus_x :
    (match CPolyG.cIntegrateHyperexpNormalGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands with
      | some res =>
        CPolyG.cisZeroG (CPolyG.csubG res.rational.1 [CField.neg nLvl1X])
          && res.logs.length == 1
          && (res.logs.all (fun cv => CPolyG.cisZeroG (CPolyG.csubG cv.2 nNormInvD)))
      | none => false) = true := by native_decide

/-! ### The special + normal mix: `∫ (1/exp + 1/(exp−1)) = −1/exp + log(exp−1) − x`

The combined driver on `f = 1/t + 1/(t−1) = (2t−1)/(t²−t)` over `ℚ(x)[t]` (`t = exp`, `η = 1`): the special
part lands `−1/t`, the normal part `log(t−1) − x`, so `∫f = −1/t + log(t−1) − x`, satisfying
`D(∫f) = f`. -/

/-- Integrand numerator `a = 2t − 1` for `f = (2t−1)/(t²−t) = 1/t + 1/(t−1)` over `CPolyG NLvl1`. -/
def nSpecNormA : CPolyG NLvl1 := [CField.neg CField.one, CField.add CField.one CField.one]

/-- Integrand denominator `d = t² − t = t(t−1)` for `f = (2t−1)/(t²−t)` over `CPolyG NLvl1` (special factor
`t`, normal factor `t−1`). -/
def nSpecNormD : CPolyG NLvl1 := [CField.zero, CField.neg CField.one, CField.one]

/-- Residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for the special+normal mix. -/
def nSpecNormCands : List NLvl1 := [CField.zero, CField.one, CField.neg CField.one]

/-- The special-part-only driver still overshoots on the special+normal mix: `cIntegrateHyperexpG` returns
`some` but its normal log part overshoots by `R = 1`, so `checkIdentityG = false`. -/
theorem nSpecNorm_specialOnly_overshoots :
    (match CPolyG.cIntegrateHyperexpG nHyperexpDt nSpecNormA nSpecNormD nSpecNormCands with
      | some res => CPolyG.checkIdentityG nHyperexpDt res nSpecNormA nSpecNormD
      | none => false) = false := by native_decide

/-- The full driver lands `∫ (1/exp + 1/(exp−1)) = −1/exp + log(exp−1) − x` with `D(∫f) = f`:
`cIntegrateHyperexpFullGWf` integrates the special part to `−1/t` and the normal part to `log(t−1) − x`,
returning `some res` satisfying `checkIdentityG`. -/
theorem nSpecNorm_full_lands :
    (match CPolyG.cIntegrateHyperexpFullGWf nHyperexpDt nSpecNormA nSpecNormD nSpecNormCands with
      | some res => CPolyG.checkIdentityG nHyperexpDt res nSpecNormA nSpecNormD
      | none => false) = true := by native_decide

/-! ### A non-constant base residual: `∫ 2x/(exp(x²) − 1) = log(exp(x²) − 1) − x²`

Take `t = exp(x²)`, so `Dt = η·t` with `η = 2x` non-constant, over `ℚ(x)[t]`, and `fₙ = 2x/(t−1)`. The
residue is the constant `1`, the log part overshoots by `R = 2x` (non-constant), and the feedback
integrates `∫R = x²`, landing `log(t−1) − x²`. -/

/-- Hyperexponential monomial derivative `Dt = η·t = [0, 2x]` over `CPolyG NLvl1 = ℚ(x)[t]`
(`t = exp(x²)`, non-constant `η = 2x ∈ ℚ(x)`). -/
def nVarDt : CPolyG NLvl1 := [CField.zero, nLvl1TwoX]

/-- Integrand numerator `a = 2x` over `CPolyG NLvl1` for `f = 2x/(t−1) = 2x/(exp(x²) − 1)`, so the residue
`2x/(η·1) = 1` is constant. -/
def nVarNormA : CPolyG NLvl1 := [nLvl1TwoX]

/-- Integrand denominator `d = t − 1` over `CPolyG NLvl1` for `f = 2x/(t−1)` (normal: `gcd(t−1, Dt) =
1`). -/
def nVarNormD : CPolyG NLvl1 := [CField.neg CField.one, CField.one]

/-- Residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for `2x/(exp(x²) − 1)` (residue `1`). -/
def nVarNormCands : List NLvl1 := [CField.zero, CField.one, CField.neg CField.one]

/-- The non-constant base residual `R = 2x` on `f = 2x/(exp(x²) − 1)`: `cHyperexpResidualG` equals `2x`, a
non-constant rational function of `x`. -/
theorem nVarNorm_residual_eq_twoX :
    CField.isZero (CField.sub
      (cHyperexpResidualG (cExpEtaG nVarDt)
        (cIntegrateReducedGWf nVarDt nVarNormA nVarNormD nVarNormCands).logs)
      nLvl1TwoX) = true := by native_decide

/-- The non-constant base residual integral `∫R = ∫2x = x²`: `crischDESolve 0 (2x)` over `ℚ(x)` recovers
`y = x²`. -/
theorem nVarNorm_baseIntegral_eq_xSq :
    (match CRischField.crischDESolve (CField.zero : NLvl1) nLvl1TwoX with
      | some y => CField.isZero (CField.sub y nLvl1XSq)
      | none => false) = true := by native_decide

/-- The driver lands `∫ 2x/(exp(x²) − 1) = log(exp(x²) − 1) − x²` with `D(∫f) = f`:
`cIntegrateHyperexpNormalGWf` reads the non-constant residual `R = 2x`, integrates `∫R = x²`, and returns
`log(t−1) − x²` (rational part `−x²`, one log) satisfying `checkIdentityG`. -/
theorem nVarNorm_landsNormalPart :
    (match CPolyG.cIntegrateHyperexpNormalGWf nVarDt nVarNormA nVarNormD nVarNormCands with
      | some res =>
        CPolyG.checkIdentityG nVarDt res nVarNormA nVarNormD
          && CPolyG.cisZeroG (CPolyG.csubG res.rational.1 [CField.neg nLvl1XSq])
          && res.logs.length == 1
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
