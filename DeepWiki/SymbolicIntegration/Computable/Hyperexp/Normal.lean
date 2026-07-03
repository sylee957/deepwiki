import DeepWiki.SymbolicIntegration.Computable.Hyperexp.Special
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.NormalCore
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.ExampleData

/-! # The hyperexponential normal part via residual feedback

`native_decide`-validated examples of the fuel-free residual-feedback hyperexponential integrators
`cIntegrateHyperexpNormalGWf` / `cIntegrateHyperexpFullGWf` (`ComputableHyperexpNormalCore`,
`∫ fₙ = ∑ᵢ cᵢ·log vᵢ − ∫R`, `R = η·∑ᵢ cᵢ` the Rothstein–Trager overshoot), such as
`∫ 1/(exp x − 1) = log(exp x − 1) − x`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ### Validation: `∫ 1/(exp x − 1) dx = log(exp x − 1) − x` (`native_decide`)

Over `ℚ(x)[t]` (`t = exp x`, `Dt = η·t`, `η = 1`), the normal integrand `f = 1/(t−1)` has
Rothstein–Trager log part `log(t−1)` overshooting by `R = 1`; the feedback subtracts `∫R = x`,
landing `log(t−1) − x` with `D(∫f) = f`. -/

open CPolyG

/-- The hyperexponential monomial derivative `Dt = η·t = [0, 1]` over `CPolyG NLvl1 = ℚ(x)[t]` (`t = exp x`,
`η = 1`): the coefficient of `t¹` is `η = 1`. -/
def nHyperexpDt : CPolyG NLvl1 := [CField.zero, CField.one]

/-- The integrand numerator `a = 1` over `CPolyG NLvl1 = ℚ(x)[t]` for `f = 1/(t−1) = 1/(exp x − 1)`. -/
def nNormInvA : CPolyG NLvl1 := [CField.one]

/-- The integrand denominator `d = t − 1 = [−1, 1]` over `CPolyG NLvl1 = ℚ(x)[t]` for
`f = 1/(t−1) = 1/(exp x − 1)` (a normal factor: `gcd(t−1, Dt) = 1`). -/
def nNormInvD : CPolyG NLvl1 := [CField.neg CField.one, CField.one]

/-- The residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for the `1/(exp x − 1)` integral
(the genuine residue is `1`). -/
def nNormInvCands : List NLvl1 := [CField.zero, CField.one, CField.neg CField.one]

/-- **The hyperexponential residual `R = 1` on `f = 1/(exp x − 1)`** (`native_decide`): for the normal part
`fₙ = 1/(t−1)` over ℚ(x)[t] (`Dt = η·t`, `η = 1`), the §5.6 Rothstein–Trager log part is `1·log(t−1)` with a
single residue `c₁ = 1`, so the §5.9 residual is `R = η·∑ᵢ cᵢ = 1·1 = 1` (`cHyperexpResidualG` of the
reduced capstone's logs), confirmed by `CField.isZero (R − 1) = true`. This is the exact overshoot
`D(log(t−1)) − fₙ = t/(t−1) − 1/(t−1) = 1` that the feedback subtracts. -/
theorem nNormInv_residual_eq_one :
    CField.isZero (CField.sub
      (cHyperexpResidualG (cExpEtaG nHyperexpDt)
        (cIntegrateReducedGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands).logs)
      (CField.one : NLvl1)) = true := by native_decide

/-- **The base residual integral `∫R = ∫1 = x`** (`native_decide`): the §5.9 feedback integrates the
residual `R = 1 ∈ ℚ(x)` as a base Risch-DE `Dy = 1` over `k = ℚ(x)` (`crischDESolve 0 1`), recovering
`y = x` — the classic base polynomial integration, recursing ℚ(x) → ℚ. Certified by `CField.isZero (y − x)
= true`. This `x` is what is subtracted from the log part to land `log(t−1) − x`. -/
theorem nNormInv_baseIntegral_eq_x :
    (match CRischField.crischDESolve (CField.zero : NLvl1) (CField.one : NLvl1) with
      | some y => CField.isZero (CField.sub y nLvl1X)
      | none => false) = true := by native_decide

/-- **The plain reduced driver overshoots on `f = 1/(exp x − 1)`** (`native_decide`, the companion): the
§5.6 reduced capstone `cIntegrateReducedG` returns `1·log(t−1)`, whose derivative `D(t−1)/(t−1) = t/(t−1)`
overshoots `fₙ = 1/(t−1)` by the hyperexponential residual `R = 1`, so the antiderivative identity
`D(res) = f` **fails** — `checkIdentityG = false`. This is exactly the §5.9 frontier the residual feedback
closes (contrast `nNormInv_landsNormalPart`). -/
theorem nNormInv_reduced_overshoots :
    CPolyG.checkIdentityG nHyperexpDt
      (cIntegrateReducedGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands)
      nNormInvA nNormInvD = false := by native_decide

/-- **★ The §5.9 driver lands `∫ 1/(exp x − 1) = log(exp x − 1) − x`, and `D(∫f) = f`** (`native_decide`,
the headline). On the hyperexponential **normal** integrand `f = 1/(t−1) = 1/(exp x − 1)` over `ℚ(x)[t]`
(`Dt = η·t`, `η = 1`) — on which the reduced `cIntegrateReducedG` overshoots by the residual `R = 1`
(`nNormInv_reduced_overshoots`) — the §5.9 driver `cIntegrateHyperexpNormalGWf` (reduced capstone + residual
`R = η·∑res = 1` + base integral `∫R = x` + subtraction) returns `some res`, and `res` satisfies the
antiderivative identity `D(res) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` (`checkIdentityG`, cleared of denominators over
ℚ(x)[t]). The returned object is `log(t−1) − x` (rational part `−x`, one log `(1, t−1)`). **This is the
deliverable: the hyperexponential normal part — built on the §5.9 residual feedback and the recursive base
integral — computes and differentiates back to `f`, completing hyperexponential integration (special §5.10
+ normal §5.9).** -/
theorem nNormInv_landsNormalPart :
    (match CPolyG.cIntegrateHyperexpNormalGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands with
      | some res => CPolyG.checkIdentityG nHyperexpDt res nNormInvA nNormInvD
      | none => false) = true := by native_decide

/-- **The §5.9 driver's result IS `log(t−1) − x`** (`native_decide`): the returned `IntegralResultG` of
`cIntegrateHyperexpNormalGWf` on `f = 1/(exp x − 1)` has rational part exactly `−x` (a single `t⁰`
coefficient `−x ∈ ℚ(x)`) and a single logarithm with argument `t − 1` — i.e. `log(t−1) − x`, the textbook
antiderivative. Pins the *shape*, not just the derivative identity. -/
theorem nNormInv_result_is_logTMinus1_minus_x :
    (match CPolyG.cIntegrateHyperexpNormalGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands with
      | some res =>
        CPolyG.cisZeroG (CPolyG.csubG res.rational.1 [CField.neg nLvl1X])
          && res.logs.length == 1
          && (res.logs.all (fun cv => CPolyG.cisZeroG (CPolyG.csubG cv.2 nNormInvD)))
      | none => false) = true := by native_decide

#print axioms nNormInv_landsNormalPart

/-! ### ★★ The special + normal mix: `∫ (1/exp + 1/(exp−1)) = −1/exp + log(exp−1) − x` (`native_decide`)

The combined §5.10 + §5.9 driver on `f = 1/t + 1/(t−1) = (2t−1)/(t²−t)` over `ℚ(x)[t]` (`t = exp`,
`Dt = η·t`, `η = 1`): the canonical split is `fₛ = 1/t` (special — `t` is the hyperexponential special
factor) and `fₙ = 1/(t−1)` (normal). The §5.10 special part lands `−1/t`; the §5.9 normal part lands
`log(t−1) − x` (residual `R = 1`, base integral `x`). So `∫f = −1/t + log(t−1) − x`. The full driver
`cIntegrateHyperexpFullGWf` routes the special part through `cIntegrateHyperexpLaurentG` and the normal part
through the §5.9 feedback, and the assembled result satisfies `D(∫f) = f` (`checkIdentityG`).

This is the **clean special + normal hyperexponential integral** that was the documented frontier in
`ComputableHyperexpSpecial` (where `cIntegrateHyperexpG` *ran* on this input but its normal log part
overshot): with the §5.9 feedback the WHOLE mix now differentiates back to `f`. -/

/-- The integrand numerator `a = 2t − 1` for `f = (2t−1)/(t²−t) = 1/t + 1/(t−1)` over `CPolyG NLvl1`. -/
def nSpecNormA : CPolyG NLvl1 := [CField.neg CField.one, CField.add CField.one CField.one]

/-- The integrand denominator `d = t² − t = t(t−1)` for `f = (2t−1)/(t²−t)` over `CPolyG NLvl1` (split:
special factor `t`, normal factor `t−1`). -/
def nSpecNormD : CPolyG NLvl1 := [CField.zero, CField.neg CField.one, CField.one]

/-- The residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for the special+normal mix. -/
def nSpecNormCands : List NLvl1 := [CField.zero, CField.one, CField.neg CField.one]

/-- **The §5.10-only driver still overshoots on the special+normal mix** (`native_decide`, the contrast):
the §5.10 driver `cIntegrateHyperexpG` (special part correct, normal part via the bare `cIntegrateReducedG`)
runs on `f = 1/t + 1/(t−1)` over ℚ(x)[t] and returns `some`, but its normal log part `log(t−1)` overshoots
`1/(t−1)` by the §5.9 residual `R = 1`, so the full-`f` antiderivative identity `D(res) = f` **fails**
(`checkIdentityG = false`) — exactly the gap the §5.9 feedback (`cIntegrateHyperexpFullGWf`) closes. -/
theorem nSpecNorm_specialOnly_overshoots :
    (match CPolyG.cIntegrateHyperexpG nHyperexpDt nSpecNormA nSpecNormD nSpecNormCands with
      | some res => CPolyG.checkIdentityG nHyperexpDt res nSpecNormA nSpecNormD
      | none => false) = false := by native_decide

/-- **★★ The full §5.10 + §5.9 driver lands `∫ (1/exp + 1/(exp−1)) = −1/exp + log(exp−1) − x`, and
`D(∫f) = f`** (`native_decide`, the stretch). On `f = 1/t + 1/(t−1)` over `ℚ(x)[t]` (`t = exp`, `Dt = η·t`,
`η = 1`) — a **special part `1/t` AND a normal part `1/(t−1)`** — the combined driver
`cIntegrateHyperexpFullGWf` integrates the special part by §5.10 Laurent (`−1/t`) and the normal part by the
§5.9 residual feedback (`log(t−1) − x`), recombining to `−1/t + log(t−1) − x`, and `res` satisfies the
antiderivative identity `D(res) = f` (`checkIdentityG`, cleared of denominators over ℚ(x)[t]). The whole
special-AND-normal hyperexponential integral computes and differentiates back to `f` — the clean mix that
was the §5.9 frontier in `ComputableHyperexpSpecial`. -/
theorem nSpecNorm_full_lands :
    (match CPolyG.cIntegrateHyperexpFullGWf nHyperexpDt nSpecNormA nSpecNormD nSpecNormCands with
      | some res => CPolyG.checkIdentityG nHyperexpDt res nSpecNormA nSpecNormD
      | none => false) = true := by native_decide

#print axioms nSpecNorm_full_lands

/-! ### ★★ A genuinely NON-CONSTANT base residual: `∫ 2x/(exp(x²) − 1) = log(exp(x²) − 1) − x²` (`native_decide`)

The headline residual `R = 1` is a `k`-constant. Here the §5.9 feedback handles a genuinely **non-constant**
base residual. Take `t = exp(x²)`, so `Dt = η·t` with `η = 2x` (non-constant in `x`), over `ℚ(x)[t]`, and
`fₙ = 2x/(t−1)`. The §5.6 residue is `A(1)/(δd)(1) = 2x/(η·1) = 2x/(2x) = 1` — a genuine δ-constant residue
(the `η` in the numerator cancels the `η` from `δd = D(t−1) = η·t`, so the residue is the *constant* `1`,
valid for the Rothstein–Trager criterion). The log part `1·log(t−1)` overshoots by `R = η·∑res = 2x·1 =
2x`, a **non-constant** rational function of `x`. The §5.9 feedback integrates the base residual `∫R = ∫2x
dx = x²` over `k = ℚ(x)` (`crischDESolve 0 (2x)` runs the §6 pipeline over ℚ[x], recursing to ℚ) and
subtracts it: `∫fₙ = log(t−1) − x²`.

This exercises the residual feedback with a **non-constant `R`** (the stretch): `R = 2x` is stored as the
reduced fraction `2x/1` (the numerator-`η` cancellation keeps the residue constant, so `R = η·1` carries no
spurious denominator — unlike the unreduced `2x/2x` of a non-δ-constant residue), so `crischDESolve` over
ℚ(x) genuinely integrates the non-constant `2x` to `x²`, and `cIntegrateHyperexpNormalGWf` lands
`log(t−1) − x²` with `D(∫f) = f`. -/

/-- The hyperexponential monomial derivative `Dt = η·t = [0, 2x]` over `CPolyG NLvl1 = ℚ(x)[t]`
(`t = exp(x²)`, `η = 2x`): the coefficient of `t¹` is the **non-constant** `η = 2x ∈ ℚ(x)`. -/
def nVarDt : CPolyG NLvl1 := [CField.zero, nLvl1TwoX]

/-- The integrand numerator `a = 2x` over `CPolyG NLvl1` for `f = 2x/(t−1) = 2x/(exp(x²) − 1)`. The
numerator carries the `η = 2x` factor so the §5.6 residue `2x/(η·1) = 1` is a genuine δ-constant. -/
def nVarNormA : CPolyG NLvl1 := [nLvl1TwoX]

/-- The integrand denominator `d = t − 1` over `CPolyG NLvl1` for `f = 2x/(t−1)` (a normal factor:
`gcd(t−1, Dt) = 1`). -/
def nVarNormD : CPolyG NLvl1 := [CField.neg CField.one, CField.one]

/-- The residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for `2x/(exp(x²) − 1)` (the genuine
δ-constant residue is `1`). -/
def nVarNormCands : List NLvl1 := [CField.zero, CField.one, CField.neg CField.one]

/-- **The non-constant base residual `R = 2x` on `f = 2x/(exp(x²) − 1)`** (`native_decide`): for the normal
part `fₙ = 2x/(t−1)` over ℚ(x)[t] (`Dt = η·t`, `η = 2x` **non-constant**), the §5.6 residue `2x/(η·1) = 1` is
a genuine δ-constant, so `∑res = 1` and the §5.9 residual `R = η·∑res = 2x·1 = 2x` is a genuinely
**non-constant** rational function of `x` (`cHyperexpResidualG`), confirmed by `CField.isZero (R − 2x) =
true`. The non-constant overshoot the feedback must integrate. -/
theorem nVarNorm_residual_eq_twoX :
    CField.isZero (CField.sub
      (cHyperexpResidualG (cExpEtaG nVarDt)
        (cIntegrateReducedGWf nVarDt nVarNormA nVarNormD nVarNormCands).logs)
      nLvl1TwoX) = true := by native_decide

/-- **The non-constant base residual integral `∫R = ∫2x = x²`** (`native_decide`): the §5.9 feedback
integrates the **non-constant** residual `R = 2x ∈ ℚ(x)` as a base Risch-DE `Dy = 2x` over `k = ℚ(x)`
(`crischDESolve 0 (2x)`, running the §6 pipeline over ℚ[x] and recursing to ℚ), recovering `y = x²` —
genuine non-constant base polynomial integration. Certified by `CField.isZero (y − x²) = true`. -/
theorem nVarNorm_baseIntegral_eq_xSq :
    (match CRischField.crischDESolve (CField.zero : NLvl1) nLvl1TwoX with
      | some y => CField.isZero (CField.sub y nLvl1XSq)
      | none => false) = true := by native_decide

/-- **★★ The §5.9 driver lands `∫ 2x/(exp(x²) − 1) = log(exp(x²) − 1) − x²`, and `D(∫f) = f`**
(`native_decide`, the non-constant-residual stretch). On the hyperexponential **normal** integrand
`f = 2x/(t−1)` over `ℚ(x)[t]` with `t = exp(x²)` (`Dt = η·t`, `η = 2x` **non-constant**), the §5.9 driver
`cIntegrateHyperexpNormalGWf` reads the **non-constant** residual `R = 2x` (`nVarNorm_residual_eq_twoX`),
integrates the base residual `∫R = x²` (`nVarNorm_baseIntegral_eq_xSq`), and subtracts it from the log
part, returning `log(t−1) − x²` (rational part `−x²`, one log `(1, t−1)`) with the antiderivative identity
`D(res) = f` (`checkIdentityG`, over ℚ(x)[t]). **The residual feedback handles a genuinely non-constant
base residual** — the §5.9 reduction is not limited to constant `R`. -/
theorem nVarNorm_landsNormalPart :
    (match CPolyG.cIntegrateHyperexpNormalGWf nVarDt nVarNormA nVarNormD nVarNormCands with
      | some res =>
        CPolyG.checkIdentityG nVarDt res nVarNormA nVarNormD
          && CPolyG.cisZeroG (CPolyG.csubG res.rational.1 [CField.neg nLvl1XSq])
          && res.logs.length == 1
      | none => false) = true := by native_decide

#print axioms nVarNorm_landsNormalPart

end DeepWiki.SymbolicIntegration
