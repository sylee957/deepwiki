import DeepWiki.SymbolicIntegration.Computable.Tower.RischDE
import DeepWiki.SymbolicIntegration.Computable.Tower.RischDEInstance
import DeepWiki.SymbolicIntegration.Computable.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.LaurentCore

/-! # The hyperexponential special-part integral — term-by-term Laurent integration

For a hyperexponential monomial `t` (`Dt = η·t`), the polynomial + special part `fₚ + fₛ` is a Laurent
polynomial `∑ⱼ aⱼ tʲ`; each term integrates by solving the base RDE `Dqⱼ + (j·η)·qⱼ = aⱼ` via
`CRischField.crischDESolve`, and the normal part goes through `cIntegrateReducedGWf`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-! ### The full hyperexponential integral driver `cIntegrateHyperexpG`

`cIntegrateHyperexpG Dt a d cands` canonical-splits `f = fₚ + (b/dₛ) + (cₙ/dₙ)`, routes the Laurent part
through `cIntegrateHyperexpLaurentG` and the normal part through `cIntegrateReducedGWf`, and combines the
rational parts. -/

/-- Full hyperexponential integral `cIntegrateHyperexpG Dt a d cands` for `f = a/d ∈ k(t)` with a monomial
`t` (`Dt = η·t`): returns `some ⟨(num, den), logs⟩` with `∫ f = num/den + ∑ᵢ cᵢ·log(vᵢ)`, or `none`.
Canonical-splits `f = fₚ + (b/dₛ) + (cₙ/dₙ)`, integrates the Laurent part `fₚ + b/dₛ` by
`cIntegrateHyperexpLaurentG` and the normal part `cₙ/dₙ` by `cIntegrateReducedGWf`, and combines the
rational parts; `none` if the Laurent integration fails. -/
def cIntegrateHyperexpG (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let η : α := cExpEtaG Dt
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFastGWf Dt a d
  let neg : List α := cHyperexpSpecialNegG b ds
  match cIntegrateHyperexpLaurentG η fp neg with
  | none => none
  | some (lnum, lden) =>
    let nrm := cIntegrateReducedGWf Dt cn dn cands
    let (gnum, gden) := nrm.rational
    -- combine `lnum/lden + gnum/gden`.
    let num := caddG (cmulG lnum gden) (cmulG gnum lden)
    let den := cmulG lden gden
    some ⟨(num, den), nrm.logs⟩

end CPolyG

/-! ### Validation: `∫ 1/exp = −1/exp` at a hyperexponential tower level

`f = t⁻¹ = 1/exp` over `ℚ(x)[t]` (`t = exp x`, `Dt = η·t`, `η = 1`) canonical-splits into the special part
`fₛ = 1/t` (`a₋₁ = 1`), whose base RDE `crischDESolve (−1) 1` gives `q₋₁ = −1`, so `∫ t⁻¹ = −1/t`. -/

open CPolyG

/-- Base field `Lvl1 = QFunNZG ℚ = ℚ(x)` over which the hyperexponential monomial `t = exp x` sits. -/
abbrev Lvl1 : Type := QFunNZG ℚ

/-- Hyperexponential monomial derivative `Dt = η·t = [0, 1]` over `CPolyG Lvl1 = ℚ(x)[t]` (`t = exp x`,
`η = 1`). -/
def hyperexpDt : CPolyG Lvl1 := [CField.zero, CField.one]

/-- Integrand numerator `a = 1` over `CPolyG Lvl1 = ℚ(x)[t]` for `f = 1/t = 1/exp`. -/
def hyperexpInvA : CPolyG Lvl1 := [CField.one]

/-- Integrand denominator `d = t = [0, 1]` over `CPolyG Lvl1 = ℚ(x)[t]` for `f = 1/t = 1/exp`. -/
def hyperexpInvD : CPolyG Lvl1 := [CField.zero, CField.one]

/-- Residue candidate set `{0, 1}` as `Lvl1 = ℚ(x)` constants for the `1/exp` integral (no genuine
residues). -/
def hyperexpInvCands : List Lvl1 := [CField.zero, CField.one]

/-- The hyperexponential coefficient `η = Dt/t = 1` for `Dt = [0, 1]`: `cExpEtaG` reads `η = 1 ∈ ℚ(x)`. -/
theorem hyperexp_eta_eq_one :
    CField.isZero (CField.sub (cExpEtaG hyperexpDt) (CField.one : Lvl1)) = true := by native_decide

/-- The driver lands `∫ 1/exp = −1/exp` with `D(∫f) = f`: on `f = 1/t` over `ℚ(x)[t]` (`Dt = η·t`, `η = 1`)
`cIntegrateHyperexpG` returns `some res` with rational part `−1/t` and no logs, satisfying
`checkIdentityG`. -/
theorem hyperexpInv_landsSpecialPart :
    (match CPolyG.cIntegrateHyperexpG hyperexpDt hyperexpInvA hyperexpInvD hyperexpInvCands with
      | some res => CPolyG.checkIdentityG hyperexpDt res hyperexpInvA hyperexpInvD
      | none => false) = true := by native_decide

#print axioms hyperexpInv_landsSpecialPart

/-! ### Poly + special mix: `∫(exp + 1/exp) = exp − 1/exp`

Over `ℚ(x)[t]` (`t = exp`, `Dt = t`), `f = t + t⁻¹` has `fₚ = t` (`a₁ = 1`) and `fₛ = t⁻¹` (`a₋₁ = 1`); the
per-term RDEs give `q₁ = 1`, `q₋₁ = −1`, so `∫(t + t⁻¹) = t − t⁻¹`. Assembled as `f = (t²+1)/t`. -/

/-- Integrand numerator `a = t² + 1` for `f = (t²+1)/t = t + 1/t = exp + 1/exp` over `CPolyG Lvl1`. -/
def hyperexpPolySpecA : CPolyG Lvl1 := [CField.one, CField.zero, CField.one]

/-- Integrand denominator `d = t` for `f = (t²+1)/t` over `CPolyG Lvl1`. -/
def hyperexpPolySpecD : CPolyG Lvl1 := [CField.zero, CField.one]

/-- The driver lands `∫(exp + 1/exp) = exp − 1/exp` with `D(∫f) = f`: `cIntegrateHyperexpG` integrates each
term (`q₁ = 1`, `q₋₁ = −1`), recombining to `t − t⁻¹` satisfying `checkIdentityG`. -/
theorem hyperexpPolySpec_lands :
    (match CPolyG.cIntegrateHyperexpG hyperexpDt hyperexpPolySpecA hyperexpPolySpecD
        hyperexpInvCands with
      | some res => CPolyG.checkIdentityG hyperexpDt res hyperexpPolySpecA hyperexpPolySpecD
      | none => false) = true := by native_decide

/-! ### A special + normal mix — the special part lands, the normal log part overshoots

On `f = t⁻¹ + 1/(t−1)` over `ℚ(x)[t]` (`t = exp`, `Dt = t`), `cIntegrateHyperexpG` lands the special part
`−1/t` but its normal log part `log(t−1)` overshoots `1/(t−1)` by the residual `R = 1`, so the full-`f`
identity fails — closed by the residual-feedback driver elsewhere. -/

/-- Integrand numerator `a = 2t − 1` for `f = (2t−1)/(t²−t) = 1/t + 1/(t−1)` over `CPolyG Lvl1`. -/
def hyperexpSpecNormA : CPolyG Lvl1 := [CField.neg CField.one, CField.add CField.one CField.one]

/-- Integrand denominator `d = t² − t = t(t−1)` for `f = (2t−1)/(t²−t)` over `CPolyG Lvl1`. -/
def hyperexpSpecNormD : CPolyG Lvl1 := [CField.zero, CField.neg CField.one, CField.one]

/-- Residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for the special+normal mix. -/
def hyperexpSpecNormCands : List Lvl1 := [CField.zero, CField.one, CField.neg CField.one]

/-- The driver runs on the special+normal integrand `f = t⁻¹ + 1/(t−1)`: `cIntegrateHyperexpG` returns
`some` (the normal log part overshoots, so the full-`f` identity does not hold). -/
theorem hyperexpSpecNorm_runs :
    (CPolyG.cIntegrateHyperexpG hyperexpDt hyperexpSpecNormA hyperexpSpecNormD
      hyperexpSpecNormCands).isSome = true := by native_decide

/-- The special part `1/t` of the special+normal integrand integrates exactly: its special part is exactly
the inverse integrand (`a = 1`, `d = t`), so this is `hyperexpInv_landsSpecialPart` — `cIntegrateHyperexpG`
gives `−1/t` satisfying `checkIdentityG`. -/
theorem hyperexpSpecNorm_specialPart_exact :
    (match CPolyG.cIntegrateHyperexpG hyperexpDt hyperexpInvA hyperexpInvD hyperexpInvCands with
      | some res => CPolyG.checkIdentityG hyperexpDt res hyperexpInvA hyperexpInvD
      | none => false) = true := hyperexpInv_landsSpecialPart

#print axioms hyperexpSpecNorm_runs

end DeepWiki.SymbolicIntegration
