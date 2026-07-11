import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEInstance
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.LaurentCore

/-! # The hyperexponential special-part integral — term-by-term Laurent integration

For a hyperexponential monomial `t` (`Dt = η·t`), the polynomial + special part `fₚ + fₛ` is a Laurent
polynomial `∑ⱼ aⱼ tʲ`; each term integrates by solving the base RDE `Dqⱼ + (j·η)·qⱼ = aⱼ` via
`CRischField.crischDESolve`, and the normal part goes through `cIntegrateReduced`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration


namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α]
  [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
  [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CRischField α]

/-! ### The full hyperexponential integral driver `cIntegrateHyperexp`

`cIntegrateHyperexp Dt a d cands` canonical-splits `f = fₚ + (b/dₛ) + (cₙ/dₙ)`, routes the Laurent part
through `cIntegrateHyperexpLaurent` and the normal part through `cIntegrateReduced`, and combines the
rational parts. -/

/-- Full hyperexponential integral `cIntegrateHyperexp Dt a d cands` for `f = a/d ∈ k(t)` with a monomial
`t` (`Dt = η·t`): returns `some ⟨(num, den), logs⟩` with `∫ f = num/den + ∑ᵢ cᵢ·log(vᵢ)`, or `none`.
Canonical-splits `f = fₚ + (b/dₛ) + (cₙ/dₙ)`, integrates the Laurent part `fₚ + b/dₛ` by
`cIntegrateHyperexpLaurent` and the normal part `cₙ/dₙ` by `cIntegrateReduced`, and combines the
rational parts; `none` if the Laurent integration fails. -/
def cIntegrateHyperexp (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) :
    Option (IntegralResult α) :=
  let η : α := cExpEta Dt
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFast Dt a d
  let neg : List α := cHyperexpSpecialNeg b ds
  match cIntegrateHyperexpLaurent η fp neg with
  | none => none
  | some (lnum, lden) =>
    let nrm := cIntegrateReduced Dt cn dn cands
    let (gnum, gden) := nrm.rational
    -- combine `lnum/lden + gnum/gden`.
    let num := cadd (cmul lnum gden) (cmul gnum lden)
    let den := cmul lden gden
    some ⟨(num, den), nrm.logs⟩

end DensePoly

/-! ### Validation: `∫ 1/exp = −1/exp` at a hyperexponential tower level

`f = t⁻¹ = 1/exp` over `ℚ(x)[t]` (`t = exp x`, `Dt = η·t`, `η = 1`) canonical-splits into the special part
`fₛ = 1/t` (`a₋₁ = 1`), whose base RDE `crischDESolve (−1) 1` gives `q₋₁ = −1`, so `∫ t⁻¹ = −1/t`. -/

open DensePoly

/-- Base field `Lvl1 = DenseFrac ℚ = ℚ(x)` over which the hyperexponential monomial `t = exp x` sits. -/
abbrev Lvl1 : Type := DenseFrac ℚ

/-- Hyperexponential monomial derivative `Dt = η·t = [0, 1]` over `DensePoly Lvl1 = ℚ(x)[t]` (`t = exp x`,
`η = 1`). -/
def hyperexpDt : DensePoly Lvl1 := [CCommRing.zero, CCommRing.one]

/-- Integrand numerator `a = 1` over `DensePoly Lvl1 = ℚ(x)[t]` for `f = 1/t = 1/exp`. -/
def hyperexpInvA : DensePoly Lvl1 := [CCommRing.one]

/-- Integrand denominator `d = t = [0, 1]` over `DensePoly Lvl1 = ℚ(x)[t]` for `f = 1/t = 1/exp`. -/
def hyperexpInvD : DensePoly Lvl1 := [CCommRing.zero, CCommRing.one]

/-- Residue candidate set `{0, 1}` as `Lvl1 = ℚ(x)` constants for the `1/exp` integral (no genuine
residues). -/
def hyperexpInvCands : List Lvl1 := [CCommRing.zero, CCommRing.one]

/-- The hyperexponential coefficient `η = Dt/t = 1` for `Dt = [0, 1]`: `cExpEta` reads `η = 1 ∈ ℚ(x)`. -/
theorem hyperexp_eta_eq_one :
    CCommRing.isZero (CField.sub (cExpEta hyperexpDt) (CCommRing.one : Lvl1)) = true := by native_decide

/-- The driver lands `∫ 1/exp = −1/exp` with `D(∫f) = f`: on `f = 1/t` over `ℚ(x)[t]` (`Dt = η·t`, `η = 1`)
`cIntegrateHyperexp` returns `some res` with rational part `−1/t` and no logs, satisfying
`checkIdentity`. -/
theorem hyperexpInv_landsSpecialPart :
    (match DensePoly.cIntegrateHyperexp hyperexpDt hyperexpInvA hyperexpInvD hyperexpInvCands with
      | some res => CPoly.checkIdentity hyperexpDt res hyperexpInvA hyperexpInvD
      | none => false) = true := by native_decide

#print axioms hyperexpInv_landsSpecialPart

/-! ### Poly + special mix: `∫(exp + 1/exp) = exp − 1/exp`

Over `ℚ(x)[t]` (`t = exp`, `Dt = t`), `f = t + t⁻¹` has `fₚ = t` (`a₁ = 1`) and `fₛ = t⁻¹` (`a₋₁ = 1`); the
per-term RDEs give `q₁ = 1`, `q₋₁ = −1`, so `∫(t + t⁻¹) = t − t⁻¹`. Assembled as `f = (t²+1)/t`. -/

/-- Integrand numerator `a = t² + 1` for `f = (t²+1)/t = t + 1/t = exp + 1/exp` over `DensePoly Lvl1`. -/
def hyperexpPolySpecA : DensePoly Lvl1 := [CCommRing.one, CCommRing.zero, CCommRing.one]

/-- Integrand denominator `d = t` for `f = (t²+1)/t` over `DensePoly Lvl1`. -/
def hyperexpPolySpecD : DensePoly Lvl1 := [CCommRing.zero, CCommRing.one]

/-- The driver lands `∫(exp + 1/exp) = exp − 1/exp` with `D(∫f) = f`: `cIntegrateHyperexp` integrates each
term (`q₁ = 1`, `q₋₁ = −1`), recombining to `t − t⁻¹` satisfying `checkIdentity`. -/
theorem hyperexpPolySpec_lands :
    (match DensePoly.cIntegrateHyperexp hyperexpDt hyperexpPolySpecA hyperexpPolySpecD
        hyperexpInvCands with
      | some res => CPoly.checkIdentity hyperexpDt res hyperexpPolySpecA hyperexpPolySpecD
      | none => false) = true := by native_decide

/-! ### A special + normal mix — the special part lands, the normal log part overshoots

On `f = t⁻¹ + 1/(t−1)` over `ℚ(x)[t]` (`t = exp`, `Dt = t`), `cIntegrateHyperexp` lands the special part
`−1/t` but its normal log part `log(t−1)` overshoots `1/(t−1)` by the residual `R = 1`, so the full-`f`
identity fails — closed by the residual-feedback driver elsewhere. -/

/-- Integrand numerator `a = 2t − 1` for `f = (2t−1)/(t²−t) = 1/t + 1/(t−1)` over `DensePoly Lvl1`. -/
def hyperexpSpecNormA : DensePoly Lvl1 := [CCommRing.neg CCommRing.one, CCommRing.add CCommRing.one CCommRing.one]

/-- Integrand denominator `d = t² − t = t(t−1)` for `f = (2t−1)/(t²−t)` over `DensePoly Lvl1`. -/
def hyperexpSpecNormD : DensePoly Lvl1 := [CCommRing.zero, CCommRing.neg CCommRing.one, CCommRing.one]

/-- Residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for the special+normal mix. -/
def hyperexpSpecNormCands : List Lvl1 := [CCommRing.zero, CCommRing.one, CCommRing.neg CCommRing.one]

/-- The driver runs on the special+normal integrand `f = t⁻¹ + 1/(t−1)`: `cIntegrateHyperexp` returns
`some` (the normal log part overshoots, so the full-`f` identity does not hold). -/
theorem hyperexpSpecNorm_runs :
    (DensePoly.cIntegrateHyperexp hyperexpDt hyperexpSpecNormA hyperexpSpecNormD
      hyperexpSpecNormCands).isSome = true := by native_decide

#print axioms hyperexpSpecNorm_runs

end DeepWiki.SymbolicIntegration
