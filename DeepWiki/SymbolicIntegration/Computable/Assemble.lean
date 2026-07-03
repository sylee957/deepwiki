import DeepWiki.SymbolicIntegration.Computable.UnifiedFuelFree
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.NormalCore
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.Special

/-! # Assemblable one-level Risch integrator

One generic integrator `cIntegrateCase` parameterized by a `MonomialCase` record (the per-case hooks), with
the primitive and hyperexponential cases as values. `cIntegrateHyperexpFullGWf` is definitionally the
hyperexp case; the primitive case is validated to reproduce the antiderivative identity.
-/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- The per-monomial-case hooks of one-level Risch integration: `integrateSpecial Dt fp b ds` handles the
polynomial/special part as a fraction, `reducedCorrect Dt` post-processes the reduced normal part. -/
structure MonomialCase (α : Type*) [CField α] [CDiffField α] where
  /-- Integrate the special/polynomial part `fₚ + b/dₛ` to a fraction `(snum, sden)`, or `none`. -/
  integrateSpecial : CPolyG α → CPolyG α → CPolyG α → CPolyG α → Option (CPolyG α × CPolyG α)
  /-- Post-process the reduced normal result (identity for primitive; residual subtraction for hyperexp). -/
  reducedCorrect : CPolyG α → IntegralResultG α → Option (IntegralResultG α)

/-- Combine a special-part fraction `snum/sden` with the corrected normal result `nrm = gnum/gden + logs`:
`(snum·gden + gnum·sden)/(sden·gden) + logs`. -/
def combineSN (snum sden : CPolyG α) (nrm : IntegralResultG α) : IntegralResultG α :=
  let gnum := nrm.rational.1
  let gden := nrm.rational.2
  ⟨(caddG (cmulG snum gden) (cmulG gnum sden), cmulG sden gden), nrm.logs⟩

variable [CFracGcdCoreWf α]

/-- The generic one-level Risch integrator, parameterized by a monomial case `C`: canonical-split, run the
case's special-part hook, correct the reduced normal part, and combine. -/
def cIntegrateCase (C : MonomialCase α) (Dt a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFastGWf Dt a d
  match C.integrateSpecial Dt fp b ds with
  | none => none
  | some (snum, sden) =>
    match C.reducedCorrect Dt (cIntegrateReducedGWf Dt cn dn cands) with
    | none => none
    | some nrm => some (combineSN snum sden nrm)

variable [CRischField α]

/-- Primitive monomial case (`Dt ∈ α`): the special part is empty (`b = 0` required), the polynomial part
`fₚ` is integrated by the `b = 0` RDE `cPolyRischDEGWf` as `qₚ/1`; the reduced part needs no correction. -/
def primitiveCase : MonomialCase α where
  integrateSpecial Dt fp b _ds :=
    if cisZeroG b then
      match cPolyRischDEGWf Dt [] fp ((cdegG fp : ℤ) + 1) with
      | none => none
      | some qp => some (qp, [CField.one])
    else none
  reducedCorrect _Dt nrm := some nrm

/-- Hyperexponential monomial case (`Dt = η·t`): the special/Laurent part is integrated by
`cIntegrateHyperexpLaurentG`; the reduced correction subtracts `∫R` (the residual `η·∑ᵢ cᵢ`). -/
def hyperexpCase : MonomialCase α where
  integrateSpecial Dt fp b ds :=
    cIntegrateHyperexpLaurentG (cExpEtaG Dt) fp (cHyperexpSpecialNegG b ds)
  reducedCorrect Dt nrm :=
    let η := cExpEtaG Dt
    let R := cHyperexpResidualG η nrm.logs
    match CRischField.crischDESolve (CField.zero : α) R with
    | none => none
    | some intR =>
      let gnum := nrm.rational.1
      let gden := nrm.rational.2
      some ⟨(csubG gnum (cmulG [intR] gden), gden), nrm.logs⟩

/-- **Bridge (hyperexp): the hyperexponential driver is definitionally the hyperexp case.** -/
theorem cIntegrateHyperexpFullGWf_eq_case (Dt a d : CPolyG α) (cands : List α) :
    cIntegrateHyperexpFullGWf Dt a d cands = cIntegrateCase hyperexpCase Dt a d cands := rfl

end CPolyG

/-! ### Validation — one assembler reproduces the antiderivative identity on both cases (`native_decide`) -/

open CPolyG

/-- Primitive case: `∫ 1/t² = −1/t` over `ℚ(x)[t]` with `Dt = 1` — `cIntegrateCase primitiveCase` returns a
result satisfying `checkIdentityG`. -/
theorem cIntegrateCase_primitive_invSq :
    (match cIntegrateCase (primitiveCase) ([CField.one] : CPolyG Lvl1)
        [CField.one] [CField.zero, CField.zero, CField.one] [CField.zero] with
      | some res => checkIdentityG ([CField.one] : CPolyG Lvl1) res [CField.one]
          [CField.zero, CField.zero, CField.one]
      | none => false) = true := by native_decide

/-- Hyperexp case: `∫ 1/exp = −1/exp` — `cIntegrateCase hyperexpCase` reproduces the hyperexp driver's
result satisfying `checkIdentityG` (same integrand data as `hyperexpInv_landsSpecialPart`). -/
theorem cIntegrateCase_hyperexp_inv :
    (match cIntegrateCase hyperexpCase hyperexpDt hyperexpInvA hyperexpInvD hyperexpInvCands with
      | some res => checkIdentityG hyperexpDt res hyperexpInvA hyperexpInvD
      | none => false) = true := by native_decide

/-- Hyperexp case on the special+normal mix `∫(1/exp + 1/(exp−1))`: the assembler lands the full identity
(where the special-part-only driver overshoots). -/
theorem cIntegrateCase_hyperexp_specNorm :
    (match cIntegrateCase hyperexpCase hyperexpDt hyperexpSpecNormA hyperexpSpecNormD
        hyperexpSpecNormCands with
      | some res => checkIdentityG hyperexpDt res hyperexpSpecNormA hyperexpSpecNormD
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
