import DeepWiki.SymbolicIntegration.Engine.IntegratorAssembly

/-! # Concrete one-level Risch case definitions

The primitive and hyperexponential `MonomialCase` realizations, plus concrete
`native_decide` validations of the generic assembler on each case.
-/

namespace DeepWiki.SymbolicIntegration


namespace CPoly

variable {α : Type*} [CField α] [CDiffField α]

variable [CFracGcdCoreWf α]

variable [CRischField α]

/-- Primitive monomial case (`Dt ∈ α`): the special part is empty (`b = 0` required), the polynomial part
`fₚ` is integrated by the `b = 0` RDE `cPolyRischDEG` as `qₚ/1`; the reduced part needs no correction. -/
def primitiveCase : MonomialCase α where
  integrateSpecial Dt fp b _ds :=
    if cisZeroG b then
      match cPolyRischDEG Dt [] fp ((cdegG fp : ℤ) + 1) with
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
theorem cIntegrateHyperexpFullG_eq_case (Dt a d : CPoly α) (cands : List α) :
    cIntegrateHyperexpFullG Dt a d cands = cIntegrateCase hyperexpCase Dt a d cands := rfl

end CPoly

open CPoly

/-! ### Validation — one assembler reproduces the antiderivative identity on both cases (`native_decide`) -/

open CPoly

/-- Primitive case: `∫ 1/t² = −1/t` over `ℚ(x)[t]` with `Dt = 1` — `cIntegrateCase primitiveCase` returns a
result satisfying `checkIdentityG`. -/
theorem cIntegrateCase_primitive_invSq :
    (match cIntegrateCase (primitiveCase) ([CField.one] : CPoly Lvl1)
        [CField.one] [CField.zero, CField.zero, CField.one] [CField.zero] with
      | some res => checkIdentityG ([CField.one] : CPoly Lvl1) res [CField.one]
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
