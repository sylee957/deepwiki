import DeepWiki.SymbolicIntegration.Engine.IntegratorAssembly

/-! # Concrete one-level Risch case definitions

The primitive and hyperexponential `MonomialCase` realizations, plus concrete
`native_decide` validations of the generic assembler on each case.
-/

namespace DeepWiki.SymbolicIntegration


namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α]

variable [CRischField α]

/-- Primitive monomial case (`Dt ∈ α`): the special part is empty (`b = 0` required), the polynomial part
`fₚ` is integrated by the `b = 0` RDE `cPolyRischDE` as `qₚ/1`; the reduced part needs no correction. -/
def primitiveCase : MonomialCase α where
  integrateSpecial Dt fp b _ds :=
    if cisZero b then
      match cPolyRischDE Dt [] fp ((cdeg fp : ℤ) + 1) with
      | none => none
      | some qp => some (qp, [CCommRing.one])
    else none
  reducedCorrect _Dt nrm := some nrm

variable [CFracGcdCoreWf α]

/-- Hyperexponential monomial case (`Dt = η·t`): the special/Laurent part is integrated by
`cIntegrateHyperexpLaurent`; the reduced correction subtracts `∫R` (the residual `η·∑ᵢ cᵢ`). -/
def hyperexpCase : MonomialCase α where
  integrateSpecial Dt fp b ds :=
    cIntegrateHyperexpLaurent (cExpEta Dt) fp (cHyperexpSpecialNeg b ds)
  reducedCorrect Dt nrm := cCorrectHyperexpNormal (cExpEta Dt) nrm

/-- **Bridge (hyperexp): the hyperexponential driver is definitionally the hyperexp case.** -/
theorem cIntegrateHyperexpFullG_eq_case (Dt a d : DensePoly α) (cands : List α) :
    cIntegrateHyperexpFull Dt a d cands = cIntegrateCase hyperexpCase Dt a d cands := rfl

end DensePoly

open DensePoly

/-! ### Validation — one assembler reproduces the antiderivative identity on both cases (`native_decide`) -/

open DensePoly

/-- Primitive case: `∫ 1/t² = −1/t` over `ℚ(x)[t]` with `Dt = 1` — `cIntegrateCase primitiveCase` returns a
result satisfying `checkIdentity`. -/
theorem cIntegrateCase_primitive_invSq :
    (match cIntegrateCase (primitiveCase) ([CCommRing.one] : DensePoly Lvl1)
        [CCommRing.one] [CCommRing.zero, CCommRing.zero, CCommRing.one] [CCommRing.zero] with
      | some res => checkIdentity ([CCommRing.one] : DensePoly Lvl1) res [CCommRing.one]
          [CCommRing.zero, CCommRing.zero, CCommRing.one]
      | none => false) = true := by native_decide

/-- Hyperexp case: `∫ 1/exp = −1/exp` — `cIntegrateCase hyperexpCase` reproduces the hyperexp driver's
result satisfying `checkIdentity` (same integrand data as `hyperexpInv_landsSpecialPart`). -/
theorem cIntegrateCase_hyperexp_inv :
    (match cIntegrateCase hyperexpCase hyperexpDt hyperexpInvA hyperexpInvD hyperexpInvCands with
      | some res => checkIdentity hyperexpDt res hyperexpInvA hyperexpInvD
      | none => false) = true := by native_decide

/-- Hyperexp case on the special+normal mix `∫(1/exp + 1/(exp−1))`: the assembler lands the full identity
(where the special-part-only driver overshoots). -/
theorem cIntegrateCase_hyperexp_specNorm :
    (match cIntegrateCase hyperexpCase hyperexpDt hyperexpSpecNormA hyperexpSpecNormD
        hyperexpSpecNormCands with
      | some res => checkIdentity hyperexpDt res hyperexpSpecNormA hyperexpSpecNormD
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
