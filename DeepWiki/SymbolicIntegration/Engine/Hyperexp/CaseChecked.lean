import DeepWiki.SymbolicIntegration.Engine.Hyperexp.LaurentCore
import DeepWiki.SymbolicIntegration.Engine.RischLevelDense

/-! # Checked hyperexponential monomial-case realization

The Laurent special solver is exposed through the common monomial interface only after an executable
denominator and derivative-identity check. The generic normal stage is already exact, so this realization
uses identity normal postprocessing. -/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α] [CRischField α]

/-- Checked hyperexponential special integration with exact normal-result passthrough. -/
def hyperexpCheckedCase : CMonomialCase DensePoly α where
  integrateSpecial Dt fp b ds :=
    match cIntegrateHyperexpLaurent (cExpEta Dt) fp (cHyperexpSpecialNeg b ds) with
    | none => none
    | some out =>
      let inputNum := CPolyEngine.add (CPolyEngine.mul fp ds) b
      let result : IntegralResult α := ⟨out, []⟩
      if ((!CPolyEngine.cisZero ds && !CPolyEngine.cisZero out.2) &&
          checkIdentity Dt result inputNum ds) then some out else none
  postprocessNormal _Dt nrm := some nrm

end DensePoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CRischField α] [Algebra ℚ (CFieldSpec.K α)]

/-- The checked hyperexponential hook satisfies the sound monomial-case contract. -/
instance instLawfulCMonomialCaseHyperexpChecked :
    LawfulCMonomialCase (DensePoly.hyperexpCheckedCase (α := α)) where
  special_sound Dt fp b ds snum sden hrun := by
    simp only [DensePoly.hyperexpCheckedCase] at hrun
    split at hrun
    · contradiction
    · rename_i out hlaurent
      split at hrun
      · rename_i hguard
        have hout : out = (snum, sden) := Option.some.inj hrun
        subst out
        rw [Bool.and_eq_true, Bool.and_eq_true] at hguard
        obtain ⟨⟨hdsBool, hsdenBool⟩, hcheck⟩ := hguard
        have hds : CPoly.toPoly ds ≠ 0 := by
          intro hz
          rw [toPoly_list_eq] at hz
          have hzero := (DensePoly.cisZeroG_iff ds).mpr hz
          have hfalse : DensePoly.cisZero ds = false := by simpa using hdsBool
          rw [hzero] at hfalse
          contradiction
        have hsden : CPoly.toPoly sden ≠ 0 := by
          intro hz
          rw [toPoly_list_eq] at hz
          have hzero := (DensePoly.cisZeroG_iff sden).mpr hz
          have hfalse : DensePoly.cisZero sden = false := by simpa using hsdenBool
          rw [hzero] at hfalse
          contradiction
        refine ⟨hsden, ?_⟩
        let inputNum := CPolyEngine.add (CPolyEngine.mul fp ds) b
        let result : IntegralResult α := ⟨(snum, sden), []⟩
        have hid := field_identity_of_checkIdentityP Dt result inputNum ds hsden hds
          (by simp [result]) hcheck
        have htarget : fieldFracP inputNum ds =
            fieldFracP fp CPoly.one + fieldFracP b ds := by
          simp only [inputNum, fieldFracP, LawfulCPolyEngine.toPoly_add,
            LawfulCPolyEngine.toPoly_mul, CPoly.toPoly_one, map_add, map_mul, map_one]
          have hAds : am α (CPoly.toPoly ds) ≠ 0 := am_ne_zero hds
          field_simp
        simpa only [result, logResidueSumP, List.map_nil, List.sum_nil, add_zero] using
          hid.trans htarget
      · contradiction
  postprocessNormal_sound _ _ _ before after hbefore hrun := by
    have heq : before = after := Option.some.inj (by
      simpa only [DensePoly.hyperexpCheckedCase] using hrun)
    subst after
    exact hbefore
  postprocessNormal_den_nonzero _ before after hden hrun := by
    have heq : before = after := Option.some.inj (by
      simpa only [DensePoly.hyperexpCheckedCase] using hrun)
    subst after
    exact hden

end DeepWiki.SymbolicIntegration
