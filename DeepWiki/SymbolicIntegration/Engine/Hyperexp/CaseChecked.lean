import DeepWiki.SymbolicIntegration.Engine.Hyperexp.LaurentCore
import DeepWiki.SymbolicIntegration.Engine.Assemble

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
  integrateSpecial _fuel Dt fp b ds :=
    match cIntegrateHyperexpLaurent (cExpEta Dt) fp (cHyperexpSpecialNeg b ds) with
    | none => none
    | some out =>
      let inputNum := CPolyEngine.add (CPolyEngine.mul fp ds) b
      let result : IntegralResult α := ⟨out, []⟩
      if ((!CPolyEngine.cisZero ds && !CPolyEngine.cisZero out.2) &&
          CPoly.checkIdentity Dt result inputNum ds) then some result else none
  postprocessNormal _Dt nrm := some nrm

end DensePoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CRischField α] [Algebra ℚ (CFieldSpec.K α)]

/-- The checked hyperexponential hook satisfies the sound monomial-case contract. -/
instance instLawfulCMonomialCaseHyperexpChecked :
    LawfulCMonomialCase (DensePoly.hyperexpCheckedCase (α := α)) where
  special_sound _fuel Dt fp b ds res hrun := by
    simp only [DensePoly.hyperexpCheckedCase] at hrun
    split at hrun
    · contradiction
    · rename_i out hlaurent
      split at hrun
      · rename_i hguard
        have hout : ({ rational := out, logs := [] } : IntegralResult α) = res :=
          Option.some.inj hrun
        subst res
        rw [Bool.and_eq_true, Bool.and_eq_true] at hguard
        obtain ⟨⟨hdsBool, hsdenBool⟩, hcheck⟩ := hguard
        have hds : CPoly.toPoly ds ≠ 0 := by
          intro hz
          rw [toPoly_list_eq] at hz
          have hzero := (DensePoly.cisZeroG_iff ds).mpr hz
          have hfalse : DensePoly.cisZero ds = false := by simpa using hdsBool
          rw [hzero] at hfalse
          contradiction
        have hsden : CPoly.toPoly out.2 ≠ 0 := by
          intro hz
          rw [toPoly_list_eq] at hz
          have hzero := (DensePoly.cisZeroG_iff out.2).mpr hz
          have hfalse : DensePoly.cisZero out.2 = false := by simpa using hsdenBool
          rw [hzero] at hfalse
          contradiction
        refine ⟨hsden, ?_⟩
        let inputNum := CPolyEngine.add (CPolyEngine.mul fp ds) b
        let result : IntegralResult α := ⟨out, []⟩
        have hid := field_identity_of_checkIdentityP Dt result inputNum ds hsden hds
          (by simp [result]) hcheck
        have htarget : fieldFracP inputNum ds =
            fieldFracP fp CPoly.one + fieldFracP b ds := by
          simp only [inputNum, fieldFracP, LawfulCPolyEngine.toPoly_add,
            LawfulCPolyEngine.toPoly_mul, CPoly.toPoly_one, map_add, map_mul, map_one]
          have hAds : am α (CPoly.toPoly ds) ≠ 0 := am_ne_zero hds
          field_simp
        change towerFractionFieldDerivP Dt (fieldFracP out.1 out.2) +
          logResidueSumP Dt [] = fieldFracP fp CPoly.one + fieldFracP b ds
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

/-- The checked hyperexponential stage emits only genuine logarithmic terms. -/
instance instLawfulGenuineCMonomialCaseHyperexpChecked :
    LawfulGenuineCMonomialCase (DensePoly.hyperexpCheckedCase (α := α)) where
  special_coefficients_constant _fuel Dt fp b ds res hrun := by
    simp only [DensePoly.hyperexpCheckedCase] at hrun
    split at hrun
    · contradiction
    · split at hrun
      · have hout : res.logs = [] := by
          rw [← Option.some.inj hrun]
        simp [hout]
      · contradiction
  special_arguments_nonzero _fuel Dt fp b ds res hrun := by
    simp only [DensePoly.hyperexpCheckedCase] at hrun
    split at hrun
    · contradiction
    · split at hrun
      · have hout : res.logs = [] := by
          rw [← Option.some.inj hrun]
        simp [hout]
      · contradiction
  postprocessNormal_coefficients_constant _ before after hconstants hrun := by
    have heq : before = after := Option.some.inj (by
      simpa only [DensePoly.hyperexpCheckedCase] using hrun)
    subst after
    exact hconstants
  postprocessNormal_arguments_nonzero _ before after hargs hrun := by
    have heq : before = after := Option.some.inj (by
      simpa only [DensePoly.hyperexpCheckedCase] using hrun)
    subst after
    exact hargs

/-- Exact raw-acceptance domain of the checked hyperexponential special stage. -/
def hyperexpCheckedSpecialDomain : MonomialSpecialDomain DensePoly α := fun Dt fp b ds =>
  ∀ (res : IntegralResult α), CPoly.toPoly res.rational.2 ≠ 0 →
    towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2) +
        logResidueSumP Dt res.logs = fieldFracP fp CPoly.one + fieldFracP b ds →
      ∃ out, DensePoly.cIntegrateHyperexpLaurent (DensePoly.cExpEta Dt) fp
          (DensePoly.cHyperexpSpecialNeg b ds) = some out ∧
        CPoly.toPoly ds ≠ 0 ∧ CPoly.toPoly out.2 ≠ 0 ∧
        CPoly.checkIdentity Dt ({ rational := out, logs := [] } : IntegralResult α)
          (CPolyEngine.add (CPolyEngine.mul fp ds) b) ds = true

/-- The checked hyperexponential monomial stage is complete on its explicit raw-acceptance domain. -/
instance instCompleteCMonomialCaseHyperexpChecked :
    CompleteCMonomialCase (DensePoly.hyperexpCheckedCase (α := α))
      (hyperexpCheckedSpecialDomain (α := α)) where
  special_complete Dt fp b ds res hdomain hsden hderiv := by
    obtain ⟨out, hlaurent, hds, hout, hcheck⟩ := hdomain res hsden hderiv
    change CPoly.checkIdentity Dt ({ rational := out, logs := [] } : IntegralResult α)
      (DensePoly.cadd (DensePoly.cmul fp ds) b) ds = true at hcheck
    have hdsBool : DensePoly.cisZero ds = false := by
      rw [Bool.eq_false_iff]
      intro hzero
      exact hds (by simpa only [toPoly_list_eq] using (DensePoly.cisZeroG_iff ds).mp hzero)
    have houtBool : DensePoly.cisZero out.2 = false := by
      rw [Bool.eq_false_iff]
      intro hzero
      exact hout (by simpa only [toPoly_list_eq] using (DensePoly.cisZeroG_iff out.2).mp hzero)
    refine ⟨0, { rational := out, logs := [] }, ?_⟩
    simp [DensePoly.hyperexpCheckedCase, hlaurent, hdsBool, houtBool, hcheck]
  postprocess_complete _ _ _ before _ := ⟨before, rfl⟩

end DeepWiki.SymbolicIntegration
