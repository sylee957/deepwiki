import DeepWiki.SymbolicIntegration.Engine.Assemble
import DeepWiki.ComputableAlgebra.PolyReprConvert

/-! # Sparse monomial-case adapter

A lawful dense monomial solver can be used behind the sparse representation boundary. -/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

universe u

variable {α : Type u} [CField α] [CFieldSpec.{u,u} α] [CDiffField α] [CDiffFieldSpec.{u,u} α]
  [Algebra ℚ (CFieldSpec.K α)]

private def convertResult {P Q : Type u → Type u} [CPoly P] [CPolyEngine P]
    [CPoly Q] [CPolyEngine Q] (res : IntegralResult α P) : IntegralResult α Q :=
  { rational := (CPolyEngine.convert res.rational.1, CPolyEngine.convert res.rational.2)
    logs := res.logs.map fun cv => (cv.1, CPolyEngine.convert cv.2) }

private theorem isIntegralResultP_convertResult {P Q : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,u} P]
    [CPoly Q] [CPolyEngine Q] [LawfulCPolyEngine.{u,u} Q]
    (Dt a d : P α) (res : IntegralResult α P) (h : IsIntegralResultP Dt a d res) :
    IsIntegralResultP (CPolyEngine.convert Dt : Q α) (CPolyEngine.convert a)
      (CPolyEngine.convert d) (convertResult res) := by
  have hlog : logResidueSumP (CPolyEngine.convert Dt : Q α)
      (res.logs.map fun cv => (cv.1, CPolyEngine.convert cv.2)) = logResidueSumP Dt res.logs := by
    rw [logResidueSumP, logResidueSumP, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro cv _
    simp only [Function.comp_apply, CPolyEngine.toPoly_convert,
      CPolyEngine.toPoly_monomialDeriv]
  simpa only [IsIntegralResultP, convertResult, CPolyEngine.toPoly_convert, hlog,
    towerFractionFieldDerivP] using h

/-- Expose dense monomial-case hooks through sparse polynomial inputs and outputs. -/
def denseMonomialCaseAsSparse (C : CMonomialCase DensePoly α) :
    CMonomialCase CPoly.SparsePoly α where
  integrateSpecial Dt fp b ds :=
    (C.integrateSpecial (CPolyEngine.convert Dt) (CPolyEngine.convert fp)
      (CPolyEngine.convert b) (CPolyEngine.convert ds)).map fun out =>
        (CPolyEngine.convert out.1, CPolyEngine.convert out.2)
  postprocessNormal Dt before :=
    (C.postprocessNormal (CPolyEngine.convert Dt)
      (convertResult (Q := DensePoly) before)).map
        (convertResult (Q := CPoly.SparsePoly))

/-- A lawful dense monomial case remains lawful through the sparse representation boundary. -/
instance instLawfulCMonomialCaseDenseAsSparse (C : CMonomialCase DensePoly α)
    [LawfulCMonomialCase C] : LawfulCMonomialCase (denseMonomialCaseAsSparse C) where
  special_sound Dt fp b ds snum sden hrun := by
    change (C.integrateSpecial (CPolyEngine.convert Dt) (CPolyEngine.convert fp)
      (CPolyEngine.convert b) (CPolyEngine.convert ds)).map
        (fun out => (CPolyEngine.convert out.1, CPolyEngine.convert out.2)) =
      some (snum, sden) at hrun
    rw [Option.map_eq_some_iff] at hrun
    obtain ⟨⟨denseNum, denseDen⟩, hdense, hout⟩ := hrun
    simp only [Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl⟩ := hout
    have h := LawfulCMonomialCase.special_sound (C := C)
      (CPolyEngine.convert Dt) (CPolyEngine.convert fp) (CPolyEngine.convert b)
      (CPolyEngine.convert ds) denseNum denseDen hdense
    constructor
    · simpa only [CPolyEngine.toPoly_convert] using h.1
    · simpa only [fieldFracP, towerFractionFieldDerivP, CPolyEngine.toPoly_convert,
        CPoly.toPoly_one, map_one, div_one] using h.2
  postprocessNormal_sound Dt cn dn before after hbefore hrun := by
    change (C.postprocessNormal (CPolyEngine.convert Dt)
      (convertResult (Q := DensePoly) before)).map
        (convertResult (Q := CPoly.SparsePoly)) = some after at hrun
    rw [Option.map_eq_some_iff] at hrun
    obtain ⟨denseAfter, hdense, rfl⟩ := hrun
    have hbeforeDense := isIntegralResultP_convertResult (Q := DensePoly) Dt cn dn before hbefore
    have hafterDense := LawfulCMonomialCase.postprocessNormal_sound (C := C)
      (CPolyEngine.convert Dt) (CPolyEngine.convert cn) (CPolyEngine.convert dn)
      (convertResult (Q := DensePoly) before) denseAfter hbeforeDense hdense
    have hlog : logResidueSumP Dt
        (denseAfter.logs.map fun cv => (cv.1, CPolyEngine.convert cv.2)) =
        logResidueSumP (CPolyEngine.convert Dt : DensePoly α) denseAfter.logs := by
      rw [logResidueSumP, logResidueSumP, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro cv _
      simp only [Function.comp_apply, CPolyEngine.toPoly_convert,
        CPolyEngine.toPoly_monomialDeriv]
    rw [IsIntegralResultP]
    simp only [convertResult]
    rw [hlog]
    simpa only [IsIntegralResultP, CPolyEngine.toPoly_convert,
      towerFractionFieldDerivP] using hafterDense
  postprocessNormal_den_nonzero Dt before after hden hrun := by
    change (C.postprocessNormal (CPolyEngine.convert Dt)
      (convertResult (Q := DensePoly) before)).map
        (convertResult (Q := CPoly.SparsePoly)) = some after at hrun
    rw [Option.map_eq_some_iff] at hrun
    obtain ⟨denseAfter, hdense, rfl⟩ := hrun
    have hdenDense :
        CPoly.toPoly (convertResult (Q := DensePoly) before).rational.2 ≠ 0 := by
      simpa only [convertResult, CPolyEngine.toPoly_convert] using hden
    have hout := LawfulCMonomialCase.postprocessNormal_den_nonzero (C := C)
      (CPolyEngine.convert Dt) (convertResult (Q := DensePoly) before)
      denseAfter hdenDense hdense
    simpa only [convertResult, CPolyEngine.toPoly_convert] using hout

end DeepWiki.SymbolicIntegration
