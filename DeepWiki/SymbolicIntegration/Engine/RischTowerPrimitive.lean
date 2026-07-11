import DeepWiki.SymbolicIntegration.Engine.CanonicalReconstructionCharZero
import DeepWiki.SymbolicIntegration.Engine.PrimitiveGuarded

/-! # LRT special-part reconstruction

`lrtMonomialCase_specialSound` composes any lawful rational LRT monomial stage with canonical
reconstruction. `primitiveSpecialSoundCore` remains the proof kernel for the recursive tower implementation,
whose polynomial recursion establishes its special identity directly. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac Polynomial Classical
open scoped Differential

universe u v

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
  [CPolySplitFactor DensePoly α] [LawfulCPolySplitFactor DensePoly α]

omit [CRischField α] in
/-- **The shared primitive special-part soundness core** (base and tower). Given the polynomial-part special
identity `hid : D_tower(⟦qp/1⟧) = ⟦fₚ/1⟧` and the vanishing special numerator `hb : crSpecNum = 0`, the
`specialSound` conclusion follows: `⟦1⟧ ≠ 0`, the witness `v = ⟦fₚ/1⟧` is the special derivative (`hid`), and
`v + ⟦cₙ/dₙ⟧ = a/d` from the lawful selected split contract through
`canonicalReconstruction_of_charZero`, with the special term dropping (`b = 0`).
Agnostic to HOW `hid` was obtained — the base proves it via `cPolyRischDEG_nil_field_identity`, the tower via
the `implicitDeriv`/`towerFractionFieldDerivG_div` bridge — so both `*_specialSound` proofs reduce to this. -/
theorem primitiveSpecialSoundCore (Dt a d qp : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hb : cisZero (crSpecNum Dt a d) = true)
    (hid : towerFractionFieldDeriv Dt (fieldFrac qp [CCommRing.one])
      = fieldFrac (crPoly Dt a d) [CCommRing.one]) :
    toPoly ([CCommRing.one] : DensePoly α) ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDeriv Dt (fieldFrac qp [CCommRing.one]) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d := by
  refine ⟨?_, fieldFrac (crPoly Dt a d) [CCommRing.one], hid, ?_⟩
  · simp only [denote, mul_zero, add_zero]; exact one_ne_zero
  · have hvan : fieldFrac (crSpecNum Dt a d) (crSpecDen Dt a d) = 0 := by
      simp only [fieldFrac, (cisZeroG_iff (crSpecNum Dt a d)).mp hb, map_zero, zero_div]
    have hrec := canonicalReconstruction_of_charZero Dt a d hd0
    rw [hvan, add_zero] at hrec
    exact hrec

omit [CRischField α] in
/-- A lawful rational LRT monomial stage composes with canonical reconstruction. -/
theorem lrtMonomialCase_specialSound (C : CLrtMonomialCase DensePoly α)
    [LawfulCLrtMonomialCase C] (Dt a d snum sden : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hhook : C.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d)
      (crSpecDen Dt a d) = some (snum, sden)) :
    toPoly sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDeriv Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d := by
  obtain ⟨hsden, hspecial⟩ :=
    LawfulCLrtMonomialCase.special_sound (C := C) Dt (crPoly Dt a d)
      (crSpecNum Dt a d) (crSpecDen Dt a d) snum sden hhook
  refine ⟨?_,
    fieldFrac (crPoly Dt a d) [CCommRing.one]
      + fieldFrac (crSpecNum Dt a d) (crSpecDen Dt a d), ?_, ?_⟩
  · simpa only [toPoly_list_eq] using hsden
  · rw [show (CPoly.one : DensePoly α) = [CCommRing.one] from rfl] at hspecial
    simpa only [fieldFracP, DensePoly.fieldFrac, towerFractionFieldDerivP,
      towerFractionFieldDeriv, toPoly_list_eq] using hspecial
  · exact canonicalReconstruction_of_charZero Dt a d hd0

end DeepWiki.SymbolicIntegration
