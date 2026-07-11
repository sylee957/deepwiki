import DeepWiki.SymbolicIntegration.Engine.IntegratorCases
import DeepWiki.SymbolicIntegration.Engine.CanonicalReconstructionCharZero
import DeepWiki.SymbolicIntegration.Engine.PrimitiveGuarded

/-! # Primitive-case special-part soundness (shared by the LRT primitive base and tower)

`primitiveGuardedCase_specialSound`: the special (polynomial/RDE) part of the primitive monomial case
integrates soundly. Under the `primitiveGuardedCase` guard (`b = 0`, `Dθ = 1`, constant `fₚ`) the polynomial
RDE is solved and `canonicalReconstruction_of_charZero` closes the reconstruction with the special term
vanishing; off the guard the hook returns `none`. This `K`-level identity is the `specialSound` field of the
LRT primitive base `instLawfulRischLevelLrtPrimitive` (`RischTowerLrt.lean`) — independent of any reduced
frontier, so the recursive solver reuses it. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac Polynomial Classical
open scoped Differential

universe u v

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CPolyGcd DensePoly α] [LawfulCPolyGcd.{u,v} DensePoly α]
  [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

omit [CRischField α] in
/-- **The shared primitive special-part soundness core** (base and tower). Given the polynomial-part special
identity `hid : D_tower(⟦qp/1⟧) = ⟦fₚ/1⟧` and the vanishing special numerator `hb : crSpecNum = 0`, the
`specialSound` conclusion follows: `⟦1⟧ ≠ 0`, the witness `v = ⟦fₚ/1⟧` is the special derivative (`hid`), and
`v + ⟦cₙ/dₙ⟧ = a/d` from `canonicalReconstruction_of_charZero` with the special term dropping (`b = 0`).
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

/-- Primitive special-part soundness shared by the LRT primitive base and tower solvers. The special
part is `primitiveGuardedCase.integrateSpecial`: under the guard (`b = 0`, `Dθ = 1`, constant `fₚ`) it solves
the polynomial RDE and the reconstruction (`canonicalReconstruction_of_charZero`) closes with the special term
vanishing; off the guard the hook returns `none`. Independent of any reduced frontier, so the recursive solver
reuses it. -/
theorem primitiveGuardedCase_specialSound (Dt a d snum sden : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hhook : primitiveGuardedCase.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d)
      (crSpecDen Dt a d) = some (snum, sden)) :
    toPoly sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDeriv Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d := by
  simp only [primitiveGuardedCase] at hhook
  by_cases hguard : (cisZero (crSpecNum Dt a d) && cisZero (csub Dt [CCommRing.one])
      && cisZero (CPolyEngine.mapDeriv (crPoly Dt a d))) = true
  · rw [if_pos hguard] at hhook
    rw [Bool.and_eq_true, Bool.and_eq_true] at hguard
    obtain ⟨⟨hb, hDt1g⟩, hconstg⟩ := hguard
    rcases hqp : cPolyRischDE Dt [] (crPoly Dt a d) ((cdeg (crPoly Dt a d) : ℤ) + 1) with _ | qp
    · rw [hqp] at hhook; simp at hhook
    · rw [hqp] at hhook
      simp only [Option.some.injEq, Prod.mk.injEq] at hhook
      obtain ⟨rfl, rfl⟩ := hhook
      have hDt1 : toPoly Dt = 1 := by
        have hh := (cisZeroG_iff (csub Dt [CCommRing.one])).mp hDt1g
        simpa only [denote, map_one, mul_zero, add_zero, sub_eq_zero] using hh
      have hconst := mapCoeffs_eq_zero_of_cisZeroG_cmapDeriv (crPoly Dt a d) hconstg
      exact primitiveSpecialSoundCore Dt a d qp hd0 hb
        (primitive_special_identity Dt (crPoly Dt a d) qp hDt1 hconst hqp)
  · rw [if_neg hguard] at hhook; simp at hhook

end DeepWiki.SymbolicIntegration
