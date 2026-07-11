import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveNorm.Construction

/-! # Denotation bridges for weak-normalized Risch-DE solving

Field-level readings of the weak-normalized solver's `CFrac` constructions. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac GBPolyCore

universe u v

section Generic

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
variable {F : (α : Type u) → [CField α] → Type u} [CFrac F P] [LawfulCFrac F P]
variable {β : Type u} [CField β] [CFieldSpec.{u,v} β] [CDiffField β] [CDiffFieldSpec.{u,v} β]
  [CFieldDomain β P] [Algebra ℚ (CFieldSpec.K β)]

/-- Weak normalization denotes subtraction of the represented logarithmic derivative. -/
theorem toRatFunc_weakNormalizedF (f q' : F β) :
    toRatFunc (weakNormalizedF f q') =
      toRatFunc f -
        extendDeriv (Differential.implicitDeriv (CPoly.toPoly (CPoly.one : P β))) (toRatFunc q') /
          toRatFunc q' := by
  rw [weakNormalizedF, toRatFunc_sub, toRatFunc_mul, toRatFunc_inv,
    CFrac.toRatFunc_towerDerivCFracWith, div_eq_mul_inv]

omit [CDiffField β] [CDiffFieldSpec.{u,v} β] [Algebra ℚ (CFieldSpec.K β)] in
/-- Multiplying a represented solution by an inverse denotes fraction-field division. -/
theorem toRatFunc_solution (ytilde q' : F β) :
    toRatFunc (mul ytilde (inv q')) = toRatFunc ytilde / toRatFunc q' := by
  rw [toRatFunc_mul, toRatFunc_inv, div_eq_mul_inv]

end Generic

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β DensePoly]
  [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

omit [CRischField β] in
/-- `towerFractionFieldDeriv_toRatFunc`: `towerFractionFieldDeriv [1]` agrees with
`towerDerivCFrac [1]` through `toRatFunc`. -/
theorem towerFractionFieldDeriv_toRatFunc (x : DenseFrac β) :
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly β) (toRatFunc x)
      = toRatFunc (towerDerivCFrac ([CCommRing.one] : DensePoly β) x) := by
  rw [towerFractionFieldDeriv]
  unfold towerDerivCFrac
  rw [toRatFunc_towerDerivCFracWith]
  simp only [toPoly_list_eq]

omit [CRischField β] in
/-- Dense weak normalization agrees with the legacy `towerFractionFieldDeriv` spelling. -/
theorem toRatFunc_weakNormalizedF_dense (f q' : DenseFrac β) :
    toRatFunc (weakNormalizedF f q')
      = toRatFunc f
        - towerFractionFieldDeriv ([CCommRing.one] : DensePoly β) (toRatFunc q') / toRatFunc q' := by
  rw [weakNormalizedF, toRatFunc_sub, toRatFunc_mul, toRatFunc_inv,
    towerFractionFieldDeriv_toRatFunc, div_eq_mul_inv]
  rfl

end DeepWiki.SymbolicIntegration
