import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv
import DeepWiki.SymbolicIntegration.Core.Differential.FractionFieldDeriv

/-! # Global-recursive represented-fraction tower instances

For every lawful `CFrac F P`, `CFieldSpec.K (F α) = RatFunc (CFieldSpec.K α)`. The abstract structures
needed by the Risch tower therefore iterate uniformly through dense and sparse fraction representations. -/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- `CharZero` iterates through every lawful represented-fraction tower. -/
noncomputable instance instCharZeroKCFrac
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P] [CFrac F P] [LawfulCFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P]
    [CharZero (CFieldSpec.K α)] : CharZero (CFieldSpec.K (F α)) :=
  inferInstanceAs (CharZero (RatFunc (CFieldSpec.K α)))

/-- `Algebra ℚ` iterates through every lawful represented-fraction tower. -/
noncomputable instance instAlgebraQKCFrac
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P] [CFrac F P] [LawfulCFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P]
    [Algebra ℚ (CFieldSpec.K α)] : Algebra ℚ (CFieldSpec.K (F α)) :=
  inferInstanceAs (Algebra ℚ (RatFunc (CFieldSpec.K α)))

/-- `CDiffFieldSpec` iterates through every lawful represented-fraction tower. -/
noncomputable instance instCDiffFieldSpecCFracRec
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P] [CFrac F P] [LawfulCFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
    [CFieldDomain α P] [Algebra ℚ (CFieldSpec.K α)] : CDiffFieldSpec (F α) where
  diffK := fractionFieldDifferential
    (Differential.implicitDeriv (CPoly.toPoly (CPoly.one : P α)))
  toK_cderiv a := by
    show CFrac.toRatFunc (CFrac.towerDerivCFracWith (CPoly.one : P α) a)
      = @Differential.deriv _ _ (fractionFieldDifferential
          (Differential.implicitDeriv (CPoly.toPoly (CPoly.one : P α)))) (CFrac.toRatFunc a)
    rw [CFrac.toRatFunc_towerDerivCFracWith (CPoly.one : P α) a]
    rfl

/-- The generic differential-denotation square resolves recursively at depth two for sparse fractions. -/
theorem sparseFrac_recursive_toK_cderiv (x : SparseFrac (SparseFrac ℚ)) :
    CFieldSpec.toK (CDiffField.cderiv x) = Differential.deriv (CFieldSpec.toK x) :=
  CDiffFieldSpec.toK_cderiv x

end DeepWiki.SymbolicIntegration
