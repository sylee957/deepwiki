import DeepWiki.SymbolicIntegration.DifferentialAlgebra.AlgebraicExtensions
import Mathlib.FieldTheory.SeparableClosure

/-! # Composita of differential fields

Separable composita, their differential extensions, and compatibility from either factor.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (F E : IntermediateField K Ω)

/-- A separable intermediate field remains separable after adjoining it to another field. -/
theorem isSeparable_compositum [Algebra.IsSeparable K E] :
    letI : Algebra F Ω := F.val.toAlgebra
    Algebra.IsSeparable F (IntermediateField.adjoin F (E : Set Ω)) := by
  letI : Algebra F Ω := F.val.toAlgebra
  letI : IsScalarTower K F Ω := IsScalarTower.of_algebraMap_eq' rfl
  let EF := IntermediateField.adjoin F (E : Set Ω)
  letI : Algebra EF Ω := EF.val.toAlgebra
  letI : IsScalarTower F EF Ω := IsScalarTower.of_algebraMap_eq' rfl
  constructor
  intro z
  have hE : (E : Set Ω) ⊆ separableClosure K Ω :=
    (le_separableClosure_iff K Ω E).2 inferInstance
  have hz' : (z : Ω) ∈ IntermediateField.adjoin F (separableClosure K Ω : Set Ω) :=
    IntermediateField.adjoin.mono F _ _ hE z.2
  have hzΩ : IsSeparable F (z : Ω) :=
    mem_separableClosure_iff.mp ((separableClosure.adjoin_le K F Ω) hz')
  exact IsSeparable.tower_bot (E := Ω) hzΩ

/-- A derivation on `F` extends uniquely to the compositum `F(E)` when `E/K` is separable. -/
theorem existsUnique_differentialExtension_compositum
    [Differential K] [Algebra.IsSeparable K E]
    (ΔF : DifferentialExtension K F) :
    letI : Algebra F Ω := F.val.toAlgebra
    let EF := IntermediateField.adjoin F (E : Set Ω)
    letI : Differential F := ΔF.toDifferential
    ∃! Δ : Differential EF, IsDifferentialExtension F EF Δ := by
  letI : Algebra F Ω := F.val.toAlgebra
  letI : IsScalarTower K F Ω := IsScalarTower.of_algebraMap_eq' rfl
  letI : Differential F := ΔF.toDifferential
  letI : Algebra.IsSeparable F (IntermediateField.adjoin F (E : Set Ω)) :=
    isSeparable_compositum F E
  exact existsUnique_differentialExtension_separable

/-- Compatible derivations on the factors make the compositum a differential extension of `E`. -/
theorem isDifferentialExtension_compositum_right
    [Differential K] [Algebra.IsSeparable K E]
    (ΔF : DifferentialExtension K F) :
    letI : Algebra F Ω := F.val.toAlgebra
    letI : IsScalarTower K F Ω := IsScalarTower.of_algebraMap_eq' rfl
    let EF := IntermediateField.adjoin F (E : Set Ω)
    let ι : E →ₐ[K] EF :=
      IntermediateField.inclusion (show E ≤ EF.restrictScalars K from
        fun _ hx => IntermediateField.subset_adjoin F (E : Set Ω) hx)
    ∀ (ΔE : Differential E) (ΔEF : Differential EF),
      IsDifferentialExtension K E ΔE →
      @IsDifferentialExtension F EF _ _ _ ΔF.toDifferential ΔEF →
      letI : Algebra E EF := ι.toRingHom.toAlgebra
      @IsDifferentialExtension E EF _ _ _ ΔE ΔEF := by
  dsimp only
  intro ΔE ΔEF hE hEF
  letI : Algebra F Ω := F.val.toAlgebra
  letI : IsScalarTower K F Ω := IsScalarTower.of_algebraMap_eq' rfl
  let EF := IntermediateField.adjoin F (E : Set Ω)
  let ι : E →ₐ[K] EF :=
    IntermediateField.inclusion (show E ≤ EF.restrictScalars K from
      fun _ hx => IntermediateField.subset_adjoin F (E : Set Ω) hx)
  letI : Differential F := ΔF.toDifferential
  letI : Differential E := ΔE
  letI : Differential EF := ΔEF
  letI : DifferentialAlgebra K F := ΔF.differentialAlgebra
  letI : DifferentialAlgebra K E := hE
  letI : DifferentialAlgebra F EF := hEF
  have hKEF : IsDifferentialExtension K EF ΔEF :=
    isDifferentialExtension_trans (inferInstance : Differential K) ΔF.toDifferential ΔEF
      ΔF.differentialAlgebra hEF
  exact isDifferentialExtension_algHom_of_isSeparable
    (inferInstance : Differential K) ΔE ΔEF hE hKEF ι

end

end DeepWiki.SymbolicIntegration
