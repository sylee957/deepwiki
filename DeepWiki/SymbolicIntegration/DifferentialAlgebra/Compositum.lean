import DeepWiki.SymbolicIntegration.DifferentialAlgebra.AlgebraicConstants
import Mathlib.FieldTheory.SeparableClosure

/-! # Composita of differential fields

Separable composita, their differential extensions, and compatibility from either factor.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

noncomputable section

section SeparableCompositum

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
      IsDifferentialExtensionOf ΔF.toDifferential ΔEF →
      letI : Algebra E EF := ι.toRingHom.toAlgebra
      IsDifferentialExtensionOf ΔE ΔEF := by
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

end SeparableCompositum

section AlgebraicClosureCompositum

variable {F Ebar : Type*} [Field F] [Field Ebar] [Algebra F Ebar]

/-- An algebraic closure of `F` embeds over `F` into an algebraic closure of an extension field. -/
theorem nonempty_algHom_isAlgClosure_extension
    {F E Fbar Ebar : Type*} [Field F] [Field E] [Field Fbar] [Field Ebar]
    [Algebra F E] [Algebra E Ebar] [Algebra F Ebar] [IsScalarTower F E Ebar]
    [Algebra F Fbar] [IsAlgClosure F Fbar] [IsAlgClosure E Ebar] :
    Nonempty (Fbar →ₐ[F] Ebar) := by
  letI : IsAlgClosed Ebar := IsAlgClosure.isAlgClosed E
  exact ⟨IsAlgClosed.lift⟩

variable (E : IntermediateField F Ebar)

/-- The relative algebraic closure of `F` inside an algebraic closure of `E/F` is an algebraic closure of `F`. -/
theorem isAlgClosure_algebraicClosure_of_isAlgClosure [IsAlgClosure E Ebar] :
    IsAlgClosure F (algebraicClosure F Ebar) := by
  letI : IsAlgClosed Ebar := IsAlgClosure.isAlgClosed E
  infer_instance

variable [D : Differential F] [PerfectField F]

/-- If `Ebar/E` is an algebraic closure, compatible differential structures on `E` and `Fbar ⊆ Ebar` extend uniquely to `E Fbar`. -/
theorem existsUnique_differentialExtension_adjoin_algebraicClosure
    [IsAlgClosure E Ebar] (Δ : DifferentialExtension F E) :
    letI : Algebra E Ebar := E.val.toAlgebra
    let Fbar := algebraicClosure F Ebar
    let DFbar : DifferentialExtension F Fbar := differentialExtensionSeparable
    let EFbar := IntermediateField.adjoin E (Fbar : Set Ebar)
    let ι : Fbar →ₐ[F] EFbar :=
      IntermediateField.inclusion (show Fbar ≤ EFbar.restrictScalars F from
        fun _ hx => IntermediateField.subset_adjoin E (Fbar : Set Ebar) hx)
    letI : Algebra Fbar EFbar := ι.toRingHom.toAlgebra
    ∃! ΔEFbar : Differential EFbar,
      IsDifferentialExtensionOf Δ.toDifferential ΔEFbar ∧
        IsDifferentialExtensionOf DFbar.toDifferential ΔEFbar := by
  dsimp only
  letI : Algebra E Ebar := E.val.toAlgebra
  letI : IsScalarTower F E Ebar := IsScalarTower.of_algebraMap_eq' rfl
  let Fbar := algebraicClosure F Ebar
  let DFbar : DifferentialExtension F Fbar := differentialExtensionSeparable
  let EFbar := IntermediateField.adjoin E (Fbar : Set Ebar)
  let ι : Fbar →ₐ[F] EFbar :=
    IntermediateField.inclusion (show Fbar ≤ EFbar.restrictScalars F from
      fun _ hx => IntermediateField.subset_adjoin E (Fbar : Set Ebar) hx)
  letI : Algebra Fbar EFbar := ι.toRingHom.toAlgebra
  obtain ⟨ΔEFbar, hE, hunique⟩ :=
    existsUnique_differentialExtension_compositum E Fbar Δ
  have hFbar : IsDifferentialExtensionOf DFbar.toDifferential ΔEFbar :=
    isDifferentialExtension_compositum_right E Fbar Δ
      DFbar.toDifferential ΔEFbar DFbar.differentialAlgebra hE
  refine ⟨ΔEFbar, ⟨hE, hFbar⟩, ?_⟩
  intro Δ' hΔ'
  exact hunique Δ' hΔ'.1

/-- Inside an algebraic closure `Ebar/E`, adjoining `Fbar` preserves equality of the constant fields. -/
theorem constantsIntermediateField_adjoin_algebraicClosure_eq_bot
    [hEbar : IsAlgClosure E Ebar] (Δ : DifferentialExtension F E) :
    letI : Algebra E Ebar := E.val.toAlgebra
    letI : IsScalarTower F E Ebar := IsScalarTower.of_algebraMap_eq' rfl
    let Fbar := algebraicClosure F Ebar
    let DFbar : DifferentialExtension F Fbar := differentialExtensionSeparable
    let EFbar := IntermediateField.adjoin E (Fbar : Set Ebar)
    let ι : Fbar →ₐ[F] EFbar :=
      IntermediateField.inclusion (show Fbar ≤ EFbar.restrictScalars F from
        fun _ hx => IntermediateField.subset_adjoin E (Fbar : Set Ebar) hx)
    letI : Algebra Fbar EFbar := ι.toRingHom.toAlgebra
    ∀ (ΔEFbar : Differential EFbar)
      (hΔ : IsDifferentialExtensionOf Δ.toDifferential ΔEFbar),
      let hFbar : IsDifferentialExtensionOf DFbar.toDifferential ΔEFbar :=
        isDifferentialExtension_compositum_right E Fbar Δ
          DFbar.toDifferential ΔEFbar DFbar.differentialAlgebra hΔ
      (letI : Differential E := Δ.toDifferential
       letI : DifferentialAlgebra F E := Δ.differentialAlgebra
       constantsIntermediateField F E = ⊥) →
      (letI : Differential Fbar := DFbar.toDifferential
       letI : Differential EFbar := ΔEFbar
       letI : DifferentialAlgebra Fbar EFbar := hFbar
       constantsIntermediateField Fbar EFbar = ⊥) := by
  dsimp only
  letI : Algebra E Ebar := E.val.toAlgebra
  letI : IsScalarTower F E Ebar := IsScalarTower.of_algebraMap_eq' rfl
  let Fbar := algebraicClosure F Ebar
  let DFbar : DifferentialExtension F Fbar := differentialExtensionSeparable
  let EFbar := IntermediateField.adjoin E (Fbar : Set Ebar)
  let ι : Fbar →ₐ[F] EFbar :=
    IntermediateField.inclusion (show Fbar ≤ EFbar.restrictScalars F from
      fun _ hx => IntermediateField.subset_adjoin E (Fbar : Set Ebar) hx)
  letI : Algebra Fbar EFbar := ι.toRingHom.toAlgebra
  intro ΔEFbar hΔ
  let hFbar : IsDifferentialExtensionOf DFbar.toDifferential ΔEFbar :=
    isDifferentialExtension_compositum_right E Fbar Δ
      DFbar.toDifferential ΔEFbar DFbar.differentialAlgebra hΔ
  intro hconstants
  letI : Differential E := Δ.toDifferential
  letI : Differential Fbar := DFbar.toDifferential
  letI : Differential EFbar := ΔEFbar
  letI : DifferentialAlgebra F E := Δ.differentialAlgebra
  letI : DifferentialAlgebra E EFbar := hΔ
  letI : DifferentialAlgebra Fbar EFbar := hFbar
  letI : Algebra.IsSeparable E EFbar := isSeparable_compositum E Fbar
  letI : IsAlgClosed Ebar := hEbar.isAlgClosed
  letI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  exact constantsIntermediateField_eq_bot_of_isAlgClosed_of_isAlgebraic hconstants

end AlgebraicClosureCompositum

end

end DeepWiki.SymbolicIntegration
