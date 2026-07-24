import DeepWiki.SymbolicIntegration.DifferentialAlgebra.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Differential extensions

Bundled differential extensions and compatibility with base derivations.
-/

open scoped Differential IntermediateField
open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- `Δ` extends `D` along the specified algebra map. -/
def IsDifferentialExtensionOf
    {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    (D : Differential F) (Δ : Differential E) : Prop :=
  @DifferentialAlgebra F E _ _ _ D Δ

/-- The explicit two-derivation extension relation is differential-algebra compatibility. -/
theorem isDifferentialExtensionOf_iff_differentialAlgebra
    {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    (D : Differential F) (Δ : Differential E) :
    IsDifferentialExtensionOf D Δ ↔ @DifferentialAlgebra F E _ _ _ D Δ :=
  Iff.rfl

/-- A differential structure on `E` is compatible with the differential ring `F`. -/
def IsDifferentialExtension (F E : Type*) [CommRing F] [CommRing E]
    [Algebra F E] [Differential F] (Δ : Differential E) : Prop :=
  IsDifferentialExtensionOf (inferInstance : Differential F) Δ

/-- A differential structure on `E` together with compatibility over the differential ring `F`. -/
abbrev DifferentialExtension (F E : Type*) [CommRing F] [CommRing E]
    [Algebra F E] [Differential F] :=
  { Δ : Differential E // IsDifferentialExtension F E Δ }

namespace DifferentialExtension

variable {F E : Type*} [CommRing F] [CommRing E] [Algebra F E] [Differential F]

/-- The target differential structure of a differential extension. -/
abbrev toDifferential (Δ : DifferentialExtension F E) : Differential E :=
  Δ.1

/-- The derivation carried by a differential extension. -/
abbrev deriv (Δ : DifferentialExtension F E) : Derivation ℤ E E :=
  Δ.toDifferential.deriv

/-- The target derivation of a differential extension is compatible with the base derivation. -/
theorem differentialAlgebra (Δ : DifferentialExtension F E) :
    @DifferentialAlgebra F E _ _ _ _ Δ.toDifferential :=
  Δ.2

/-- The derivation of a differential extension commutes with `algebraMap`. -/
theorem deriv_algebraMap (Δ : DifferentialExtension F E) (a : F) :
    Δ.deriv (algebraMap F E a) = algebraMap F E (a′) :=
  Δ.differentialAlgebra.deriv_algebraMap a

/-- Restrict a differential extension to a derivation-stable intermediate field. -/
noncomputable def restrictIntermediateField
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential F]
    (Δ : DifferentialExtension F E) (K : IntermediateField F E)
    (hstable : ∀ x : E, x ∈ K → Δ.deriv x ∈ K) :
    DifferentialExtension F K := by
  let f : K →+ K :=
    { toFun := fun x => ⟨Δ.deriv x, hstable x x.property⟩
      map_zero' := by
        apply Subtype.ext
        exact map_zero Δ.deriv
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add Δ.deriv (x : E) (y : E) }
  let d : Derivation ℤ K K :=
    Derivation.mk' f.toIntLinearMap fun x y => by
      apply Subtype.ext
      change Δ.deriv ((x : E) * (y : E)) =
        (x : E) * Δ.deriv (y : E) + (y : E) * Δ.deriv (x : E)
      simpa only [smul_eq_mul] using Δ.deriv.leibniz (x : E) (y : E)
  let D : Differential K := ⟨d⟩
  refine ⟨D, ?_⟩
  exact ⟨fun a => by
    apply Subtype.ext
    exact Δ.deriv_algebraMap a⟩

/-- The restricted derivation agrees with the ambient derivation after inclusion. -/
@[simp] theorem restrictIntermediateField_deriv
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential F]
    (Δ : DifferentialExtension F E) (K : IntermediateField F E)
    (hstable : ∀ x : E, x ∈ K → Δ.deriv x ∈ K) (x : K) :
    ((restrictIntermediateField Δ K hstable).deriv x : E) = Δ.deriv x :=
  rfl

/-- If `t` is constant, the simple extension `F⟮t⟯` is stable under the ambient derivation. -/
theorem deriv_mem_adjoin_of_deriv_eq_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential F]
    (Δ : DifferentialExtension F E) {t : E} (ht : Δ.deriv t = 0) :
    ∀ x : E, x ∈ F⟮t⟯ → Δ.deriv x ∈ F⟮t⟯ := by
  apply IntermediateField.adjoin_induction F
    (p := fun x hx => Δ.deriv x ∈ F⟮t⟯)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [ht]
    exact IntermediateField.zero_mem _
  · intro a
    rw [Δ.deriv_algebraMap]
    exact IntermediateField.algebraMap_mem _ (a′)
  · intro x y hx hy hdx hdy
    rw [map_add]
    exact IntermediateField.add_mem _ hdx hdy
  · intro x hx hdx
    rw [Derivation.leibniz_inv]
    exact IntermediateField.mul_mem _
      (IntermediateField.neg_mem _
        (Subalgebra.pow_mem _ (IntermediateField.inv_mem _ hx) 2))
      hdx
  · intro x y hx hy hdx hdy
    rw [Derivation.leibniz]
    exact IntermediateField.add_mem _
      (IntermediateField.mul_mem _ hx hdy)
      (IntermediateField.mul_mem _ hy hdx)

/-- Restrict an ambient differential extension to `F⟮t⟯` when `t` is constant. -/
noncomputable def restrictAdjoin
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential F]
    (Δ : DifferentialExtension F E) (t : E) (ht : Δ.deriv t = 0) :
    DifferentialExtension F (F⟮t⟯) :=
  restrictIntermediateField Δ F⟮t⟯ (deriv_mem_adjoin_of_deriv_eq_zero Δ ht)

/-- The generator has derivative zero in the restriction to `F⟮t⟯`. -/
theorem restrictAdjoin_gen_deriv_eq_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential F]
    (Δ : DifferentialExtension F E) (t : E) (ht : Δ.deriv t = 0) :
    (restrictAdjoin Δ t ht).deriv
      (IntermediateField.AdjoinSimple.gen F t) = 0 := by
  apply Subtype.ext
  exact ht

/-- Differential extensions are equal when their derivations are equal. -/
@[ext] theorem ext {Δ₁ Δ₂ : DifferentialExtension F E}
    (h : Δ₁.deriv = Δ₂.deriv) : Δ₁ = Δ₂ :=
  Subtype.ext (Differential.ext h)

end DifferentialExtension

section Compatibility

/-- `S/R` is a differential algebra iff its derivation extends that of `R` along `algebraMap`. -/
theorem differentialAlgebra_iff_deriv_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Differential R] [Differential S] :
    DifferentialAlgebra R S ↔
      ∀ a : R, (algebraMap R S a)′ = algebraMap R S (a′) := by
  constructor
  · exact fun h => h.deriv_algebraMap
  · exact fun h => ⟨h⟩

/-- For a literal subring `R ⊆ S`, differential-algebra compatibility is `Δ(a) = D(a)`. -/
theorem differentialAlgebra_subring_iff {S : Type*} [CommRing S] [Differential S]
    (R : Subring S) [Differential R] :
    DifferentialAlgebra R S ↔ ∀ a : R, (a : S)′ = ((a′ : R) : S) := by
  rw [differentialAlgebra_iff_deriv_algebraMap]
  rfl

/-- Differential-extension compatibility is transitive along an algebra tower. -/
theorem isDifferentialExtension_trans
    {K F E : Type*} [CommRing K] [CommRing F] [CommRing E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    (ΔK : Differential K) (ΔF : Differential F) (ΔE : Differential E)
    (hKF : IsDifferentialExtensionOf ΔK ΔF)
    (hFE : IsDifferentialExtensionOf ΔF ΔE) :
    IsDifferentialExtensionOf ΔK ΔE := by
  letI : Differential K := ΔK
  letI : Differential F := ΔF
  letI : Differential E := ΔE
  letI : DifferentialAlgebra K F := hKF
  letI : DifferentialAlgebra F E := hFE
  apply differentialAlgebra_iff_deriv_algebraMap.mpr
  intro a
  rw [IsScalarTower.algebraMap_apply K F E, deriv_algebraMap, deriv_algebraMap,
    IsScalarTower.algebraMap_apply K F E]

end Compatibility

/-- `(aeval α P)' = aeval α (κ_D P) + aeval α P.derivative * α'` in a differential algebra. -/
theorem deriv_aeval_eq_extensions {F E : Type*} [Field F] [Differential F] [Field E]
    [Algebra F E] [Differential E] [DifferentialAlgebra F E] (α : E) (P : F[X]) :
    (aeval α P)′ = aeval α (Differential.mapCoeffs P) + aeval α (derivative P) * α′ :=
  Differential.deriv_aeval_eq α P

/-- Constants of the base field remain constants in a differential extension. -/
theorem deriv_algebraMap_eq_zero {F E : Type*} [Field F] [Field E] [Differential F]
    [Differential E] [Algebra F E] [DifferentialAlgebra F E] {c : F} (hc : c′ = 0) :
    (algebraMap F E c)′ = 0 := by
  rw [deriv_algebraMap, hc, map_zero]

end DeepWiki.SymbolicIntegration
