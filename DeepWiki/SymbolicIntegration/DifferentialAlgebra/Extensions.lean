import DeepWiki.SymbolicIntegration.DifferentialAlgebra.Basic

/-! # Differential extensions

Bundled differential extensions and compatibility with base derivations.
-/

open scoped Differential
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
