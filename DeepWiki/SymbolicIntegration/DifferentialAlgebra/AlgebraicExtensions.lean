import DeepWiki.SymbolicIntegration.DifferentialAlgebra.Extensions
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Galois.Basic

/-! # Algebraic differential extensions

Étale and separable extension theory, canonical algebraic extensions, and finite Galois
trace/norm compatibility.
-/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section DerivationalEtale

/-- Restriction sends a derivation on `E` to its composite with `F →ₐ E`. -/
def derivationRestriction {F E : Type*} [CommRing F] [CommRing E] [Algebra F E] :
    Derivation ℤ E E → Derivation ℤ F E :=
  fun d => d.compAlgebraMap F

/-- Restriction evaluates a derivation on elements coming from the base ring. -/
@[simp] theorem derivationRestriction_apply
    {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    (d : Derivation ℤ E E) (a : F) :
    derivationRestriction d a = d (algebraMap F E a) :=
  rfl

/-- A derivationally étale extension has bijective restriction on derivations. -/
def IsDerivationallyEtale (F E : Type*) [CommRing F] [CommRing E] [Algebra F E] : Prop :=
  Function.Bijective (derivationRestriction (F := F) (E := E))

/-- Explicit mutually inverse lifting data for restriction of derivations. -/
structure DerivationalEtaleData
    (F E : Type*) [CommRing F] [CommRing E] [Algebra F E] where
  /-- The chosen extension of a derivation from `F` to `E`. -/
  lift : Derivation ℤ F E → Derivation ℤ E E
  /-- Restricting a chosen lift recovers the original derivation. -/
  restriction_lift : ∀ d, derivationRestriction (lift d) = d
  /-- Lifting the restriction of a derivation recovers that derivation. -/
  lift_restriction : ∀ d, lift (derivationRestriction d) = d

namespace DerivationalEtaleData

variable {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]

/-- Explicit lifting data implies bijectivity of derivation restriction. -/
theorem toIsDerivationallyEtale (h : DerivationalEtaleData F E) :
    IsDerivationallyEtale F E := by
  constructor
  · intro d₁ d₂ hd
    rw [← h.lift_restriction d₁, ← h.lift_restriction d₂, hd]
  · intro d
    exact ⟨h.lift d, h.restriction_lift d⟩

variable [Differential F]

/-- The differential extension selected by explicit derivation-lifting data. -/
def differentialExtension (h : DerivationalEtaleData F E) :
    DifferentialExtension F E := by
  let b : Derivation ℤ F E :=
    (Algebra.linearMap F E).compDer Differential.deriv
  let d : Derivation ℤ E E := h.lift b
  let δ : Differential E := ⟨d⟩
  have hd : ∀ a : F, d (algebraMap F E a) = algebraMap F E (a′) :=
    fun a => Derivation.congr_fun (h.restriction_lift b) a
  exact ⟨δ, differentialAlgebra_iff_deriv_algebraMap.mpr hd⟩

/-- Explicit lifting data gives a choice-free unique differential extension. -/
@[reducible] def uniqueDifferentialExtension (h : DerivationalEtaleData F E) :
    Unique (DifferentialExtension F E) where
  default := h.differentialExtension
  uniq Γ := by
    apply DifferentialExtension.ext
    apply h.toIsDerivationallyEtale.1
    ext a
    exact (Γ.deriv_algebraMap a).trans (h.differentialExtension.deriv_algebraMap a).symm

end DerivationalEtaleData

/-- A derivationally étale extension admits a unique derivation extending the base derivation. -/
theorem existsUnique_derivation_of_isDerivationallyEtale
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    (h : IsDerivationallyEtale F E) :
    ∃! d : Derivation ℤ E E,
      ∀ a : F, d (algebraMap F E a) = algebraMap F E (a′) := by
  let b : Derivation ℤ F E :=
    (Algebra.linearMap F E).compDer Differential.deriv
  obtain ⟨d, hd⟩ := h.2 b
  refine ⟨d, fun a => Derivation.congr_fun hd a, fun e he => ?_⟩
  apply h.1
  exact Derivation.ext fun a => (he a).trans (Derivation.congr_fun hd a).symm

/-- A derivationally étale algebra has a unique compatible differential structure. -/
theorem existsUnique_differentialExtension_of_isDerivationallyEtale
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    (h : IsDerivationallyEtale F E) :
    ∃! Δ : Differential E, IsDifferentialExtension F E Δ := by
  obtain ⟨d, hd, huniq⟩ := existsUnique_derivation_of_isDerivationallyEtale h
  let Δ : Differential E := ⟨d⟩
  refine ⟨Δ, differentialAlgebra_iff_deriv_algebraMap.mpr hd, ?_⟩
  intro Γ hΓ
  apply Differential.ext
  apply huniq Γ.deriv
  exact hΓ.deriv_algebraMap

example
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    (h : IsDerivationallyEtale F E) :
    ∃! Δ : Differential E, IsDifferentialExtension F E Δ :=
  existsUnique_differentialExtension_of_isDerivationallyEtale h

/-- A derivationally étale algebra admits a compatible differential extension. -/
theorem nonempty_differentialExtension_of_isDerivationallyEtale
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    (h : IsDerivationallyEtale F E) :
    Nonempty (DifferentialExtension F E) := by
  obtain ⟨d, hd, _⟩ := existsUnique_derivation_of_isDerivationallyEtale h
  letI δ : Differential E := ⟨d⟩
  exact ⟨⟨δ, differentialAlgebra_iff_deriv_algebraMap.mpr hd⟩⟩

/-- Compatible differential extensions of a derivationally étale algebra are subsingleton. -/
theorem subsingleton_differentialExtension_of_isDerivationallyEtale
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    (h : IsDerivationallyEtale F E) :
    Subsingleton (DifferentialExtension F E) := by
  constructor
  intro Δ Γ
  apply DifferentialExtension.ext
  apply h.1
  ext a
  exact (Δ.deriv_algebraMap a).trans (Γ.deriv_algebraMap a).symm

end DerivationalEtale

section Separable

/-- A derivation into `E` encoded as a ring map into a trivial square-zero extension. -/
private def derivationTrivSqZeroRingHom
    {F E : Type*} [Field F] [Field E] [Algebra F E] (d : Derivation ℤ F E) :
    F →+* TrivSqZeroExt E E where
  toFun a := (algebraMap F E a, d a)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, Algebra.smul_def, mul_comm]

/-- Formal étaleness implies bijective restriction on derivations. -/
theorem isDerivationallyEtale_of_formallyEtale
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.FormallyEtale F E] :
    IsDerivationallyEtale F E := by
  constructor
  · intro d₁ d₂ hres
    let d₀ : Derivation ℤ F E := derivationRestriction d₁
    letI : Algebra F (TrivSqZeroExt E E) :=
      (derivationTrivSqZeroRingHom d₀).toAlgebra
    let I : Ideal (TrivSqZeroExt E E) := TrivSqZeroExt.kerIdeal E E
    let g₁ : E →ₐ[F] TrivSqZeroExt E E :=
      { toFun := fun x => (x, d₁ x)
        map_one' := by ext <;> simp
        map_mul' := by intro x y; ext <;> simp [Derivation.leibniz, mul_comm]
        map_zero' := by ext <;> simp
        map_add' := by intro x y; ext <;> simp
        commutes' := fun a => by
          ext
          · rfl
          · rfl }
    let g₂ : E →ₐ[F] TrivSqZeroExt E E :=
      { toFun := fun x => (x, d₂ x)
        map_one' := by ext <;> simp
        map_mul' := by intro x y; ext <;> simp [Derivation.leibniz, mul_comm]
        map_zero' := by ext <;> simp
        map_add' := by intro x y; ext <;> simp
        commutes' := fun a => by
          ext
          · rfl
          · exact (Derivation.congr_fun hres a).symm }
    have hcomp :
        (Ideal.Quotient.mkₐ F I).comp g₁ = (Ideal.Quotient.mkₐ F I).comp g₂ := by
      ext x
      apply Ideal.Quotient.eq.mpr
      change TrivSqZeroExt.fst (g₁ x - g₂ x) = 0
      simp [g₁, g₂]
    have hg : g₁ = g₂ :=
      (Algebra.FormallyEtale.comp_bijective F E I
        (TrivSqZeroExt.kerIdeal_sq E E)).1 hcomp
    ext x
    exact congr_arg (fun g : E →ₐ[F] TrivSqZeroExt E E => (g x).snd) hg
  · intro d₀
    let I : Ideal (TrivSqZeroExt E E) := TrivSqZeroExt.kerIdeal E E
    letI : Algebra F (TrivSqZeroExt E E) :=
      (derivationTrivSqZeroRingHom d₀).toAlgebra
    let qinl : E →ₐ[F] (TrivSqZeroExt E E) ⧸ I :=
      { toFun := fun x => Ideal.Quotient.mk I (TrivSqZeroExt.inl x)
        map_one' := by simp [I]
        map_mul' := by intro x y; simp [I]
        map_zero' := by simp [I]
        map_add' := by intro x y; simp [I]
        commutes' := fun a => by
          apply Ideal.Quotient.eq.mpr
          change TrivSqZeroExt.fst
            (TrivSqZeroExt.inl (algebraMap F E a) -
              algebraMap F (TrivSqZeroExt E E) a) = 0
          rw [show algebraMap F (TrivSqZeroExt E E) a =
            (algebraMap F E a, d₀ a) from rfl]
          simp only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl,
            TrivSqZeroExt.fst_mk, sub_self] }
    obtain ⟨g, hg⟩ :=
      (Algebra.FormallyEtale.comp_bijective F E I
        (TrivSqZeroExt.kerIdeal_sq E E)).2 qinl
    have hfst (x : E) : (g x).fst = x := by
      have hx := AlgHom.congr_fun hg x
      change Ideal.Quotient.mk I (g x) =
        Ideal.Quotient.mk I (TrivSqZeroExt.inl x) at hx
      rw [Ideal.Quotient.eq] at hx
      change TrivSqZeroExt.fst (g x - TrivSqZeroExt.inl x) = 0 at hx
      rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl] at hx
      exact sub_eq_zero.mp hx
    let dAdd : E →+ E :=
      { toFun := fun x => (g x).snd
        map_zero' := by rw [map_zero]; exact TrivSqZeroExt.snd_zero
        map_add' := fun x y => by rw [map_add]; exact TrivSqZeroExt.snd_add _ _ }
    let d : Derivation ℤ E E := Derivation.mk' dAdd.toIntLinearMap fun x y => by
      change (g (x * y)).snd = x * (g y).snd + y * (g x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
      simp [mul_comm]
    refine ⟨d, ?_⟩
    ext a
    change (g (algebraMap F E a)).snd = d₀ a
    rw [g.commutes]
    rfl

/-- Classically, finite separability implies bijective restriction of derivations. -/
theorem isDerivationallyEtale_of_finiteSeparable
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    IsDerivationallyEtale F E := by
  letI : Algebra.FormallyEtale F E :=
    Algebra.FormallyEtale.of_isSeparable_aux F E
  exact isDerivationallyEtale_of_formallyEtale

/-- Formal étaleness extends a base differential through a square-zero lift. -/
noncomputable def differentialExtensionOfFormallyEtale
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    [Algebra.FormallyEtale F E] :
    DifferentialExtension F E := by
  have h : ∃! d : Derivation ℤ E E,
      ∀ a : F, d (algebraMap F E a) = algebraMap F E (a′) :=
    existsUnique_derivation_of_isDerivationallyEtale
      isDerivationallyEtale_of_formallyEtale
  let d : Derivation ℤ E E := Classical.choose h.exists
  have hd : ∀ a : F, d (algebraMap F E a) = algebraMap F E (a′) :=
    Classical.choose_spec h.exists
  let δ : Differential E := ⟨d⟩
  exact ⟨δ, differentialAlgebra_iff_deriv_algebraMap.mpr hd⟩

/-- A possibly infinite separable extension has a differential extension by classical gluing. -/
noncomputable def differentialExtensionSeparable
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] :
    DifferentialExtension F E := by
  letI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  exact differentialExtensionOfFormallyEtale

/-- Any two differential extensions along a separable algebraic extension are equal. -/
theorem differentialExtension_separable_unique
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] (Δ₁ Δ₂ : DifferentialExtension F E) :
    Δ₁ = Δ₂ := by
  apply DifferentialExtension.ext
  ext x
  let p := minpoly F x
  have h₁ : aeval x (Differential.mapCoeffs p) +
      aeval x (derivative p) * Δ₁.deriv x = 0 := by
    letI : Differential E := Δ₁.toDifferential
    haveI : DifferentialAlgebra F E := Δ₁.differentialAlgebra
    rw [← deriv_aeval_eq_extensions, minpoly.aeval, map_zero]
  have h₂ : aeval x (Differential.mapCoeffs p) +
      aeval x (derivative p) * Δ₂.deriv x = 0 := by
    letI : Differential E := Δ₂.toDifferential
    haveI : DifferentialAlgebra F E := Δ₂.differentialAlgebra
    rw [← deriv_aeval_eq_extensions, minpoly.aeval, map_zero]
  have hp : aeval x (derivative p) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable F x).aeval_derivative_ne_zero (minpoly.aeval F x)
  apply mul_left_cancel₀ hp
  exact add_left_cancel (h₁.trans h₂.symm)

/-- Classically, a finite separable extension has a unique compatible differential structure. -/
theorem existsUnique_differentialExtension_finiteSeparable
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃! Δ : Differential E, IsDifferentialExtension F E Δ :=
  existsUnique_differentialExtension_of_isDerivationallyEtale
    isDerivationallyEtale_of_finiteSeparable

example
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃! Δ : Differential E, IsDifferentialExtension F E Δ :=
  existsUnique_differentialExtension_finiteSeparable

/-- Classically, a separable algebraic extension has a unique differential extension. -/
theorem existsUnique_differentialExtension_separable
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] :
    ∃! Δ : Differential E, IsDifferentialExtension F E Δ := by
  let Δ : DifferentialExtension F E := differentialExtensionSeparable
  refine ⟨Δ.toDifferential, Δ.differentialAlgebra, ?_⟩
  intro Γ hΓ
  have h :
      (⟨Γ, hΓ⟩ : DifferentialExtension F E) = Δ :=
    differentialExtension_separable_unique ⟨Γ, hΓ⟩ Δ
  exact congr_arg DifferentialExtension.toDifferential h

example
    {F E : Type*} [Field F] [Differential F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] :
    ∃! Δ : Differential E, IsDifferentialExtension F E Δ :=
  existsUnique_differentialExtension_separable

end Separable

section Algebraic

/-- The finite-dimensional algebraic differential structure on `E/F` in characteristic zero. -/
@[reducible]
noncomputable def differentialAlgebraic {F E : Type*} [Field F] [Differential F] [CharZero F]
    [Field E] [Algebra F E] [FiniteDimensional F E] : Differential E :=
  Differential.differentialFiniteDimensional F E

/-- The algebraic differential structure on `E` is compatible with the derivation on `F`. -/
theorem differentialAlgebra_algebraic {F E : Type*} [Field F] [Differential F] [CharZero F]
    [Field E] [Algebra F E] [FiniteDimensional F E] :
    letI := differentialAlgebraic (F := F) (E := E)
  DifferentialAlgebra F E :=
  Differential.differentialAlgebraFiniteDimensional

/-- The canonical differential extension on a finite-dimensional algebraic extension. -/
noncomputable def differentialExtensionAlgebraic
    {F E : Type*} [Field F] [Differential F]
    [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    DifferentialExtension F E :=
  ⟨differentialAlgebraic (F := F) (E := E),
    differentialAlgebra_algebraic (F := F) (E := E)⟩

/-- Any two differential extensions on a finite-dimensional algebraic extension are equal. -/
theorem differentialExtension_algebraic_unique
    {F E : Type*} [Field F] [Differential F] [CharZero F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    (Δ₁ Δ₂ : DifferentialExtension F E) : Δ₁ = Δ₂ :=
  (Differential.uniqueDifferentialAlgebraFiniteDimensional (F := F) (K := E)).uniq Δ₁ |>.trans
    ((Differential.uniqueDifferentialAlgebraFiniteDimensional (F := F) (K := E)).uniq Δ₂).symm

/-- A finite-dimensional algebraic extension has a unique differential extension structure. -/
@[reducible] noncomputable def uniqueDifferentialExtension_algebraic
    {F E : Type*} [Field F] [Differential F] [CharZero F]
    [Field E] [Algebra F E] [FiniteDimensional F E] :
    Unique (DifferentialExtension F E) :=
  Differential.uniqueDifferentialAlgebraFiniteDimensional

end Algebraic

section Automorphism

/-- A base-field embedding from a separable differential extension preserves derivation. -/
theorem isDifferentialExtension_algHom_of_isSeparable
    {F E L : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [Algebra.IsSeparable F E]
    (D : Differential F) (ΔE : Differential E) (ΔL : Differential L)
    (hE : @IsDifferentialExtension F E _ _ _ D ΔE)
    (hL : @IsDifferentialExtension F L _ _ _ D ΔL)
    (f : E →ₐ[F] L) :
    letI : Algebra E L := f.toRingHom.toAlgebra
    @IsDifferentialExtension E L _ _ _ ΔE ΔL := by
  letI : Differential F := D
  letI : Differential E := ΔE
  letI : Differential L := ΔL
  letI : DifferentialAlgebra F E := hE
  letI : DifferentialAlgebra F L := hL
  letI : Algebra E L := f.toRingHom.toAlgebra
  apply differentialAlgebra_iff_deriv_algebraMap.mpr
  intro x
  exact (Differential.algHom_deriv' f f.injective x).symm

/-- An `F`-algebra automorphism of a separable differential extension commutes with derivation. -/
theorem algEquiv_comm_deriv {F E : Type*} [Field F] [Differential F] [Field E]
    [Differential E] [Algebra F E] [DifferentialAlgebra F E] [Algebra.IsSeparable F E]
    (σ : E ≃ₐ[F] E) (a : E) : σ (a′) = (σ a)′ :=
  Differential.algEquiv_deriv' σ a

end Automorphism

section TraceNorm

/-- Trace commutes with derivation on a finite Galois differential extension. -/
theorem deriv_trace_eq_trace_deriv {F E : Type*} [Field F] [Differential F] [Field E]
    [Differential E] [Algebra F E] [DifferentialAlgebra F E] [FiniteDimensional F E]
    [IsGalois F E] (a : E) :
    (Algebra.trace F E a)′ = Algebra.trace F E (a′) := by
  apply FaithfulSMul.algebraMap_injective F E
  rw [← deriv_algebraMap, trace_eq_sum_automorphisms,
    trace_eq_sum_automorphisms, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← algEquiv_comm_deriv σ a]

/-- The trace of `a' / a` is the logarithmic derivative of the norm of `a`. -/
theorem trace_logDeriv_eq_logDeriv_norm {F E : Type*} [Field F] [Differential F] [Field E]
    [Differential E] [Algebra F E] [DifferentialAlgebra F E] [FiniteDimensional F E]
    [IsGalois F E] (a : E) (ha : a ≠ 0) :
    Algebra.trace F E (a′ / a) = (Algebra.norm F a)′ / Algebra.norm F a := by
  have hσne : ∀ σ : E ≃ₐ[F] E, σ a ≠ 0 := fun σ => by
    rw [ne_eq, map_eq_zero_iff _ σ.injective]; exact ha
  apply FaithfulSMul.algebraMap_injective F E
  -- LHS: `algebraMap (Tr(a'/a)) = ∑_σ σ(a'/a) = ∑_σ (σ a)'/(σ a)`.
  have hlhs : algebraMap F E (Algebra.trace F E (a′ / a)) = ∑ σ : E ≃ₐ[F] E, (σ a)′ / σ a := by
    rw [trace_eq_sum_automorphisms]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_div₀, algEquiv_comm_deriv σ a]
  -- RHS: `algebraMap (D(N a)/N a) = logDeriv (algebraMap (N a)) = logDeriv (∏_σ σ a)`.
  have hrhs : algebraMap F E ((Algebra.norm F a)′ / Algebra.norm F a)
      = ∑ σ : E ≃ₐ[F] E, (σ a)′ / σ a := by
    have hstep : Differential.logDeriv ((algebraMap F E) (Algebra.norm F a))
        = ∑ σ : E ≃ₐ[F] E, (σ a)′ / σ a := by
      rw [Algebra.norm_eq_prod_automorphisms,
        Differential.logDeriv_prod _ Finset.univ (fun σ : E ≃ₐ[F] E => σ a) (fun σ _ => hσne σ)]
      rfl
    rw [map_div₀, ← deriv_algebraMap]
    exact hstep
  rw [hlhs, hrhs]

end TraceNorm

section AlgebraicClosure

/-- A finite intermediate field has a unique differential extension structure over `F`. -/
@[reducible] noncomputable def uniqueDifferentialExtension_intermediateField
    {F K : Type*} [Field F]
    [Differential F] [CharZero F] [Field K] [Algebra F K] (B : IntermediateField F K)
    [FiniteDimensional F B] :
    Unique (DifferentialExtension F B) :=
  uniqueDifferentialExtension_algebraic

/-- A differential extension of `F` is also a differential extension of a finite intermediate field. -/
theorem differentialAlgebra_intermediateField_tower {F K : Type*} [Field F] [Differential F]
    [CharZero F] [Field K] [Algebra F K] [Differential K] [DifferentialAlgebra F K]
    (B : IntermediateField F K) [FiniteDimensional F B] : DifferentialAlgebra B K :=
  inferInstance

end AlgebraicClosure

end DeepWiki.SymbolicIntegration
