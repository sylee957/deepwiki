import DeepWiki.SymbolicIntegration.DifferentialAlgebra
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Galois.Basic

/-! # Derivation extensions
Uniqueness and compatibility lemmas for algebraic differential extensions, intermediate fields,
and finite Galois trace/norm operations. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section Algebraic

/-- `(aeval α P)' = aeval α (κ_D P) + aeval α P.derivative * α'` in a differential algebra. -/
theorem deriv_aeval_eq_extensions {F E : Type*} [Field F] [Differential F] [Field E]
    [Algebra F E] [Differential E] [DifferentialAlgebra F E] (α : E) (P : F[X]) :
    (aeval α P)′ = aeval α (Differential.mapCoeffs P) + aeval α (derivative P) * α′ :=
  Differential.deriv_aeval_eq α P

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

/-- A finite-dimensional algebraic extension has at most one compatible differential structure. -/
theorem unique_differentialAlgebra_algebraic {F E : Type*} [Field F] [Differential F]
    [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] (Δ₁ Δ₂ : Differential E)
    (h₁ : @DifferentialAlgebra F E _ _ _ _ Δ₁) (h₂ : @DifferentialAlgebra F E _ _ _ _ Δ₂) :
    Δ₁ = Δ₂ := by
  have := Subtype.ext_iff.mp <|
    (Differential.uniqueDifferentialAlgebraFiniteDimensional (F := F) (K := E)).uniq ⟨Δ₁, h₁⟩
      |>.trans
      ((Differential.uniqueDifferentialAlgebraFiniteDimensional (F := F) (K := E)).uniq
        ⟨Δ₂, h₂⟩).symm
  exact this

/-- A finite-dimensional algebraic extension has a unique compatible differential structure. -/
theorem existsUnique_differentialAlgebra_algebraic {F E : Type*} [Field F] [Differential F]
    [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    ∃! Δ : Differential E, @DifferentialAlgebra F E _ _ _ _ Δ := by
  let Δ₀ := differentialAlgebraic (F := F) (E := E)
  have hΔ₀ : @DifferentialAlgebra F E _ _ _ _ Δ₀ :=
    differentialAlgebra_algebraic (F := F) (E := E)
  refine ⟨Δ₀, hΔ₀, ?_⟩
  intro Δ hΔ
  exact unique_differentialAlgebra_algebraic (F := F) (E := E) Δ Δ₀ hΔ hΔ₀

example {F E : Type*} [Field F] [Differential F] [CharZero F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : ∃! Δ : Differential E, @DifferentialAlgebra F E _ _ _ _ Δ :=
  existsUnique_differentialAlgebra_algebraic (F := F) (E := E)

end Algebraic

section Automorphism

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

/-- A finite intermediate field has a unique differential structure compatible with `F`. -/
theorem existsUnique_differentialAlgebra_intermediateField {F K : Type*} [Field F]
    [Differential F] [CharZero F] [Field K] [Algebra F K] (B : IntermediateField F K)
    [FiniteDimensional F B] :
    ∃! Δ : Differential B, @DifferentialAlgebra F B _ _ _ _ Δ := by
  exact existsUnique_differentialAlgebra_algebraic (F := F) (E := B)

/-- A differential extension of `F` is also a differential extension of a finite intermediate field. -/
theorem differentialAlgebra_intermediateField_tower {F K : Type*} [Field F] [Differential F]
    [CharZero F] [Field K] [Algebra F K] [Differential K] [DifferentialAlgebra F K]
    (B : IntermediateField F K) [FiniteDimensional F B] : DifferentialAlgebra B K :=
  inferInstance

end AlgebraicClosure

end DeepWiki.SymbolicIntegration
