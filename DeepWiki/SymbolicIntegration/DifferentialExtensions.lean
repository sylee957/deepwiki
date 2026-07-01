import DeepWiki.SymbolicIntegration.DifferentialFields
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Galois.Basic

/-! # Derivation extensions
Uniqueness and compatibility lemmas for extending derivations to fraction fields, rational-function
fields, finite algebraic extensions, and finite Galois trace/norm operations. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section FractionField
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Differential R]

/-- A derivation on a fraction field `K` of `R` is unique if it extends the derivation on `R`. -/
theorem unique_derivation_fractionRing {Δ₁ Δ₂ : Derivation ℤ K K}
    (h₁ : ∀ a : R, Δ₁ (algebraMap R K a) = algebraMap R K (a′))
    (h₂ : ∀ a : R, Δ₂ (algebraMap R K a) = algebraMap R K (a′)) : Δ₁ = Δ₂ :=
  derivation_ext_fractionRing (R := R) fun a => (h₁ a).trans (h₂ a).symm

/-- A compatible differential structure on a fraction field gives the unique extending derivation. -/
theorem existsUnique_derivation_fractionRing [Differential K] [DifferentialAlgebra R K] :
    ∃! Δ : Derivation ℤ K K, ∀ a : R, Δ (algebraMap R K a) = algebraMap R K (a′) := by
  refine ⟨Differential.deriv, fun a => ?_, fun Δ hΔ => ?_⟩
  · rw [deriv_algebraMap]
  · exact unique_derivation_fractionRing (R := R) hΔ (fun a => by rw [deriv_algebraMap])

end FractionField

section Transcendental
variable {F : Type*} [Field F] [Differential F]

omit [Differential F] in
/-- A derivation on a fraction field of `F[X]` is determined by its values on constants and `X`. -/
theorem unique_derivation_rationalFunction {K : Type*} [Field K] [Algebra F[X] K]
    [IsFractionRing F[X] K] {Δ₁ Δ₂ : Derivation ℤ K K}
    (hC : ∀ c : F, Δ₁ (algebraMap F[X] K (C c)) = Δ₂ (algebraMap F[X] K (C c)))
    (hX : Δ₁ (algebraMap F[X] K X) = Δ₂ (algebraMap F[X] K X)) : Δ₁ = Δ₂ := by
  refine derivation_ext_fractionRing (R := F[X]) fun p => ?_
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Δ₁.leibniz, Δ₂.leibniz, ih, hX]

end Transcendental

section Algebraic
variable {F : Type*} [Field F] [Differential F] [CharZero F]
variable {E : Type*} [Field E] [Algebra F E]

omit [CharZero F] in
/-- `(aeval α P)' = aeval α (κ_D P) + aeval α P.derivative * α'` in a differential algebra. -/
theorem deriv_aeval_eq_extensions [Differential E] [DifferentialAlgebra F E] (α : E) (P : F[X]) :
    (aeval α P)′ = aeval α (Differential.mapCoeffs P) + aeval α (derivative P) * α′ :=
  Differential.deriv_aeval_eq α P

variable [FiniteDimensional F E]

/-- The finite-dimensional algebraic differential structure on `E/F` in characteristic zero. -/
@[reducible]
noncomputable def differentialAlgebraic : Differential E :=
  Differential.differentialFiniteDimensional F E

/-- The algebraic differential structure on `E` is compatible with the derivation on `F`. -/
theorem differentialAlgebra_algebraic :
    letI := differentialAlgebraic (F := F) (E := E)
    DifferentialAlgebra F E :=
  Differential.differentialAlgebraFiniteDimensional

/-- A finite-dimensional algebraic extension has at most one compatible differential structure. -/
theorem unique_differentialAlgebra_algebraic (Δ₁ Δ₂ : Differential E)
    (h₁ : @DifferentialAlgebra F E _ _ _ _ Δ₁) (h₂ : @DifferentialAlgebra F E _ _ _ _ Δ₂) :
    Δ₁ = Δ₂ := by
  have := Subtype.ext_iff.mp <|
    (Differential.uniqueDifferentialAlgebraFiniteDimensional (F := F) (K := E)).uniq ⟨Δ₁, h₁⟩
      |>.trans
      ((Differential.uniqueDifferentialAlgebraFiniteDimensional (F := F) (K := E)).uniq
        ⟨Δ₂, h₂⟩).symm
  exact this

end Algebraic

section Automorphism
variable {F : Type*} [Field F] [Differential F]
variable {E : Type*} [Field E] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
  [Algebra.IsSeparable F E]

/-- An `F`-algebra automorphism of a separable differential extension commutes with derivation. -/
theorem algEquiv_comm_deriv (σ : E ≃ₐ[F] E) (a : E) : σ (a′) = (σ a)′ :=
  Differential.algEquiv_deriv' σ a

end Automorphism

section TraceNorm
variable {F E : Type*} [Field F] [Differential F] [Field E] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- Trace commutes with derivation on a finite Galois differential extension. -/
theorem deriv_trace_eq_trace_deriv (a : E) :
    (Algebra.trace F E a)′ = Algebra.trace F E (a′) := by
  apply FaithfulSMul.algebraMap_injective F E
  rw [← deriv_algebraMap, trace_eq_sum_automorphisms,
    trace_eq_sum_automorphisms, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← algEquiv_comm_deriv σ a]

/-- The trace of `a' / a` is the logarithmic derivative of the norm of `a`. -/
theorem trace_logDeriv_eq_logDeriv_norm (a : E) (ha : a ≠ 0) :
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
variable {F : Type*} [Field F] [Differential F] [CharZero F]
variable {K : Type*} [Field K] [Algebra F K]

/-- A finite intermediate field has a unique differential structure compatible with `F`. -/
theorem existsUnique_differentialAlgebra_intermediateField (B : IntermediateField F K)
    [FiniteDimensional F B] :
    ∃! Δ : Differential B, @DifferentialAlgebra F B _ _ _ _ Δ := by
  let instB : Differential B := inferInstance
  have hinst : @DifferentialAlgebra F B _ _ _ _ instB := by
    change @DifferentialAlgebra F B _ _ _ _
      (Differential.instSubtypeMemIntermediateFieldOfFiniteDimensional B)
    infer_instance
  refine ⟨instB, hinst, ?_⟩
  intro Δ hΔ
  exact unique_differentialAlgebra_algebraic (F := F) (E := B) Δ instB hΔ hinst

/-- A differential extension of `F` is also a differential extension of a finite intermediate field. -/
theorem differentialAlgebra_intermediateField_tower [Differential K] [DifferentialAlgebra F K]
    (B : IntermediateField F K) [FiniteDimensional F B] : DifferentialAlgebra B K :=
  inferInstance

end AlgebraicClosure

end DeepWiki.SymbolicIntegration
