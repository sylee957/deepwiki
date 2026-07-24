import Mathlib.FieldTheory.Differential.Liouville

/-! # Algebraic completeness frontier predicates

Defines the abstract Liouville-form predicates and frontier interfaces used by the
algebraic completeness layer. -/

open scoped Differential
open Differential

namespace DeepWiki.SymbolicIntegration.AlgebraicCompleteness

/-! ## Algebraic-elementary predicates -/

section Predicate

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- `IsAlgebraicElementary F K f` gives a Liouville form for `f` over `K`. -/
def IsAlgebraicElementary (f : F) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → K) (v : K),
    (algebraMap F K f) = ∑ x, (algebraMap F K (c x)) * logDeriv (u x) + v′

end Predicate

/-! ## Finite-dimensional descent -/

section FiniteDimDescent

variable (F : Type*) (K : Type*) [Field F] [Field K] [CharZero F]
variable [Differential F] [Differential K] [Algebra F K] [DifferentialAlgebra F K]

/-- Elementary over a finite-dimensional extension `K / F` descends to `F`. -/
theorem elementary_base_of_elementary_finiteDim [FiniteDimensional F K] (f : F)
    (h : IsAlgebraicElementary F K f) : IsAlgebraicElementary F F f := by
  haveI : IsLiouville F K := isLiouville_of_finiteDimensional
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := h
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville f ι c hc u v hrep
  exact ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-- Base non-elementarity propagates up a finite-dimensional extension `K / F`. -/
theorem not_elementary_extension_of_not_elementary_base_alg [FiniteDimensional F K] (f : F)
    (h : ¬ IsAlgebraicElementary F F f) : ¬ IsAlgebraicElementary F K f :=
  fun hK => h (elementary_base_of_elementary_finiteDim F K f hK)

end FiniteDimDescent

/-! ## Liouville and rational-part frontier interfaces -/

section Frontier

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- `AlgebraicLiouvilleFrontier F` propagates base non-elementarity through Liouville extensions. -/
def AlgebraicLiouvilleFrontier : Prop :=
  ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K] [IsLiouville F K]
    (f : F), ¬ IsAlgebraicElementary F F f → ¬ IsAlgebraicElementary F K f

omit [CharZero F] in
/-- `AlgebraicLiouvilleFrontier F` holds for each supplied Liouville extension. -/
theorem algebraicLiouville_single_extension : AlgebraicLiouvilleFrontier F := by
  intro K _ _ _ _ _ f h hK
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := hK
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville f ι c hc u v hrep
  exact h ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-! ### Rational parts -/

omit [CharZero F] in
/-- The derivative `v′` is algebraic-elementary via the empty logarithmic family. -/
theorem ratPart_isAlgebraicElementary (v : F) : IsAlgebraicElementary F F (v′) := by
  refine ⟨Empty, inferInstance, Empty.elim, fun x => x.elim, Empty.elim, v, ?_⟩
  simp only [Algebra.algebraMap_self_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_add]

/-- `RationalPartExhaustivenessFrontier F` reduces `f - v′` to a purely logarithmic form. -/
def RationalPartExhaustivenessFrontier : Prop :=
  ∀ (f v : F), IsAlgebraicElementary F F f →
    IsAlgebraicElementary F F (f - v′) →
      ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → F),
        (f - v′) = ∑ x, c x * logDeriv (u x)

end Frontier

/-! ## Axiom audit -/


/-! ### Axiom audit -/

#print axioms elementary_base_of_elementary_finiteDim
#print axioms not_elementary_extension_of_not_elementary_base_alg
#print axioms ratPart_isAlgebraicElementary
#print axioms algebraicLiouville_single_extension

end DeepWiki.SymbolicIntegration.AlgebraicCompleteness
