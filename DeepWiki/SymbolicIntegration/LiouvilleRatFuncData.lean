import Mathlib.FieldTheory.Differential.Liouville
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Liouville data over rational function fields

Shared transport from rational-function-field data to the existential conclusion of `IsLiouville`.
-/

open scoped Differential
open Differential

namespace DeepWiki.SymbolicIntegration

variable {F : Type*} [Field F] [Differential F]

/-- Rational-function-field data over `F` yields the existential conclusion of `IsLiouville`. -/
theorem isLiouville_conclusion_of_ratFuncData [Differential (RatFunc F)]
    [DifferentialAlgebra F (RatFunc F)]
    (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
    (w₀ : ι → F) (v₀ : F)
    (h : algebraMap F (RatFunc F) a
          = ∑ x, algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x))
              + (algebraMap F (RatFunc F) v₀)′) :
    ∃ (ι₀ : Type) (_ : Fintype ι₀) (c₀ : ι₀ → F) (_ : ∀ x, (c₀ x)′ = 0)
      (u₀ : ι₀ → F) (v₀' : F), a = ∑ x, c₀ x * logDeriv (u₀ x) + v₀'′ := by
  refine ⟨ι, inferInstance, c, hc, w₀, v₀, ?_⟩
  apply FaithfulSMul.algebraMap_injective F (RatFunc F)
  rw [map_add, map_sum, ← deriv_algebraMap]
  have hsum : ∀ x, (algebraMap F (RatFunc F)) (c x * logDeriv (w₀ x))
      = algebraMap F (RatFunc F) (c x) * logDeriv (algebraMap F (RatFunc F) (w₀ x)) := by
    intro x
    rw [map_mul, ← logDeriv_algebraMap]
  simp_rw [hsum]
  exact h

end DeepWiki.SymbolicIntegration
