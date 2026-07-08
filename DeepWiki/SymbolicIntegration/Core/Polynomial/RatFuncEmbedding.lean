import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Rational-function polynomial embeddings

Small API for the embeddings `K → RatFunc K` and `K[X] → RatFunc K`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- The polynomial embedding into `RatFunc K` preserves nonzero polynomials. -/
theorem ratFunc_algebraMap_ne_zero {q : K[X]} (hq : q ≠ 0) :
    algebraMap K[X] (RatFunc K) q ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hq

/-- `algebraMap K (RatFunc K) b = algebraMap K[X] (RatFunc K) (C b)`. -/
theorem ratFunc_algebraMap_eq_algebraMap_C (b : K) :
    algebraMap K (RatFunc K) b = algebraMap K[X] (RatFunc K) (Polynomial.C b) := by
  rw [IsScalarTower.algebraMap_eq K K[X] (RatFunc K)]
  simp [Polynomial.algebraMap_eq]

/-- A polynomial image in `RatFunc K` lies in `range (algebraMap K)` iff it is constant. -/
theorem ratFunc_algebraMap_poly_mem_range_iff (p : K[X]) :
    algebraMap K[X] (RatFunc K) p ∈ (algebraMap K (RatFunc K)).range
      ↔ ∃ b : K, p = Polynomial.C b := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply FaithfulSMul.algebraMap_injective K[X] (RatFunc K)
    rw [← ratFunc_algebraMap_eq_algebraMap_C, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨b, (ratFunc_algebraMap_eq_algebraMap_C b).symm⟩

end DeepWiki.SymbolicIntegration
