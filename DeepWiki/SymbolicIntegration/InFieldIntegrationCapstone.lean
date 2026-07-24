import DeepWiki.SymbolicIntegration.InFieldIntegration

/-! # In-field integration — the constructive antiderivative
The constructive half of the recognition criterion: when `A = 0`, the Hermite quotient `g` is the
antiderivative (`inFieldIntegral g` with `(inFieldIntegral g)′ = f`), giving the decision-with-witness
`inFieldIntegrable_iff`. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- The Hermite quotient `g ∈ K[X]` viewed in `K(x)` as the antiderivative: `inFieldIntegral g =
algebraMap g`. -/
noncomputable def inFieldIntegral (g : K[X]) : RatFunc K :=
  algebraMap K[X] (RatFunc K) g

/-- `inFieldIntegral g = algebraMap g` — the antiderivative is the Hermite quotient, read in `K(x)`. -/
@[simp] theorem inFieldIntegral_eq (g : K[X]) :
    inFieldIntegral g = algebraMap K[X] (RatFunc K) g := rfl

/-- If `f = (algebraMap g)′ + A/D` with `A = 0`, then `(inFieldIntegral g)′ = f`: the Hermite quotient
`g` is an antiderivative of `f`. -/
theorem inFieldIntegral_spec {f : RatFunc K} {g A D : K[X]} (hA : A = 0)
    (hf : f = (algebraMap K[X] (RatFunc K) g)′
          + algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D) :
    (inFieldIntegral g)′ = f := by
  rw [inFieldIntegral, hf, hA, map_zero, zero_div, add_zero]

/-- For `f` with Hermite reduction `f = (algebraMap g)′ + A/D`, `f` has a rational antiderivative iff
`A = 0`, and then the Hermite quotient `g` is one (`(inFieldIntegral g)′ = f`). -/
theorem inFieldIntegrable_iff [CharZero K] {f : RatFunc K} {g A D : K[X]}
    (hD : Squarefree D) (hAD : IsCoprime A D) (hdeg : A.degree < D.degree)
    (hf : f = (algebraMap K[X] (RatFunc K) g)′
          + algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D) :
    (∃ v : RatFunc K, v′ = f) ↔ (A = 0 ∧ (inFieldIntegral g)′ = f) := by
  rw [isRationalDerivative_iff hD hAD hdeg hf]
  constructor
  · intro hA; exact ⟨hA, inFieldIntegral_spec hA hf⟩
  · exact fun h => h.1

end DeepWiki.SymbolicIntegration
