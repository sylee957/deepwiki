import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.Diophantine
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.HermitePower

/-! # Hermite reduction kernels

Prime-power Hermite reduction assembled over coprime squarefree denominator factors.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Differential in
open Classical in
/-- A sum of prime-power fractions Hermite-reduces to a derivative plus squarefree residuals. -/
theorem hermiteReduce_sum_spec [CharZero K] {ι : Type*} (s : Finset ι) (D : ι → K[X])
    (e : ι → ℕ) (A : ι → K[X]) (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i) :
    ∑ i ∈ s, algebraMap K[X] (RatFunc K) (A i) / algebraMap K[X] (RatFunc K) (D i) ^ e i
      = (∑ i ∈ s, (hermiteReducePower (D i) (e i) (A i)).1)′
        + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (hermiteReducePower (D i) (e i) (A i)).2
            / algebraMap K[X] (RatFunc K) (D i) := by
  rw [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi =>
    hermiteReducePower_spec (D i) (hD i hi) (e i) (he i hi) (A i)

open scoped Differential in
open Classical in
/-- A coprime squarefree-power denominator admits a full Hermite reduction. -/
theorem hermiteReduce_full [CharZero K] {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (D : ι → K[X]) (e : ι → ℕ) (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (g : RatFunc K) (r : ι → K[X]),
      algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = g′ + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i) / algebraMap K[X] (RatFunc K) (D i) := by
  obtain ⟨B, hB⟩ := ratFunc_partialFraction_prod (fun i => D i ^ e i) s hs
    (fun i hi => pow_ne_zero _ (hD i hi).ne_zero)
    (fun i hi j hj hij => (hcop i hi j hj hij).pow) A
  simp only [map_pow] at hB
  exact ⟨_, _, hB.trans (hermiteReduce_sum_spec s D e B hD he)⟩

end DeepWiki.SymbolicIntegration
