import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors

/-! # Rational-integration log form
Closed log-form assembly for rational functions over split squarefree denominators. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Differential in
open Classical in
/-- A sum of proper split squarefree fractions equals the grouped residue log-derivative sum. -/
theorem sum_proper_fraction_eq_logForm {ι : Type*} (s : Finset ι) (sset : ι → Finset K)
    (r : ι → K[X]) (g : RatFunc K) (p : K[X])
    (hproper : ∀ i ∈ s, (r i).degree < (sset i).card) :
    g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
        + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i)
            / algebraMap K[X] (RatFunc K) (Lagrange.nodal (sset i) id)
      = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
        + ∑ i ∈ s, ∑ a ∈ (sset i).image
            (fun α => (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id))),
            algebraMap K[X] (RatFunc K) (C a)
              * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                  (∏ α ∈ (sset i).filter
                      (fun α => (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id)) = a),
                    (X - C α))) := by
  rw [Finset.sum_congr rfl
    (fun i hi => ratFunc_eq_sum_residue_grouped (sset i) (r i) (hproper i hi))]

open scoped Differential in
open Classical in
/-- A rational function with split squarefree-power denominator admits a grouped-log derivative form. -/
theorem integrateRationalFunction_logForm [CharZero K] {ι : Type*} (s : Finset ι)
    (sset : ι → Finset K) (e : ι → ℕ) (he : ∀ i ∈ s, 1 ≤ e i)
    (hne : ∀ i ∈ s, (sset i).Nonempty)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (sset i) (sset j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
        algebraMap K[X] (RatFunc K) A
            / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (Lagrange.nodal (sset i) id) ^ e i
          = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
            + ∑ i ∈ s, ∑ a ∈ (sset i).image
                (fun α => (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id))),
                algebraMap K[X] (RatFunc K) (C a)
                  * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                      (∏ α ∈ (sset i).filter
                          (fun α =>
                            (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id)) = a),
                        (X - C α))) := by
  have hsf : ∀ i ∈ s, Squarefree (Lagrange.nodal (sset i) id) := fun i _ => by
    rw [Lagrange.nodal_eq]; exact squarefree_prod_X_sub_C (sset i)
  have hmonic : ∀ i ∈ s, (Lagrange.nodal (sset i) id).Monic := fun i _ => Lagrange.nodal_monic
  have hnd : ∀ i ∈ s, 0 < (Lagrange.nodal (sset i) id).natDegree := fun i hi => by
    rw [Lagrange.natDegree_nodal]; exact (hne i hi).card_pos
  have hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      IsCoprime (Lagrange.nodal (sset i) id) (Lagrange.nodal (sset j) id) := fun i hi j hj hij => by
    rw [Lagrange.nodal_eq, Lagrange.nodal_eq]
    exact isCoprime_prod_X_sub_C_of_disjoint (hdisj i hi j hj hij)
  obtain ⟨g, p, r, hproper, hred⟩ :=
    integrateRationalFunction_reduction_proper s (fun i => Lagrange.nodal (sset i) id) e hmonic hsf
      hnd he hcop A
  have hproper' : ∀ i ∈ s, (r i).degree < (sset i).card := fun i hi => by
    have := hproper i hi
    rwa [Lagrange.degree_nodal] at this
  refine ⟨g, p, r, ?_⟩
  rw [hred]
  exact sum_proper_fraction_eq_logForm s sset r g p hproper'

end DeepWiki.SymbolicIntegration
