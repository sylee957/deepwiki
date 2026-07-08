import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.Core.Polynomial.Diophantine
import Mathlib.RingTheory.EuclideanDomain

/-! # Partial fractions from polynomial Diophantine solvers

Rational-function partial-fraction decompositions built from the polynomial
Diophantine solver.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open Classical in
/-- For coprime nonzero `P` and `Q`, `A / (P * Q)` splits into `B / Q + C / P`. -/
theorem ratFunc_partialFraction_coprime {P Q A : K[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPQ : IsCoprime P Q) :
    algebraMap K[X] (RatFunc K) A
        / (algebraMap K[X] (RatFunc K) P * algebraMap K[X] (RatFunc K) Q)
      = algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).1 / algebraMap K[X] (RatFunc K) Q
        + algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).2 / algebraMap K[X] (RatFunc K) P := by
  have hp : algebraMap K[X] (RatFunc K) P ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hP
  have hq : algebraMap K[X] (RatFunc K) Q ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hQ
  have hspec : algebraMap K[X] (RatFunc K) A
      = algebraMap K[X] (RatFunc K) P * algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).1
        + algebraMap K[X] (RatFunc K) Q * algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).2 := by
    rw [← map_mul, ← map_mul, ← map_add, diophantineSolve_spec hPQ A]
  rw [hspec]; field_simp

open Classical in
/-- A nonempty product of pairwise-coprime nonzero factors admits a partial-fraction decomposition. -/
theorem ratFunc_partialFraction_prod {ι : Type*} (P : ι → K[X]) :
    ∀ (s : Finset ι), s.Nonempty → (∀ i ∈ s, P i ≠ 0) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (P i) (P j)) → ∀ (A : K[X]),
      ∃ B : ι → K[X],
        algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (P i)
          = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (B i) / algebraMap K[X] (RatFunc K) (P i) := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact fun _ _ A => ⟨fun _ => A, by simp⟩
  | cons a s ha hs ih =>
      intro hP hcop A
      have hmem : ∀ i ∈ s, i ∈ Finset.cons a s ha := fun i hi => Finset.mem_cons.mpr (Or.inr hi)
      have hPa : P a ≠ 0 := hP a (Finset.mem_cons_self a s)
      have hP' : ∀ i ∈ s, P i ≠ 0 := fun i hi => hP i (hmem i hi)
      have hcop' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (P i) (P j) :=
        fun i hi j hj hij => hcop i (hmem i hi) j (hmem j hj) hij
      have hQ0 : (∏ i ∈ s, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hP'
      have hcopaQ : IsCoprime (P a) (∏ i ∈ s, P i) :=
        IsCoprime.prod_right fun i hi =>
          hcop a (Finset.mem_cons_self a s) i (hmem i hi) (by rintro rfl; exact ha hi)
      obtain ⟨B', hB'⟩ := ih hP' hcop' (diophantineSolve (P a) (∏ i ∈ s, P i) A).1
      refine ⟨fun i => if i = a then (diophantineSolve (P a) (∏ i ∈ s, P i) A).2 else B' i, ?_⟩
      have hsplit := ratFunc_partialFraction_coprime (A := A) hPa hQ0 hcopaQ
      rw [map_prod] at hsplit
      have hsumeq : (∑ i ∈ s, algebraMap K[X] (RatFunc K)
            (if i = a then (diophantineSolve (P a) (∏ i ∈ s, P i) A).2 else B' i)
            / algebraMap K[X] (RatFunc K) (P i))
          = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (B' i) / algebraMap K[X] (RatFunc K) (P i) :=
        Finset.sum_congr rfl fun i hi => by
          rw [if_neg (fun (h : i = a) => ha (h ▸ hi))]
      rw [Finset.prod_cons, Finset.sum_cons]
      dsimp only
      rw [hsumeq, if_pos rfl, hsplit, hB', add_comm]

end DeepWiki.SymbolicIntegration
