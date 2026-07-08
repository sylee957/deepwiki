import DeepWiki.SymbolicIntegration.RationalIntegration
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Polynomial.Degree.Units

/-! # Polynomial Diophantine solvers for rational integration

Extended-Euclidean Bézout solvers and their degree-reduced variant used by Hermite
reduction, partial fractions, and local-principal-part constructions. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open Classical in
/-- Extended-Euclidean solver returning cofactors for `a * B + b * C = c` when `a` and `b` are coprime. -/
noncomputable def diophantineSolve (a b c : K[X]) : K[X] × K[X] :=
  (c * EuclideanDomain.gcdA a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹,
   c * EuclideanDomain.gcdB a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹)

open Classical in
/-- For coprime `a` and `b`, `diophantineSolve a b c` solves `a * B + b * C = c`. -/
theorem diophantineSolve_spec {a b : K[X]} (hab : IsCoprime a b) (c : K[X]) :
    a * (diophantineSolve a b c).1 + b * (diophantineSolve a b c).2 = c := by
  have hg : IsUnit (EuclideanDomain.gcd a b) := EuclideanDomain.gcd_isUnit_iff.mpr hab
  have hdeg : (EuclideanDomain.gcd a b).natDegree = 0 := natDegree_eq_zero_of_isUnit hg
  have hgC : EuclideanDomain.gcd a b = C ((EuclideanDomain.gcd a b).coeff 0) :=
    eq_C_of_natDegree_eq_zero hdeg
  have hr0 : (EuclideanDomain.gcd a b).coeff 0 ≠ 0 := fun h =>
    hg.ne_zero (by rw [hgC, h, map_zero])
  simp only [diophantineSolve]
  have step : a * (c * EuclideanDomain.gcdA a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹)
        + b * (c * EuclideanDomain.gcdB a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹)
      = c * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹
        * (a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b) := by ring
  rw [step, ← EuclideanDomain.gcd_eq_gcd_ab, mul_assoc]
  nth_rewrite 2 [hgC]
  rw [← map_mul, inv_mul_cancel₀ hr0, map_one, mul_one]

open Classical in
/-- Diophantine solver whose first cofactor is reduced modulo `b`. -/
noncomputable def diophantineSolveReduced (a b c : K[X]) : K[X] × K[X] :=
  ((diophantineSolve a b c).1 % b,
   (diophantineSolve a b c).2 + ((diophantineSolve a b c).1 / b) * a)

open Classical in
/-- For coprime `a` and `b`, `diophantineSolveReduced a b c` still solves `a * B + b * C = c`. -/
theorem diophantineSolveReduced_spec {a b : K[X]} (hab : IsCoprime a b) (c : K[X]) :
    a * (diophantineSolveReduced a b c).1 + b * (diophantineSolveReduced a b c).2 = c := by
  have hbase := diophantineSolve_spec hab c
  simp only [diophantineSolveReduced]
  have hdm : b * ((diophantineSolve a b c).1 / b) + (diophantineSolve a b c).1 % b
      = (diophantineSolve a b c).1 := EuclideanDomain.div_add_mod _ b
  linear_combination hbase + a * hdm

open Classical in
/-- The first cofactor returned by `diophantineSolveReduced` has degree below `b.degree` when `b ≠ 0`. -/
theorem diophantineSolveReduced_fst_degree_lt {a b : K[X]} (hb : b ≠ 0) (c : K[X]) :
    (diophantineSolveReduced a b c).1.degree < b.degree := by
  simp only [diophantineSolveReduced]
  exact Polynomial.degree_mod_lt _ hb

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
