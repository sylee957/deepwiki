import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionDerivative
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Radical.Basic

/-! # Horowitz-Ostrogradsky denominator splitting

Denominator splitting and the rational-function identity for one-shot rational-part extraction.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## Horowitz-Ostrogradsky Split
Denominator splitting and rational-function identity for one-shot rational-part extraction. -/

open Classical in
/-- Horowitz-Ostrogradsky denominator split `(gcd(D, D'), D / gcd(D, D'))`. -/
noncomputable def hoSplit (D : K[X]) : K[X] × K[X] :=
  (gcd D (derivative D), D / gcd D (derivative D))

open Classical in
/-- `gcd(D, D') ≠ 0` for `D ≠ 0`. -/
private theorem gcd_derivative_ne_zero {D : K[X]} (hD : D ≠ 0) : gcd D (derivative D) ≠ 0 :=
  fun h => hD (zero_dvd_iff.mp (h ▸ gcd_dvd_left D (derivative D)))

open Classical in
/-- The Horowitz-Ostrogradsky split factors `D` when `D ≠ 0`. -/
theorem hoSplit_mul (D : K[X]) (hD : D ≠ 0) : (hoSplit D).1 * (hoSplit D).2 = D :=
  EuclideanDomain.mul_div_cancel' (gcd_derivative_ne_zero hD) (gcd_dvd_left _ _)

open Classical in
/-- In characteristic zero, the second component of `hoSplit D` is squarefree. -/
theorem hoSplit_snd_squarefree [CharZero K] (D : K[X]) (hD : D ≠ 0) :
    Squarefree (hoSplit D).2 := by
  have hprim : D.IsPrimitive := (isPrimitive_iff_ne_zero D).mpr hD
  have hpp : D.primPart = D := by
    have h := eq_C_content_mul_primPart D
    rw [hprim.content_eq_one, map_one, one_mul] at h; exact h.symm
  have hppne : D.primPart ≠ 0 := by rw [hpp]; exact hD
  have hmul : gcd D (derivative D) * (hoSplit D).2 = D := hoSplit_mul D hD
  have h1 : Associated (squarefreePart D * deflation D 1) D := by
    have := squarefreePart_mul_deflation D hppne; rwa [hpp] at this
  have h2 : Associated (gcd D (derivative D)) (deflation D 1) := by
    have := deflation_one_eq_gcd D hppne; rwa [hpp] at this
  -- cancel the common factor gcd ~ deflation to get D* ~ squarefreePart
  have hcomb : Associated (gcd D (derivative D) * (hoSplit D).2)
      (deflation D 1 * squarefreePart D) := by
    rw [hmul, mul_comm (deflation D 1) (squarefreePart D)]; exact h1.symm
  have hAD : Associated (hoSplit D).2 (squarefreePart D) :=
    Associated.of_mul_left hcomb h2 (gcd_derivative_ne_zero hD)
  have hsqfp : squarefreePart D = UniqueFactorizationMonoid.radical D := by
    unfold squarefreePart UniqueFactorizationMonoid.radical UniqueFactorizationMonoid.primeFactors
    rw [hpp]; congr!
  rw [hAD.squarefree_iff, hsqfp]
  exact UniqueFactorizationMonoid.squarefree_radical

open Classical in
/-- The first component of `hoSplit D` divides its derivative times the second component. -/
theorem hoSplit_fst_dvd_deriv_mul_snd (D : K[X]) (hD : D ≠ 0) :
    (hoSplit D).1 ∣ derivative (hoSplit D).1 * (hoSplit D).2 := by
  have hmul : (hoSplit D).1 * (hoSplit D).2 = D := hoSplit_mul D hD
  have hderiv : derivative D
      = derivative (hoSplit D).1 * (hoSplit D).2 + (hoSplit D).1 * derivative (hoSplit D).2 := by
    conv_lhs => rw [← hmul]
    rw [derivative_mul]
  have hdvdD' : (hoSplit D).1 ∣ derivative D := gcd_dvd_right D (derivative D)
  have key : (hoSplit D).1 ∣ derivative D - (hoSplit D).1 * derivative (hoSplit D).2 :=
    dvd_sub hdvdD' (dvd_mul_right _ _)
  rwa [hderiv, add_sub_cancel_right] at key

open scoped Differential in
/-- The Horowitz-Ostrogradsky reduction identity transported to rational functions `K(x)`. -/
theorem horowitzReduce_step_ratFunc {A B C Dminus Dstar E : K[X]} (hDm : Dminus ≠ 0) (hDs : Dstar ≠ 0)
    (hE : E * Dminus = derivative Dminus * Dstar)
    (hA : derivative B * Dstar - B * E + C * Dminus = A) :
    algebraMap K[X] (RatFunc K) A
        / (algebraMap K[X] (RatFunc K) Dminus * algebraMap K[X] (RatFunc K) Dstar)
      = (algebraMap K[X] (RatFunc K) B / algebraMap K[X] (RatFunc K) Dminus)′
        + algebraMap K[X] (RatFunc K) C / algebraMap K[X] (RatFunc K) Dstar := by
  have hm : algebraMap K[X] (RatFunc K) Dminus ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hDm
  have hs : algebraMap K[X] (RatFunc K) Dstar ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hDs
  have hE' : algebraMap K[X] (RatFunc K) E * algebraMap K[X] (RatFunc K) Dminus
      = (algebraMap K[X] (RatFunc K) Dminus)′ * algebraMap K[X] (RatFunc K) Dstar := by
    rw [show (algebraMap K[X] (RatFunc K) Dminus)′
          = algebraMap K[X] (RatFunc K) (derivative Dminus) from ratFuncDeriv_algebraMap Dminus,
        ← map_mul, ← map_mul, hE]
  have key := horowitz_reduction_step (algebraMap K[X] (RatFunc K) B) (algebraMap K[X] (RatFunc K) C)
    (algebraMap K[X] (RatFunc K) Dminus) (algebraMap K[X] (RatFunc K) Dstar)
    (algebraMap K[X] (RatFunc K) E) hm hs hE'
  have hnum : (algebraMap K[X] (RatFunc K) B)′ * algebraMap K[X] (RatFunc K) Dstar
        - algebraMap K[X] (RatFunc K) B * algebraMap K[X] (RatFunc K) E
        + algebraMap K[X] (RatFunc K) C * algebraMap K[X] (RatFunc K) Dminus
      = algebraMap K[X] (RatFunc K) A := by
    rw [show (algebraMap K[X] (RatFunc K) B)′
          = algebraMap K[X] (RatFunc K) (derivative B) from ratFuncDeriv_algebraMap B,
        ← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_add, hA]
  rw [hnum] at key
  exact key

end DeepWiki.SymbolicIntegration
