import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.Diophantine
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.HermitePower
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager
import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import DeepWiki.SymbolicIntegration.Subresultants
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Radical.Basic
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.PartialFractions

/-! # Rational-function integration algorithms
Functional kernels for rational integration over `K[X]`: Diophantine solves, Hermite reduction,
resultants, subresultants, polynomial parts, and Horowitz denominator splitting. -/

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

/-! ## Polynomial Part
Termwise polynomial antiderivatives and the polynomial-division split for rational functions. -/

/-- Termwise polynomial antiderivative `∑ aₙ/(n+1) * X^(n+1)`. -/
noncomputable def polyIntegral (Q : K[X]) : K[X] :=
  Q.sum fun n a => C (a / ((n : K) + 1)) * X ^ (n + 1)

/-- Over a characteristic-zero field, `polyIntegral Q` differentiates to `Q`. -/
theorem polyIntegral_derivative [CharZero K] (Q : K[X]) : derivative (polyIntegral Q) = Q := by
  rw [polyIntegral, Polynomial.sum_def, derivative_sum]
  rw [show (∑ n ∈ Q.support, derivative (C (Q.coeff n / ((n : K) + 1)) * X ^ (n + 1)))
        = ∑ n ∈ Q.support, C (Q.coeff n) * X ^ n from Finset.sum_congr rfl fun n _ => ?_]
  · conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq Q, Polynomial.sum_def]
  · rw [derivative_C_mul_X_pow, Nat.add_sub_cancel]
    have hn1 : ((n + 1 : ℕ) : K) = (n : K) + 1 := by push_cast; ring
    rw [hn1, div_mul_cancel₀ _ (by exact_mod_cast Nat.succ_ne_zero n)]

-- `∫ Q dx` is a genuine antiderivative of `Q`.
example [CharZero K] (Q : K[X]) : derivative (polyIntegral Q) = Q := polyIntegral_derivative Q

/-- In `K(x)`, `A / Den` splits into its polynomial quotient plus remainder fraction. -/
theorem ratFunc_polyDivide_split (A Den : K[X]) (hDen : Den ≠ 0) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) Den
      = algebraMap K[X] (RatFunc K) (A / Den)
        + algebraMap K[X] (RatFunc K) (A % Den) / algebraMap K[X] (RatFunc K) Den := by
  have hd : algebraMap K[X] (RatFunc K) Den ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hDen
  have hAeq : algebraMap K[X] (RatFunc K) A
      = algebraMap K[X] (RatFunc K) Den * algebraMap K[X] (RatFunc K) (A / Den)
        + algebraMap K[X] (RatFunc K) (A % Den) := by
    rw [← map_mul, ← map_add, EuclideanDomain.div_add_mod]
  rw [hAeq]; field_simp

open scoped Differential in
open Classical in
/-- A squarefree-power rational function reduces to derivative, polynomial, and squarefree residual parts. -/
theorem integrateRationalFunction_reduction [CharZero K] {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (D : ι → K[X]) (e : ι → ℕ) (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
      algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i) / algebraMap K[X] (RatFunc K) (D i) := by
  set Den : K[X] := ∏ i ∈ s, D i ^ e i with hDen
  have hDenne : Den ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hD i hi).ne_zero
  have hDenmap : (∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i)
      = algebraMap K[X] (RatFunc K) Den := by
    rw [hDen, map_prod]; exact Finset.prod_congr rfl fun i _ => (map_pow _ _ _).symm
  -- PolyDivide: split off the polynomial quotient `A / Den`.
  rw [hDenmap, ratFunc_polyDivide_split A Den hDenne]
  -- Hermite-reduce the proper remainder `(A % Den) / Den`.
  obtain ⟨g, r, hg⟩ := hermiteReduce_full s hs D e hD he hcop (A % Den)
  rw [← hDenmap, hg]
  -- The polynomial quotient integrates to `polyIntegral (A / Den)`.
  refine ⟨g, A / Den, r, ?_⟩
  have hpi : (algebraMap K[X] (RatFunc K) (polyIntegral (A / Den)))′
      = algebraMap K[X] (RatFunc K) (A / Den) := by
    show ratFuncDeriv _ = _
    rw [ratFuncDeriv_algebraMap (polyIntegral (A / Den)), polyIntegral_derivative]
  rw [hpi]; ring

open scoped Differential in
open Classical in
-- `∫ A/Den` reduces to a rational part, a polynomial-integral part, and a squarefree-denominator sum.
example [CharZero K] {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (D : ι → K[X]) (e : ι → ℕ)
    (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
      algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i) / algebraMap K[X] (RatFunc K) (D i) :=
  integrateRationalFunction_reduction s hs D e hD he hcop A

open scoped Differential in
open Classical in
/-- The rational-function reduction can choose squarefree residual numerators proper below each factor. -/
theorem integrateRationalFunction_reduction_proper [CharZero K] {ι : Type*} (s : Finset ι)
    (D : ι → K[X]) (e : ι → ℕ) (hmonic : ∀ i ∈ s, (D i).Monic) (hsf : ∀ i ∈ s, Squarefree (D i))
    (hnd : ∀ i ∈ s, 0 < (D i).natDegree) (he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
      (∀ i ∈ s, (r i).degree < (D i).degree) ∧
      algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i) / algebraMap K[X] (RatFunc K) (D i) := by
  -- Degree-bounded partial fraction over the monic powers `g i = (D i)^(e i)`.
  have hgmonic : ∀ i ∈ s, ((D i) ^ e i).Monic := fun i hi => (hmonic i hi).pow _
  have hgcop : Set.Pairwise (↑s : Set ι) fun i j => IsCoprime ((D i) ^ e i) ((D j) ^ e j) :=
    fun i hi j hj hij => (hcop i hi j hj hij).pow
  obtain ⟨p, B, hBdeg, hpf⟩ :=
    Polynomial.div_prod_eq_quo_add_sum_rem_div (R := K) (K := RatFunc K) A hgmonic hgcop
  -- Reduce each proper prime power `Bᵢ/(Dᵢ^eᵢ)` by the Hermite loop.
  refine ⟨∑ i ∈ s, (hermiteReducePower (D i) (e i) (B i)).1, p,
    fun i => (hermiteReducePower (D i) (e i) (B i)).2, fun i hi => ?_, ?_⟩
  · -- properness: `deg rᵢ < deg Dᵢ` from the degree-tracking lemma.
    simp only []
    refine hermiteReducePower_remainder_degree (D i) (hsf i hi) (hnd i hi) (e i) (he i hi) (B i) ?_
    have hd : ((D i) ^ e i).degree = ((e i * (D i).natDegree : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_pow, Polynomial.degree_eq_natDegree (hmonic i hi).ne_zero,
        nsmul_eq_mul, ← Nat.cast_mul]
    exact (hBdeg i hi).trans_eq hd
  · -- assemble: partial fraction → `hermiteReduce_sum_spec` → `polyIntegral`.
    have hsumeq := hermiteReduce_sum_spec s D e B hsf he
    -- normalize the Mathlib casts `↑` to `algebraMap`, with `↑(Dᵢ^eᵢ) = (algebraMap Dᵢ)^eᵢ`.
    have hpf' : algebraMap K[X] (RatFunc K) A
          / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = algebraMap K[X] (RatFunc K) p
          + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (B i) / algebraMap K[X] (RatFunc K) (D i) ^ e i := by
      have e1 : (∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i)
          = ∏ i ∈ s, (algebraMap K[X] (RatFunc K) ((D i) ^ e i) : RatFunc K) :=
        Finset.prod_congr rfl fun i _ => (map_pow _ _ _).symm
      have e2 : (∑ i ∈ s, algebraMap K[X] (RatFunc K) (B i)
            / algebraMap K[X] (RatFunc K) (D i) ^ e i)
          = ∑ i ∈ s, (algebraMap K[X] (RatFunc K) (B i) : RatFunc K)
              / algebraMap K[X] (RatFunc K) ((D i) ^ e i) :=
        Finset.sum_congr rfl fun i _ => by rw [map_pow]
      rw [e1, e2]; exact hpf
    rw [hpf', hsumeq]
    have hpi : (algebraMap K[X] (RatFunc K) (polyIntegral p))′
        = algebraMap K[X] (RatFunc K) p := by
      show ratFuncDeriv _ = _
      rw [ratFuncDeriv_algebraMap (polyIntegral p), polyIntegral_derivative]
    rw [hpi]; ring

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
