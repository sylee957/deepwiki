import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.Hermite
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionDerivative
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.PartialFractions

/-! # Polynomial parts of rational integration

Polynomial antiderivatives and polynomial-division splits for rational functions.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

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

end DeepWiki.SymbolicIntegration
