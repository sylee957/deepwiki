import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import DeepWiki.Algebra.PolynomialNormalization
import DeepWiki.Algebra.SquarefreeDeflation
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory.Derivative
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory.PartDerivatives
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory.Parts
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory.YunLoop

/-! # Squarefree factorization initialization

Derivative-gcd initialization and the abstract Yun-loop API for squarefree factorization.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

section Deflation
open UniqueFactorizationMonoid
variable {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D]

end Deflation

section GcdField

open UniqueFactorizationMonoid

variable {K : Type*} [Field K] [CharZero K]

open Classical

/-! ### The abstract Yun loop and its factor products -/

/-- Over a characteristic-`0` field: if `Pʲ ∣ p` exactly (`P^{j+1} ∤ p`) for irreducible `P` and
`j ≥ 1`, then `Pʲ ∤ dp/dx`. -/
private theorem pow_not_dvd_derivative_aux (p P : K[X]) (j : ℕ) (hj : 1 ≤ j) (hP : Irreducible P)
    (hdvd : P ^ j ∣ p) (hndvd : ¬ P ^ (j + 1) ∣ p) : ¬ P ^ j ∣ derivative p := by
  obtain ⟨g, hg⟩ := hdvd
  have hPg : ¬ P ∣ g := fun ⟨h, hgh⟩ => hndvd ⟨h, by rw [hg, hgh]; ring⟩
  rw [hg]
  intro hdvd2
  rw [derivative_mul, derivative_pow] at hdvd2
  have hPne : P ^ (j - 1) ≠ 0 := pow_ne_zero _ hP.ne_zero
  have hsplit : P ^ j = P ^ (j - 1) * P := by rw [← pow_succ]; congr 1; omega
  have h1 : P ^ j ∣ C (j : K) * P ^ (j - 1) * derivative P * g :=
    (dvd_add_left (dvd_mul_right (P ^ j) (derivative g))).mp hdvd2
  rw [show C (j : K) * P ^ (j - 1) * derivative P * g
      = P ^ (j - 1) * (C (j : K) * derivative P * g) from by ring, hsplit,
    mul_dvd_mul_iff_left hPne] at h1
  rcases hP.prime.dvd_mul.mp h1 with h | hg'
  · rcases hP.prime.dvd_mul.mp h with hcj | hdP
    · exact hP.prime.not_unit (isUnit_of_dvd_unit hcj
        (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))))
    · exact hP.prime.not_unit ((hP.separable).isUnit_of_dvd' (dvd_refl P) hdP)
  · exact hPg hg'

/-- Over a characteristic-`0` field, `gcd(pp(A), d pp(A)/dx)` is associated to the deflation
`A⁻¹`. -/
theorem deflation_one_eq_gcd (A : K[X]) (hA : A.primPart ≠ 0) :
    Associated (gcd A.primPart (derivative A.primPart)) (deflation A 1) := by
  set I := (normalizedFactors A.primPart).toFinset.image
    (fun P => (normalizedFactors A.primPart).count P) with hI
  set f := sqfreeFactPart A with hf
  have hfact : Associated A.primPart (∏ i ∈ I, (f i) ^ i) :=
    primPart_associated_prod_sqfreeFactPart A hA
  have hD1 : deflation A 1 = ∏ i ∈ I, (f i) ^ (i - 1) := deflation_eq_prod_sqfreeFactPart A 1
  have hpair : ∀ e : ℕ → ℕ,
      (↑I : Set ℕ).Pairwise (Function.onFun IsRelPrime fun i => (f i) ^ (e i)) :=
    fun e i _ j _ hij => (((sqfreeFactPart_isRelPrime A hij).isCoprime).pow_left.pow_right).isRelPrime
  have hI_dvd : deflation A 1 ∣ derivative A.primPart := by
    rw [hD1]
    refine Finset.prod_dvd_of_isRelPrime (hpair (fun i => i - 1)) (fun i hi => ?_)
    exact pow_sub_one_dvd_derivative_of_pow_dvd
      ((Finset.dvd_prod_of_mem (fun i => (f i) ^ i) hi).trans hfact.symm.dvd)
  obtain ⟨s, hs⟩ := id hI_dvd
  have hgcdne : gcd A.primPart (derivative A.primPart) ≠ 0 :=
    fun h => hA (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
  have hcop : IsCoprime (gcd A.primPart (derivative A.primPart)) s := by
    rw [← isRelPrime_iff_isCoprime, isRelPrime_iff_no_prime_factors hgcdne]
    intro P hPg hPs hPp
    have hPpp : P ∣ A.primPart := hPg.trans (gcd_dvd_left _ _)
    have hPprod : P ∣ ∏ i ∈ I, (f i) ^ i := hPpp.trans hfact.dvd
    rw [hPp.dvd_finsetProd_iff] at hPprod
    obtain ⟨j, hjI, hPfjpow⟩ := hPprod
    have hPfj : P ∣ f j := hPp.dvd_of_dvd_pow hPfjpow
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · rw [hj0, pow_zero] at hPfjpow; exact absurd (isUnit_of_dvd_one hPfjpow) hPp.not_unit
      · exact hj0
    obtain ⟨c, hc⟩ := hPfj
    have hPc : ¬ P ∣ c := fun ⟨d, hd⟩ =>
      hPp.not_unit ((sqfreeFactPart_squarefree A j) P ⟨d, by rw [← hf, hc, hd]; ring⟩)
    have hcoperase : IsCoprime P (∏ i ∈ I.erase j, (f i) ^ i) := by
      refine IsCoprime.prod_right (fun i hi => ?_)
      have hij : j ≠ i := fun h => (Finset.mem_erase.mp hi).1 h.symm
      exact (((sqfreeFactPart_isRelPrime A hij).isCoprime).of_isCoprime_of_dvd_left
        ⟨c, hc⟩).pow_right
    have hndvd : ¬ P ^ (j + 1) ∣ A.primPart := by
      intro hd
      rw [hfact.dvd_iff_dvd_right, ← Finset.mul_prod_erase I (fun i => (f i) ^ i) hjI] at hd
      have h2 : P ^ (j + 1) ∣ (f j) ^ j := (hcoperase.pow_left).dvd_of_dvd_mul_right hd
      rw [hc, mul_pow, pow_succ] at h2
      exact hPc (hPp.dvd_of_dvd_pow ((mul_dvd_mul_iff_left (pow_ne_zero j hPp.ne_zero)).mp h2))
    have hdvdj : P ^ j ∣ A.primPart :=
      ((pow_dvd_pow_of_dvd ⟨c, hc⟩ j).trans
        (Finset.dvd_prod_of_mem (fun i => (f i) ^ i) hjI)).trans hfact.symm.dvd
    have hpdvd : P ^ j ∣ derivative A.primPart := by
      rw [hs, show j = (j - 1) + 1 from by omega, pow_succ]
      exact mul_dvd_mul ((pow_dvd_pow_of_dvd ⟨c, hc⟩ (j - 1)).trans
        (hD1 ▸ Finset.dvd_prod_of_mem (fun i => (f i) ^ (i - 1)) hjI)) hPs
    exact pow_not_dvd_derivative_aux A.primPart P j hj1 hPp.irreducible hdvdj hndvd hpdvd
  exact associated_of_dvd_dvd (hcop.dvd_of_dvd_mul_right (hs ▸ gcd_dvd_right _ _))
    (dvd_gcd (deflation_dvd_primPart A 1 hA) ⟨s, hs⟩)

/-! ### The abstract Yun loop base case -/

open UniqueFactorizationMonoid in
open Classical in
/-- `deflation A k` is monic. -/
theorem deflation_monic {K : Type*} [Field K] (A : K[X]) (k : ℕ) :
    (deflation A k).Monic := by
  rw [deflation]
  refine monic_prod_of_monic _ _ (fun P hP => ?_)
  have hmem := Multiset.mem_toFinset.mp hP
  refine (?_ : (P).Monic).pow _
  rw [← normalize_normalized_factor P hmem]
  exact monic_normalize (irreducible_of_normalized_factor P hmem).ne_zero

open UniqueFactorizationMonoid in
open Classical in
/-- `A.primPart` is associated to `A` over a field. -/
theorem associated_primPart_self {K : Type*} [Field K] (A : K[X]) (hA0 : A ≠ 0) :
    Associated A.primPart A := by
  have hc : IsUnit (Polynomial.C A.content) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    exact fun h => hA0 (by rw [A.eq_C_content_mul_primPart, h, map_zero, zero_mul])
  refine ⟨hc.unit, ?_⟩
  rw [IsUnit.unit_spec]
  conv_rhs => rw [A.eq_C_content_mul_primPart]
  ring

open UniqueFactorizationMonoid in
open Classical in
/-- `deflation A 0 = normalize A` over a field. -/
theorem deflation_zero_eq_normalize {K : Type*} [Field K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) : deflation A 0 = normalize A := by
  refine eq_of_monic_of_associated (deflation_monic A 0)
    ((monic_normalize hA0)) ?_
  exact ((deflation_zero A hA).trans (associated_primPart_self A hA0)).trans
    (associated_normalize A)

open UniqueFactorizationMonoid in
open Classical in
/-- `derivative A = C (content A) * derivative A.primPart`. -/
theorem derivative_eq_C_content_mul_derivative_primPart {K : Type*} [Field K] (A : K[X]) :
    derivative A = Polynomial.C A.content * derivative A.primPart := by
  conv_lhs => rw [A.eq_C_content_mul_primPart]
  rw [derivative_mul, derivative_C, zero_mul, zero_add]

open UniqueFactorizationMonoid in
open Classical in
/-- `gcd A (derivative A) = deflation A 1` over a characteristic-zero field. -/
theorem gcd_self_derivative_eq_deflation_one {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) :
    gcd A (derivative A) = deflation A 1 := by
  have hgne : gcd A (derivative A) ≠ 0 :=
    fun h => hA0 (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
  have hgmonic : (gcd A (derivative A)).Monic := by
    rw [← normalize_eq_self_iff_monic hgne]; exact normalize_gcd A (derivative A)
  refine eq_of_monic_of_associated hgmonic (deflation_monic A 1) ?_
  have hAp : Associated A A.primPart := (associated_primPart_self A hA0).symm
  have hc : IsUnit (Polynomial.C A.content) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    exact fun h => hA0 (by rw [A.eq_C_content_mul_primPart, h, map_zero, zero_mul])
  have hAp' : Associated (derivative A) (derivative A.primPart) := by
    rw [derivative_eq_C_content_mul_derivative_primPart A]
    exact associated_unit_mul_left (derivative A.primPart) (Polynomial.C A.content) hc
  exact (Associated.gcd hAp hAp').trans (deflation_one_eq_gcd A hA)

open UniqueFactorizationMonoid in
open Classical in
/-- `squarefreePart (deflation A 0) * deflation A 1 = deflation A 0`. -/
theorem squarefreePart_mul_deflation_one {K : Type*} [Field K] (A : K[X]) (hA : A.primPart ≠ 0) :
    squarefreePart (deflation A 0) * deflation A 1 = deflation A 0 := by
  refine eq_of_monic_of_associated
    ((squarefreePart_deflation_monic A 0 hA).mul (deflation_monic A 1)) (deflation_monic A 0) ?_
  exact squarefreePart_mul_deflation_succ A 0 hA

open UniqueFactorizationMonoid in
open Classical in
/-- The Yun loop initialization satisfies `YunInv A 1`. -/
theorem yunInv_base {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) :
    YunInv A 1 (A / gcd A (derivative A))
      (derivative A / gcd A (derivative A) - derivative (A / gcd A (derivative A))) := by
  have hg : gcd A (derivative A) = deflation A 1 := gcd_self_derivative_eq_deflation_one A hA0 hA
  have hd1ne : deflation A 1 ≠ 0 := deflation_ne_zero A 1
  have hlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA0
  have hAeq : A = Polynomial.C A.leadingCoeff * deflation A 0 := by
    rw [deflation_zero_eq_normalize A hA0 hA]
    exact self_eq_C_leadingCoeff_mul_normalize A hA0
  have hbabs : Babs A 1 = squarefreePart (deflation A 0) := by rw [Babs]
  have hAfact : A = (Polynomial.C A.leadingCoeff * squarefreePart (deflation A 0)) * deflation A 1 := by
    rw [mul_assoc, squarefreePart_mul_deflation_one A hA, ← hAeq]
  have hb1 : A / gcd A (derivative A) = Polynomial.C A.leadingCoeff * Babs A 1 := by
    rw [hg, hbabs]
    nth_rewrite 1 [hAfact]
    rw [mul_div_cancel_right₀ _ hd1ne]
  have hAderiv : derivative A = Polynomial.C A.leadingCoeff * (deflation A 1 * Yun A 1) := by
    have hdp := derivative_deflation_pred A 1 (le_refl 1)
    rw [Nat.sub_self] at hdp
    conv_lhs => rw [hAeq, derivative_C_mul, hdp]
  have hd1div : derivative A / gcd A (derivative A) = Polynomial.C A.leadingCoeff * Yun A 1 := by
    rw [hg]
    nth_rewrite 1 [hAderiv]
    rw [mul_comm (deflation A 1) (Yun A 1), ← mul_assoc, mul_div_cancel_right₀ _ hd1ne]
  refine ⟨A.leadingCoeff, hlc, hb1, ?_⟩
  rw [hd1div, hb1, derivative_C_mul, Dabs, Nat.sub_self, ← hbabs, mul_sub]

/-! ### Unconditional abstract Yun factorization -/

open Classical in
/-- Abstract Yun factorization from the standard initialization. -/
noncomputable def yunFactorizationAbs {K : Type*} [Field K] (A : K[X]) (n : ℕ) : List K[X] :=
  yunLoopAbs A (A / gcd A (derivative A),
    derivative A / gcd A (derivative A) - derivative (A / gcd A (derivative A))) 1 n

open Classical in
/-- `yunFactorizationAbs` is factorwise associated to consecutive squarefree parts. -/
theorem yunFactorizationAbs_forall₂ {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) (n : ℕ) :
    List.Forall₂ Associated (yunFactorizationAbs A n)
      ((List.range n).map (fun j => sqfreeFactPart A (1 + j))) :=
  yunLoopAbs_forall₂ A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA)

open Classical in
/-- Every factor in `yunFactorizationAbs` is squarefree. -/
theorem yunFactorizationAbs_squarefree {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) (n : ℕ) : ∀ V ∈ yunFactorizationAbs A n, Squarefree V :=
  yunLoopAbs_squarefree A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA)

open Classical in
/-- Distinct-position factors in `yunFactorizationAbs` are relatively prime. -/
theorem yunFactorizationAbs_pairwise_isRelPrime {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ) {p q : ℕ} (hpq : p ≠ q)
    (hp : p < (yunFactorizationAbs A n).length) (hq : q < (yunFactorizationAbs A n).length) :
    IsRelPrime ((yunFactorizationAbs A n).get ⟨p, hp⟩) ((yunFactorizationAbs A n).get ⟨q, hq⟩) :=
  yunLoopAbs_pairwise_isRelPrime A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA) hpq hp hq

open Classical in
/-- The powered product of `yunFactorizationAbs` matches the powered squarefree parts up to association. -/
theorem yunFactorizationAbs_prodPow_assoc {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ) :
    Associated (prodPow 1 (yunFactorizationAbs A n))
      (prodPow 1 ((List.range n).map (fun j => sqfreeFactPart A (1 + j)))) :=
  yunLoopAbs_prodPow_assoc A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA)

end GcdField

end DeepWiki.SymbolicIntegration
