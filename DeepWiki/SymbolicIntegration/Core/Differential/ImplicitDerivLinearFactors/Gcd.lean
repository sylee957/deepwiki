import DeepWiki.SymbolicIntegration.Core.Differential.GcdDeriv
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors.Products

/-! # GCD formulas for implicit-derivative linear factors

GCD, radical, and derivative companion formulas for products of linear factors.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

section LinearFactor
open Polynomial

open Classical in
/-- Squarefree gcd formula: `gcd(∏_{a∈s}(X − a), (∏)′) ~ ∏_{a : v(a)=a′}(X − a)`. -/
theorem gcd_prod_X_sub_C_implicitDeriv {K : Type*} [Field K] [Differential K] (v : K[X])
    (s : Finset K) :
    Associated (gcd (∏ a ∈ s, (X - C a)) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a))))
      (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  refine (associated_gcd_deriv_prod s (fun a => X - C a) (fun a _ b _ hab =>
    gcd_isUnit_iff_isRelPrime.mpr (isCoprime_X_sub_C_iff.mpr
      (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hab)).isRelPrime)).trans ?_
  rw [Finset.prod_filter]
  refine Associated.prod s _ _ (fun a _ => ?_)
  by_cases h : v.eval a = a′
  · rw [if_pos h]
    exact isSpecial_iff_associated_gcd.mp ((dvd_X_sub_C_implicitDeriv_iff v a).mpr h)
  · rw [if_neg h]
    exact associated_one_iff_isUnit.mpr
      (IsNormal.isUnit_gcd ((isCoprime_X_sub_C_implicitDeriv_iff v a).mpr h))

open Classical in
/-- General gcd formula: over char `0`, for `p = ∏_{a∈s}(X − a)^{eₐ}` (each `eₐ ≥ 1`),
`gcd(p, p′) ~ (∏_a (X − a)^{eₐ−1}) · ∏_{a : v(a)=a′}(X − a)`. -/
theorem gcd_prod_X_sub_C_pow_implicitDeriv {K : Type*} [Field K] [CharZero K] [Differential K]
    (v : K[X]) (s : Finset K) (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    Associated
      (gcd (∏ a ∈ s, (X - C a) ^ e a) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a) ^ e a)))
      ((∏ a ∈ s, (X - C a) ^ (e a - 1)) * ∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  have hunit : ∀ a ∈ s, IsUnit ((e a : K[X])) := by
    intro a ha
    rw [← map_natCast (C : K →+* K[X])]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by have := he a ha; omega)))
  refine (associated_gcd_deriv_prod s (fun a => (X - C a) ^ e a) (fun a _ b _ hab =>
    gcd_isUnit_iff_isRelPrime.mpr ((IsCoprime.pow (isCoprime_X_sub_C_iff.mpr
      (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hab))).isRelPrime))).trans ?_
  refine (Associated.prod s _ _ (fun a ha => associated_gcd_deriv_pow (he a ha) (hunit a ha))).trans ?_
  rw [Finset.prod_mul_distrib]
  refine Associated.mul_left _ ?_
  rw [Finset.prod_filter]
  refine Associated.prod s _ _ (fun a _ => ?_)
  by_cases h : v.eval a = a′
  · rw [if_pos h]
    exact isSpecial_iff_associated_gcd.mp ((dvd_X_sub_C_implicitDeriv_iff v a).mpr h)
  · rw [if_neg h]
    exact associated_one_iff_isUnit.mpr
      (IsNormal.isUnit_gcd ((isCoprime_X_sub_C_implicitDeriv_iff v a).mpr h))

open Classical in
/-- The `d/dX` companion: over char `0`, `gcd(∏_{a∈s}(X − a)^{eₐ}, d/dX) ~ ∏_a (X − a)^{eₐ−1}`. -/
theorem gcd_prod_X_sub_C_pow_derivative {K : Type*} [Field K] [CharZero K] (s : Finset K)
    (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    Associated (gcd (∏ a ∈ s, (X - C a) ^ e a) (derivative (∏ a ∈ s, (X - C a) ^ e a)))
      (∏ a ∈ s, (X - C a) ^ (e a - 1)) := by
  letI : Differential K[X] := ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩
  have hunit : ∀ a ∈ s, IsUnit ((e a : K[X])) := by
    intro a ha
    rw [← map_natCast (C : K →+* K[X])]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by have := he a ha; omega)))
  refine (associated_gcd_deriv_prod s (fun a => (X - C a) ^ e a) (fun a _ b _ hab =>
    gcd_isUnit_iff_isRelPrime.mpr ((IsCoprime.pow (isCoprime_X_sub_C_iff.mpr
      (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hab))).isRelPrime))).trans ?_
  refine (Associated.prod s _ _ (fun a ha => associated_gcd_deriv_pow (he a ha) (hunit a ha))).trans ?_
  refine Associated.prod s _ _ (fun a _ => ?_)
  have hg1 : IsUnit (gcd (X - C a) ((X - C a)′)) := by
    have hd : (X - C a)′ = 1 := by show derivative (X - C a) = 1; simp
    rw [hd]; exact isUnit_gcd_one_right _
  exact (associated_mul_unit_right _ _ hg1).symm

open Classical in
/-- Squarefree part / radical: over char `0`, `∏_{a∈s}(X − a)^{eₐ} ~ gcd(A, dA/dx) · ∏(X − a)`. -/
theorem prod_X_sub_C_pow_associated_gcd_mul_radical {K : Type*} [Field K] [CharZero K]
    (s : Finset K) (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    Associated (∏ a ∈ s, (X - C a) ^ e a)
      (gcd (∏ a ∈ s, (X - C a) ^ e a) (derivative (∏ a ∈ s, (X - C a) ^ e a))
        * ∏ a ∈ s, (X - C a)) := by
  have hsplit : (∏ a ∈ s, (X - C a) ^ (e a - 1)) * ∏ a ∈ s, (X - C a)
      = ∏ a ∈ s, (X - C a) ^ e a := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a ha => by rw [← pow_succ, Nat.sub_add_cancel (he a ha)]
  have key := (gcd_prod_X_sub_C_pow_derivative s e he).symm.mul_right (∏ a ∈ s, (X - C a))
  rwa [hsplit] at key

open Classical in
/-- Special-part formula: over char `0`, `gcd(p, p′) ~ gcd(p, dp/dX) · ∏_{a : v(a)=a′}(X − a)`. -/
theorem gcd_implicitDeriv_associated_gcd_derivative_mul_special {K : Type*} [Field K] [CharZero K]
    [Differential K] (v : K[X]) (s : Finset K) (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    Associated
      (gcd (∏ a ∈ s, (X - C a) ^ e a) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a) ^ e a)))
      (gcd (∏ a ∈ s, (X - C a) ^ e a) (derivative (∏ a ∈ s, (X - C a) ^ e a))
        * ∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) :=
  (gcd_prod_X_sub_C_pow_implicitDeriv v s e he).trans
    ((gcd_prod_X_sub_C_pow_derivative s e he).symm.mul_right _)

end LinearFactor

end DeepWiki.SymbolicIntegration
