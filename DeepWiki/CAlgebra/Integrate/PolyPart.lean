import DeepWiki.CAlgebra.Diff.Derivative

/-! # The polynomial part: integration

The polynomial stage of the integration pipeline: `polyIntegrate` (the antiderivative
with zero constant term, characteristic zero), its soundness `(∫p)′ = p`, and its
completeness — antiderivatives are unique up to the integration constant. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

open scoped Differential FormalDiff

variable {K : Type u} [Field K] [DecidableEq K] [CharZero K]

/-- The polynomial antiderivative with zero constant term (characteristic zero):
`∑ aₖ xᵏ ↦ ∑ aₖ/(k+1) · xᵏ⁺¹`. -/
def polyIntegrate (p : DensePoly K) : DensePoly K :=
  ofList ((List.range (p.size + 1)).map fun k =>
    if k = 0 then 0 else p.coeff (k - 1) / ((k : ℕ) : K))

omit [CharZero K] in
/-- The derivative of a constant is zero. -/
@[simp] theorem deriv_C (c : K) : (C c : DensePoly K)′ = 0 := by
  apply toPolynomial_injective
  simp only [toPolynomial_deriv, toPolynomial_C, Polynomial.derivative_C, toPolynomial_zero]

/-- The kernel of the derivative is the constants (characteristic zero). -/
theorem eq_C_of_deriv_eq_zero {q : DensePoly K} (h : q′ = 0) : q = C (q.coeff 0) := by
  have h0 : Polynomial.derivative (toPolynomial q) = 0 := by
    rw [← toPolynomial_deriv, h, toPolynomial_zero]
  have hdeg : (toPolynomial q).natDegree = 0 :=
    Polynomial.derivative_eq_zero.mp h0
  rcases eq_or_ne q 0 with rfl | hq
  · rw [coeff_zero]
    apply toPolynomial_injective
    rw [toPolynomial_C, toPolynomial_zero, map_zero]
  · have hs : q.size = 1 := by
      rw [natDegree_toPolynomial_eq_size_sub_one] at hdeg
      have : q.size ≠ 0 := fun h0 => hq (eq_zero_of_size_zero h0)
      omega
    exact eq_C_of_size_eq_one hs

/-- `polyIntegrate` is a right inverse of the derivative. -/
@[simp] theorem polyIntegrate_deriv (p : DensePoly K) : (polyIntegrate p)′ = p := by
  apply toPolynomial_injective
  rw [toPolynomial_deriv]
  ext n
  rw [Polynomial.coeff_derivative, coeff_toPolynomial, coeff_toPolynomial, polyIntegrate,
    coeff_ofList_map_range]
  by_cases h : n < p.size
  · rw [if_pos (by omega : n + 1 < p.size + 1), if_neg (by omega : ¬ n + 1 = 0)]
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [div_mul_cancel₀]
    exact_mod_cast Nat.succ_ne_zero n
  · rw [if_neg (by omega : ¬ n + 1 < p.size + 1), zero_mul,
      coeff_eq_zero_of_size_le p (by omega)]

/-- **Completeness (uniqueness) of polynomial integration**: `q` is an antiderivative of
`p` exactly when it is `polyIntegrate p` shifted by a constant. -/
theorem polyIntegrate_complete (p q : DensePoly K) :
    q′ = p ↔ ∃ c : K, q = polyIntegrate p + C c := by
  constructor
  · intro h
    have hker : (q - polyIntegrate p)′ = 0 := by
      rw [sub_eq_add_neg, deriv_add, deriv_neg, h, polyIntegrate_deriv, add_neg_cancel]
    refine ⟨(q - polyIntegrate p).coeff 0, ?_⟩
    have := eq_C_of_deriv_eq_zero hker
    rw [← this]
    ring
  · rintro ⟨c, rfl⟩
    rw [deriv_add, polyIntegrate_deriv, deriv_C, add_zero]

end DensePoly

end DeepWiki.CAlgebra
