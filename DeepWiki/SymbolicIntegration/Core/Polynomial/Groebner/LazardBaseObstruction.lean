import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateView

/-! # Lazard base obstruction

The concrete `xy + 1` obstruction showing Lazard base divisibility is not automatic. -/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

/-! ## The base obstruction

The descent base `C(g₀) ∣ lazardView f₀` cannot be discharged for free: the
polynomial `xy + 1` has leading `y`-coefficient `x`, but `C(x)` does not divide
its `K[x][y]` view. -/

/-- `xy + 1`'s leading-`y`-coefficient `x = X 0` does not divide `1` in `K[x]`
(`= MvPolynomial (Fin 1) K`). -/
theorem leadingYCoeff_xyAddOne_not_dvd_one {K : Type*} [Field K] :
    ¬ (X (0 : Fin 1) : MvPolynomial (Fin 1) K) ∣ 1 := by
  intro h
  have he : (MvPolynomial.eval (fun _ => (0 : K))) (X (0 : Fin 1))
      ∣ (MvPolynomial.eval (fun _ => (0 : K))) 1 := map_dvd _ h
  rw [MvPolynomial.eval_X, map_one, zero_dvd_iff] at he
  exact one_ne_zero he

/-- The `K[x][y]` view of `xy + 1` is `C(x)·Y + 1` (`x = X 0`, `y = X 1`). -/
theorem lazardView_xyAddOne {K : Type*} [Field K] :
    lazardView (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K)
      = Polynomial.C (X 0) * Polynomial.X + 1 := by
  have h1 : (X (1 : Fin 2) : MvPolynomial (Fin 2) K) = X (0 : Fin 1).succ := by congr 1
  rw [lazardView, map_add, map_mul, map_one, finSuccEquiv_X_zero, h1, finSuccEquiv_X_succ]

/-- `leadingYCoeff (xy + 1) = x` (`= X 0`): the coefficient of `Y¹` in `C(x)·Y + 1`. -/
theorem leadingYCoeff_xyAddOne {K : Type*} [Field K] :
    leadingYCoeff (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K) = X 0 := by
  rw [leadingYCoeff, lazardView_xyAddOne]
  have hCX : (Polynomial.C (X (0 : Fin 1) : MvPolynomial (Fin 1) K) * Polynomial.X).natDegree = 1 :=
    Polynomial.natDegree_C_mul_X _ (MvPolynomial.X_ne_zero _)
  have hd : (Polynomial.C (X (0 : Fin 1) : MvPolynomial (Fin 1) K) * Polynomial.X + 1).natDegree = 1 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt
      (by rw [hCX, Polynomial.natDegree_one]; decide), hCX]
  rw [Polynomial.leadingCoeff, hd, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_one, mul_one, Polynomial.coeff_one, if_neg (by decide), add_zero]

/-- `leadingYCoeff f₀` need not be a unit: `xy + 1` has `leadingYCoeff = x`, not a unit of `K[x]`. -/
theorem not_isUnit_leadingYCoeff_xyAddOne {K : Type*} [Field K] :
    ¬ IsUnit (leadingYCoeff (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K)) := by
  rw [leadingYCoeff_xyAddOne]
  exact fun h => leadingYCoeff_xyAddOne_not_dvd_one (isUnit_iff_dvd_one.mp h)

/-- The base divisibility `C(g₀) ∣ lazardView f₀` genuinely fails: for `f = xy + 1`,
`C(leadingYCoeff f) = C(x)` does not divide `lazardView f = C(x)·Y + 1`. -/
theorem not_C_leadingYCoeff_dvd_lazardView_xyAddOne {K : Type*} [Field K] :
    ¬ Polynomial.C (leadingYCoeff (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K))
        ∣ lazardView (X 1 * X 0 + 1 : MvPolynomial (Fin 2) K) := by
  rw [leadingYCoeff_xyAddOne, lazardView_xyAddOne, Polynomial.C_dvd_iff_dvd_coeff]
  intro h
  have h0 := h 0
  simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_C,
    Polynomial.coeff_X_zero, mul_zero, Polynomial.coeff_one_zero, zero_add] at h0
  exact leadingYCoeff_xyAddOne_not_dvd_one h0

end DeepWiki.SymbolicIntegration
