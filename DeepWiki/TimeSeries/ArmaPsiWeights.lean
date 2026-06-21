import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic

/-! # The `ψ`-weight recursion `ψ = θ/φ` (§3.3, the First Method)
The autocovariance-computation `ψ`-weights of a causal `ARMA(p,q)` process are the coefficients of
the formal power series `ψ(z) = θ(z)/φ(z)` (eq 3.3.2), which satisfy the Cauchy recursion
`∑_{k≤j} φₖ ψ_{j−k} = θⱼ` (eq 3.3.3). This is the **algebraic** spine of the First Method: the
*analytic* convergence `∑ⱼ |ψⱼ| < ∞` (which the `L²` `MA(∞)` representation needs) requires the
causality decay estimate `|ψⱼ| = O(rʲ)` and is infra-blocked. -/

namespace DeepWiki.TimeSeries

open PowerSeries

/-- The `ψ`-weight power series of an `ARMA(p,q)` process: `ψ(z) = θ(z)/φ(z) = φ(z)⁻¹ θ(z)` as a
formal power series (eq 3.3.2). -/
noncomputable def armaPsi (φ θ : Polynomial ℝ) : PowerSeries ℝ :=
  (φ : PowerSeries ℝ)⁻¹ * (θ : PowerSeries ℝ)

/-- **Equations 3.3.2–3.3.3** (the defining identity): when `φ(0) ≠ 0` (the constant term is a unit,
e.g. `φ(0) = 1`), the `ψ`-weight series satisfies `φ(z) ψ(z) = θ(z)`, i.e. `ψ = θ/φ`. -/
theorem coe_mul_armaPsi {φ θ : Polynomial ℝ} (hφ : constantCoeff (φ : PowerSeries ℝ) ≠ 0) :
    (φ : PowerSeries ℝ) * armaPsi φ θ = (θ : PowerSeries ℝ) := by
  rw [armaPsi, ← mul_assoc, PowerSeries.mul_inv_cancel _ hφ, one_mul]

/-- **Equation 3.3.3** (the `ψ`-weight recursion): the coefficients of `ψ = θ/φ` satisfy the Cauchy
recursion `∑_{k=0}^j φₖ ψ_{j−k} = θⱼ` (the `zʲ`-coefficient of `φ ψ = θ`). With `φ₀ = 1`
(`φ(z) = 1 − φ₁z − ⋯`) this is the book's `ψⱼ − ∑_{0<k≤j} φ'ₖ ψ_{j−k} = θⱼ`; for `j > deg θ` the
right-hand side is `0`, giving the homogeneous tail. -/
theorem armaPsi_coeff_recursion {φ θ : Polynomial ℝ}
    (hφ : constantCoeff (φ : PowerSeries ℝ) ≠ 0) (j : ℕ) :
    ∑ k ∈ Finset.range (j + 1), φ.coeff k * coeff (j - k) (armaPsi φ θ) = θ.coeff j := by
  have h := congrArg (coeff j) (coe_mul_armaPsi (φ := φ) (θ := θ) hφ)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => coeff a (φ : PowerSeries ℝ) * coeff b (armaPsi φ θ)) j,
    Polynomial.coeff_coe] at h
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_coe]

/-- **Equation 3.3.3, antidiagonal form**: `∑_{(a,b), a+b=j} φₐ ψ_b = θⱼ` — the recursion as an
`antidiagonal` sum (the shape consumed by `aeval_mul_tsum_psi`/the Cauchy-product transfer relation),
equivalent to the `range`-form `armaPsi_coeff_recursion`. -/
theorem armaPsi_coeff_recursion_antidiagonal {φ θ : Polynomial ℝ}
    (hφ : constantCoeff (φ : PowerSeries ℝ) ≠ 0) (j : ℕ) :
    ∑ p ∈ Finset.antidiagonal j, φ.coeff p.1 * coeff p.2 (armaPsi φ θ) = θ.coeff j := by
  have h := congrArg (coeff j) (coe_mul_armaPsi (φ := φ) (θ := θ) hφ)
  rw [coeff_mul, Polynomial.coeff_coe] at h
  rw [← h]
  exact Finset.sum_congr rfl fun p _ => by rw [Polynomial.coeff_coe]

/-- For a pure `AR(p)` process (`θ = 1`), the `ψ`-weight series is the reciprocal `ψ = 1/φ`. -/
@[simp] theorem armaPsi_one (φ : Polynomial ℝ) : armaPsi φ 1 = (φ : PowerSeries ℝ)⁻¹ := by
  rw [armaPsi, Polynomial.coe_one, mul_one]

/-- The leading `ψ`-weight `ψ₀ = θ₀/φ₀` (the `j = 0` base case of the recursion). -/
theorem constantCoeff_armaPsi (φ θ : Polynomial ℝ) :
    constantCoeff (armaPsi φ θ) = (φ.coeff 0)⁻¹ * θ.coeff 0 := by
  rw [armaPsi, map_mul, constantCoeff_inv, Polynomial.constantCoeff_coe,
    Polynomial.constantCoeff_coe]

/-- The geometric series `∑ⱼ aʲ Xʲ` is the inverse of `1 − a X` in `ℝ⟦X⟧`. -/
theorem inv_one_sub_C_mul_X (a : ℝ) :
    (1 - C a * X : PowerSeries ℝ)⁻¹ = mk fun j => a ^ j := by
  have hc : constantCoeff (1 - C a * X : PowerSeries ℝ) ≠ 0 := by simp
  rw [inv_eq_iff_mul_eq_one hc]
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_one, mul_comm (mk fun j => a ^ j) (C a * X),
    mul_assoc, coeff_C_mul, coeff_mk]
  cases n with
  | zero => simp
  | succ m => rw [coeff_succ_X_mul, coeff_mk, if_neg (Nat.succ_ne_zero m), pow_succ]; ring

/-- **Example 3.2.2 ↔ §3.3:** the `ψ`-weights of the `AR(1)` process (`φ(z) = 1 − φ₁z`, `θ = 1`) are
the geometric weights `ψⱼ = φ₁ʲ` — the abstract `ψ = θ/φ` agrees with the explicit `ar1Filter`. -/
theorem coeff_armaPsi_ar1 (φ₁ : ℝ) (j : ℕ) :
    coeff j (armaPsi (1 - Polynomial.C φ₁ * Polynomial.X) 1) = φ₁ ^ j := by
  rw [armaPsi, Polynomial.coe_one, mul_one, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, inv_one_sub_C_mul_X, coeff_mk]

end DeepWiki.TimeSeries
