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

end DeepWiki.TimeSeries
