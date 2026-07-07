import Mathlib.Algebra.Polynomial.Derivative
import DeepWiki.SymbolicIntegration.AlgebraicPreliminaries

/-! # Polynomial derivative divisibility

Reusable divisibility facts relating powers of a polynomial to derivatives.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

/-- If `Pⁿ⁺¹ ∣ A` then `Pⁿ` divides both `A` and its derivative `dA/dx`. -/
theorem pow_dvd_and_pow_dvd_derivative {A P : R[X]} {n : ℕ} (h : P ^ (n + 1) ∣ A) :
    P ^ n ∣ A ∧ P ^ n ∣ derivative A := by
  refine ⟨(pow_dvd_pow P (Nat.le_succ n)).trans h, ?_⟩
  obtain ⟨B, rfl⟩ := h
  rw [derivative_mul, derivative_pow_succ]
  apply dvd_add
  · exact ((dvd_mul_left (P ^ n) _).mul_right _).mul_right _
  · exact (pow_dvd_pow P (Nat.le_succ n)).mul_right _

/-- If `Pⁿ⁺¹ ∣ A` then `Pⁿ ∣ G` for any gcd `G` of `A` and its derivative `dA/dx`. -/
theorem pow_dvd_gcd_of_pow_succ_dvd {A P G : R[X]} {n : ℕ} (h : P ^ (n + 1) ∣ A)
    (hG : IsGCD A (derivative A) G) : P ^ n ∣ G :=
  hG.dvd (pow_dvd_and_pow_dvd_derivative h).1 (pow_dvd_and_pow_dvd_derivative h).2

end DeepWiki.SymbolicIntegration
