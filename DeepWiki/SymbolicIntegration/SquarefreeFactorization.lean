import Mathlib.Algebra.Polynomial.Derivative
import DeepWiki.SymbolicIntegration.AlgebraicPreliminaries

/-! # Squarefree factorization — the derivative criterion (Bronstein §1.6)
The squarefree part and deflations of `A ∈ D[x]` are computed by gcd's with `dA/dx`, resting on
the fact that a prime factor `P` divides `dA/dx` exactly once less than it divides `A`. Here we
prove the easy half (Theorem 1.6.1(i), over any commutative ring): if `Pⁿ⁺¹ ∣ A` then `Pⁿ`
divides both `A` and `dA/dx`, hence `Pⁿ ∣ gcd(A, dA/dx)`. The characteristic-`0` converse
(Theorem 1.6.1(ii)) and the deflation theory it powers are tracked as remaining library work. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

/-- **Theorem 1.6.1(i)** (§1.6, core): if `Pⁿ⁺¹ ∣ A` then `Pⁿ` divides both `A` and its
derivative `dA/dx`. -/
theorem pow_dvd_and_pow_dvd_derivative {A P : R[X]} {n : ℕ} (h : P ^ (n + 1) ∣ A) :
    P ^ n ∣ A ∧ P ^ n ∣ derivative A := by
  refine ⟨(pow_dvd_pow P (Nat.le_succ n)).trans h, ?_⟩
  obtain ⟨B, rfl⟩ := h
  rw [derivative_mul, derivative_pow_succ]
  apply dvd_add
  · exact ((dvd_mul_left (P ^ n) _).mul_right _).mul_right _
  · exact (pow_dvd_pow P (Nat.le_succ n)).mul_right _

/-- **Theorem 1.6.1(i)** (§1.6): if `Pⁿ⁺¹ ∣ A` then `Pⁿ ∣ gcd(A, dA/dx)` (for any gcd `G` of `A`
and its derivative). -/
theorem pow_dvd_gcd_of_pow_succ_dvd {A P G : R[X]} {n : ℕ} (h : P ^ (n + 1) ∣ A)
    (hG : IsGCD A (derivative A) G) : P ^ n ∣ G :=
  hG.dvd (pow_dvd_and_pow_dvd_derivative h).1 (pow_dvd_and_pow_dvd_derivative h).2

end DeepWiki.SymbolicIntegration
