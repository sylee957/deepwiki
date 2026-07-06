import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-! # Differential polynomials

Formal polynomial expressions in a base variable and derivative variables. -/

namespace DeepWiki.SymbolicIntegration

open MvPolynomial

variable {K : Type*} [Field K]

/-- The differential-variable polynomial ring with `X none` for `x` and `X (some n)` for `u^(n)`. -/
abbrev DiffPoly (K : Type*) [Field K] : Type _ := MvPolynomial (Option ℕ) K

/-- The base variable `x = X none` in `DiffPoly K`. -/
noncomputable abbrev dpX : DiffPoly K := X none

/-- The `n`-th derivative variable `u^(n) = X (some n)` in `DiffPoly K`. -/
noncomputable abbrev dpU (n : ℕ) : DiffPoly K := X (some n)

/-- The embedding `K[x] → DiffPoly K` sending `X` to `dpX`. -/
noncomputable def dpEmbed : Polynomial K →+* DiffPoly K :=
  Polynomial.eval₂RingHom (MvPolynomial.C : K →+* DiffPoly K) (X none)

/-- `dpEmbed` sends the polynomial variable to `dpX`. -/
@[simp] theorem dpEmbed_X : dpEmbed (Polynomial.X : Polynomial K) = (X none : DiffPoly K) := by
  simp [dpEmbed]

/-- `dpEmbed` sends a constant polynomial to the matching `MvPolynomial` constant. -/
@[simp] theorem dpEmbed_C (c : K) : dpEmbed (Polynomial.C c) = (MvPolynomial.C c : DiffPoly K) := by
  simp [dpEmbed]

/-- The `d/dx` derivation on `DiffPoly K`, with `ddx x = 1` and `ddx u^(n) = u^(n+1)`. -/
noncomputable def ddx : Derivation K (DiffPoly K) (DiffPoly K) :=
  MvPolynomial.mkDerivation K fun v => match v with
    | none => 1
    | some n => X (some (n + 1))

/-- `ddx dpX = 1`. -/
@[simp] theorem ddx_x : ddx (dpX : DiffPoly K) = 1 := by
  simp [ddx, dpX]

/-- `ddx (dpU n) = dpU (n + 1)`. -/
@[simp] theorem ddx_u (n : ℕ) : ddx (dpU n : DiffPoly K) = dpU (n + 1) := by
  simp [ddx, dpU]

/-- `ddx` kills constants from `K`. -/
@[simp] theorem ddx_C (c : K) : ddx (MvPolynomial.C c : DiffPoly K) = 0 := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (ddx (K := K)).map_algebraMap c

/-- `ddx` of an embedded polynomial is the embedded formal derivative. -/
theorem ddx_dpEmbed (p : Polynomial K) : ddx (dpEmbed p) = dpEmbed (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on with
  | C c => simp [dpEmbed]
  | add p q hp hq => simp [hp, hq]
  | monomial n c _ih =>
      rw [Polynomial.derivative_C_mul_X_pow, Nat.add_sub_cancel]
      have hembed : dpEmbed (Polynomial.C c * Polynomial.X ^ (n + 1))
          = MvPolynomial.C c * (X none : DiffPoly K) ^ (n + 1) := by
        simp [dpEmbed]
      have hembedR : dpEmbed (Polynomial.C (c * (↑(n + 1) : K)) * Polynomial.X ^ n)
          = MvPolynomial.C c * (↑(n + 1) : DiffPoly K) * (X none : DiffPoly K) ^ n := by
        rw [map_mul, map_pow, dpEmbed_X, dpEmbed_C, map_mul, map_natCast]
      rw [hembed, hembedR, Derivation.leibniz, ddx_C, smul_zero, add_zero,
        Derivation.leibniz_pow, ddx_x, Nat.add_sub_cancel]
      simp only [smul_eq_mul, mul_one, nsmul_eq_mul]
      push_cast
      ring

end DeepWiki.SymbolicIntegration
