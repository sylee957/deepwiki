import DeepWiki.SymbolicIntegration.DifferentialFields
import DeepWiki.SymbolicIntegration.AlgebraicConstants
import DeepWiki.SymbolicIntegration.ConstantsAlgebraicClosure
import DeepWiki.SymbolicIntegration.DifferentialAlgebraFacts

/-! # Worked differential-algebra examples (Bronstein Ch 3)
Concrete instances of the §3.1–§3.2 differential-field machinery, formalized faithfully against
the book's wording: the induced derivation `Δ = κ_D + X·d/dX` on a polynomial ring `R[X]` and the
substitution-quotient `R[X]/(X) ≃ R` (§3.1), the uniqueness of the transcendental derivation
extension pinned by the value at `x`/`t` (§3.2), and the fact that an element algebraic over the
constant field of a characteristic-`0` differential field is itself a constant (§3.2). The
symbolic `SplitFactor`/`SplitSquarefreeFactor` traces of §3.5 are illustrations of the already
proven general correctness theorems (`splitFactor_isSplittingFactorization`) over the
noncomputable rational-function field `ℚ(x)`, so they are not re-run here. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section PolynomialDerivation
variable {R : Type*} [CommRing R] [Differential R]

/-- **Example 3.1.3** (§3.1): the induced derivation `Δ = κ_D + X·d/dX` on `R[X]` — the unique
derivation `Differential.implicitDeriv X` extending `D` on the constants with `Δ X = X` — acts on a
monomial `a·Xⁿ` by `Δ(a·Xⁿ) = (Da + n·a)·Xⁿ`, i.e. `Δ(∑ aₙ Xⁿ) = ∑ (Daₙ + n·aₙ) Xⁿ`. -/
theorem implicitDeriv_X_monomial (n : ℕ) (a : R) :
    Differential.implicitDeriv (X : R[X]) (Polynomial.monomial n a)
      = Polynomial.monomial n (a′ + n * a) := by
  rw [Differential.implicitDeriv]
  simp only [Derivation.add_apply, Differential.mapCoeffs_monomial, Derivation.smul_apply,
    Derivation.restrictScalars_apply, Polynomial.derivative'_apply, Polynomial.derivative_monomial,
    smul_eq_mul]
  rw [Polynomial.X_mul, ← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_mul_monomial]
  rcases n with _ | m
  · simp
  · rw [Nat.add_sub_cancel, ← (Polynomial.monomial (m + 1)).map_add]
    congr 1
    push_cast
    ring

/-- **Example 3.1.3** (§3.1), the induced derivation on the substitution quotient `R[X]/(X) ≃ R`:
`Δ = Differential.implicitDeriv X` reduces, on constant coefficients, to `D` — the constant term of
`Δ p` is the `D`-derivative of the constant term of `p`, `(Δ p)(0)′-style: (Δ p).coeff 0 = (p.coeff
0)′`. Under `π : R[X] → R[X]/(X) ≃ R` (the substitution `X ↦ 0`) this says the induced `Δ*` equals
`D` on `R`. -/
theorem implicitDeriv_X_coeff_zero (p : R[X]) :
    (Differential.implicitDeriv (X : R[X]) p).coeff 0 = (p.coeff 0)′ := by
  rw [Differential.implicitDeriv]
  simp only [Derivation.add_apply, Polynomial.coeff_add, Differential.coeff_mapCoeffs,
    Derivation.smul_apply, Derivation.restrictScalars_apply, Polynomial.derivative'_apply,
    smul_eq_mul, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero]
  ring

end PolynomialDerivation

section TranscendentalExtension
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Example 3.2.1 / 3.2.2** (§3.2): on the fraction field `K` of `R`, a derivation is determined
by its restriction to `R`. Hence a derivation on `F(x)` (resp. `F(t)`) is the *unique* one with a
prescribed restriction — `Example 3.2.1` is `(F, 0_F)` extended by `Dx = 1` (only `d/dx`),
`Example 3.2.2` is `(F, D)` extended by `Δt = 0` (only `κ_D`). This is the fraction-field uniqueness
`derivation_ext_fractionRing` restated as the example. -/
theorem derivation_fractionRing_unique_of_restrict {Δ₁ Δ₂ : Derivation ℤ K K}
    (h : ∀ a : R, Δ₁ (algebraMap R K a) = Δ₂ (algebraMap R K a)) : Δ₁ = Δ₂ :=
  derivation_ext_fractionRing h

end TranscendentalExtension

section AlgebraicOverConstants
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- **Example 3.2.3** (§3.2): in a characteristic-`0` differential field, *any algebraic element
over the constants is itself a constant*. If `α ∈ E` is integral over `F` and is a root of a
separable nonzero polynomial `q` with constant coefficients (the minimal polynomial of `α` over the
constants, separable in char `0`), then `α′ = 0`. (Differentiate `q(α) = 0`: `0 = q'(α)·α′`, and
`q'(α) ≠ 0` by separability.) -/
theorem deriv_eq_zero_of_separable_root_const_coeffs {α : E} (q : E[X]) (hq : ∀ i, (q.coeff i)′ = 0)
    (hroot : q.eval α = 0) (hsep : q.derivative.eval α ≠ 0) : α′ = 0 :=
  deriv_eq_zero_of_isAlgebraicOverConst q hq hroot hsep

/-- **Example 3.2.3** (§3.2), the char-`0` characterisation: an element `α ∈ E` integral over `F` is
a constant **iff** it is a root of a separable nonzero polynomial with constant coefficients —
specialising `deriv_eq_zero_iff_isAlgebraicOverConst_separable`. So "algebraic over the constants"
(via the separable minimal polynomial) is equivalent to "is a constant". -/
theorem deriv_eq_zero_iff_separable_root_const_coeffs [CharZero F] {α : E} (hint : IsIntegral F α) :
    α′ = 0 ↔ ∃ q : E[X], q ≠ 0 ∧ (∀ i, (q.coeff i)′ = 0) ∧ q.eval α = 0 ∧
      q.derivative.eval α ≠ 0 :=
  deriv_eq_zero_iff_isAlgebraicOverConst_separable hint

end AlgebraicOverConstants

end DeepWiki.SymbolicIntegration
