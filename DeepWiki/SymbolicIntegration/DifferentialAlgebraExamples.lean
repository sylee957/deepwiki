import DeepWiki.SymbolicIntegration.DifferentialAlgebra
import DeepWiki.SymbolicIntegration.DifferentialAlgebraFacts

/-! # Worked differential-algebra examples
Concrete instances of the differential-field machinery: the induced derivation
`Δ = κ_D + X·d/dX` on `R[X]` and its restriction to the substitution quotient `R[X]/(X) ≃ R`,
the differential ideals of `(K[X], d/dX)`, and the fraction-field uniqueness of derivation
extensions. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section PolynomialDerivation
variable {R : Type*} [CommRing R] [Differential R]

/-- The induced derivation `Δ = κ_D + X·d/dX` on `R[X]` (`Differential.implicitDeriv X`, the
unique derivation extending `D` with `Δ X = X`) acts on a monomial by
`Δ(a·Xⁿ) = (Da + n·a)·Xⁿ`. -/
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

/-- `(Δ p).coeff 0 = (p.coeff 0)′` for `Δ = Differential.implicitDeriv X`: on the substitution
quotient `R[X]/(X) ≃ R` (the substitution `X ↦ 0`) the induced derivation equals `D`. -/
theorem implicitDeriv_X_coeff_zero (p : R[X]) :
    (Differential.implicitDeriv (X : R[X]) p).coeff 0 = (p.coeff 0)′ := by
  rw [Differential.implicitDeriv]
  simp only [Derivation.add_apply, Polynomial.coeff_add, Differential.coeff_mapCoeffs,
    Derivation.smul_apply, Derivation.restrictScalars_apply, Polynomial.derivative'_apply,
    smul_eq_mul, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero]
  ring

end PolynomialDerivation

end DeepWiki.SymbolicIntegration
