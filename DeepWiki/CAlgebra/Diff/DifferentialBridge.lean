import DeepWiki.CAlgebra.Diff.DifferentialRing

/-! # The differential-ring bridge `DensePoly R ≃ Polynomial R`

`Polynomial R` is made a `Differential` ring via `Polynomial.derivative` (Mathlib provides the
derivative but not the `Differential` instance). Then `toPolynomial` is a differential-ring morphism:
it intertwines the `DensePoly` derivation `′` with the `Polynomial` derivation `′`. This is the
commuting square at the derivation level — the shape every ported engine step will transport through. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- `Polynomial.derivative` as a `ℤ`-derivation. -/
noncomputable def polynomialDerivation : Derivation ℤ (Polynomial R) (Polynomial R) where
  toLinearMap := (Polynomial.derivative (R := R)).toAddMonoidHom.toIntLinearMap
  map_one_eq_zero' := Polynomial.derivative_one
  leibniz' a b := by
    show Polynomial.derivative (a * b) = a • Polynomial.derivative b + b • Polynomial.derivative a
    rw [Polynomial.derivative_mul, smul_eq_mul, smul_eq_mul]; ring

/-- `Polynomial R` is a differential ring via its formal derivative. -/
noncomputable instance : Differential (Polynomial R) := ⟨polynomialDerivation⟩

omit [DecidableEq R] in
/-- The `Polynomial` differential-ring derivation is `Polynomial.derivative`. -/
@[simp] theorem polynomialDerivation_apply (p : Polynomial R) :
    polynomialDerivation p = Polynomial.derivative p := rfl

open scoped Differential in
/-- `toPolynomial` is a differential-ring morphism: it intertwines the two `′` derivations. This is
the derivation-level commuting square the engine re-anchor transports every step through. -/
@[simp] theorem toPolynomial_differential (p : DensePoly R) :
    toPolynomial (p′) = (toPolynomial p)′ := toPolynomial_deriv p

open scoped Differential in
/-- Validation: the ring iso commutes with differentiation. -/
example (p : DensePoly R) : toPolynomial (p′) = (toPolynomial p)′ := toPolynomial_differential p

end DeepWiki.CAlgebra
