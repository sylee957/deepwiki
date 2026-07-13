import DeepWiki.CAlgebra.Poly.Derivative
import Mathlib.RingTheory.Derivation.DifferentialRing

/-! # Differential structure on `DensePoly` and its Mathlib bridge

The formal derivative `deriv` packages into a Mathlib `Derivation ℤ`, making `DensePoly R` a
`Differential` ring; `Polynomial R` is likewise a `Differential` ring via `Polynomial.derivative`
(Mathlib provides the derivative but not the instance); and `toPolynomial` is a differential-ring
morphism (`toPolynomial p′ = (toPolynomial p)′`). This lets the abstract Risch/Hermite development,
written over `[Differential K]`, run over the CAlgebra carriers with each step carried to
`Polynomial.derivative`. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- The formal derivative as a `ℤ`-derivation on `DensePoly R`. -/
noncomputable def densePolyDerivation : Derivation ℤ (DensePoly R) (DensePoly R) where
  toLinearMap := (AddMonoidHom.mk' DensePoly.deriv DensePoly.deriv_add).toIntLinearMap
  map_one_eq_zero' := DensePoly.deriv_one
  leibniz' a b := by
    show DensePoly.deriv (a * b) = a • DensePoly.deriv b + b • DensePoly.deriv a
    rw [DensePoly.deriv_mul, smul_eq_mul, smul_eq_mul]; ring

/-- `DensePoly R` is a differential ring via the formal derivative. -/
noncomputable instance : Differential (DensePoly R) := ⟨densePolyDerivation⟩

/-- The differential-ring derivation is the formal derivative. -/
@[simp] theorem densePolyDerivation_apply (p : DensePoly R) :
    densePolyDerivation p = DensePoly.deriv p := rfl

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
/-- `toPolynomial` is a differential-ring morphism: it intertwines the two `′` derivations. -/
@[simp] theorem toPolynomial_differential (p : DensePoly R) :
    toPolynomial (p′) = (toPolynomial p)′ := toPolynomial_deriv p

open scoped Differential in
/-- Validation: the ring iso commutes with differentiation, and the derivation is the formal one. -/
example (p : DensePoly R) :
    toPolynomial (p′) = (toPolynomial p)′ ∧ densePolyDerivation p = DensePoly.deriv p :=
  ⟨toPolynomial_differential p, rfl⟩

end DeepWiki.CAlgebra
