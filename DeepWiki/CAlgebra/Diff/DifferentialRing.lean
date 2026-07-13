import DeepWiki.CAlgebra.Poly.Derivative
import DeepWiki.CAlgebra.PolyBridge.Ring
import Mathlib.RingTheory.Derivation.DifferentialRing

/-! # `DensePoly` as a differential ring

The formal derivative `deriv` packages into a Mathlib `Derivation ℤ`, making `DensePoly R` a
`Differential` ring. This is the Phase-6 foundation: the abstract Risch/Hermite development (written
over `[Differential K]`) can then run over the CAlgebra carriers, with `toPolynomial` carrying each
step to the `Polynomial.derivative` world. -/

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
@[simp] theorem densePolyDerivation_apply (p : DensePoly R) : densePolyDerivation p = DensePoly.deriv p :=
  rfl

/-- Validation: the differential structure's derivation is the formal derivative, and it carries to
`Polynomial.derivative` through the ring iso. -/
example (p : DensePoly R) : toPolynomial (densePolyDerivation p) = (toPolynomial p).derivative :=
  toPolynomial_deriv p

end DeepWiki.CAlgebra
