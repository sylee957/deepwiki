import Mathlib.RingTheory.Polynomial.Resultant.Basic
import DeepWiki.CAlgebra.Poly.Operations

/-! # The bivariate polynomial bridge

`toPolynomial₂` reads a dense bivariate polynomial (`x` outermost, coefficients an inner
`DensePoly`) as Mathlib's `(R[X])[X]`: the outer `toPolynomial` followed by mapping every
coefficient through the ring equivalence. Satellites: the coefficient reading, injectivity,
ring-operation transport, and degree preservation. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- The bivariate bridge: read `DensePoly (DensePoly R)` as `Polynomial (Polynomial R)`. -/
noncomputable def toPolynomial₂ (p : DensePoly (DensePoly R)) : Polynomial (Polynomial R) :=
  (toPolynomial p).map (equiv (R := R)).toRingHom

/-- Coefficient reading: the `i`-th coefficient is the bridged inner polynomial. -/
@[simp] theorem toPolynomial₂_coeff (p : DensePoly (DensePoly R)) (i : ℕ) :
    (toPolynomial₂ p).coeff i = toPolynomial (p.coeff i) := by
  rw [toPolynomial₂, Polynomial.coeff_map, coeff_toPolynomial]
  rfl

/-- The bivariate bridge is injective. -/
theorem toPolynomial₂_injective : Function.Injective (toPolynomial₂ (R := R)) :=
  fun _ _ h => toPolynomial_injective
    (Polynomial.map_injective _ (RingEquiv.injective _) h)

@[simp] theorem toPolynomial₂_zero : toPolynomial₂ (0 : DensePoly (DensePoly R)) = 0 := by
  rw [toPolynomial₂, toPolynomial_zero, Polynomial.map_zero]

@[simp] theorem toPolynomial₂_one : toPolynomial₂ (1 : DensePoly (DensePoly R)) = 1 := by
  rw [toPolynomial₂, toPolynomial_one, Polynomial.map_one]

@[simp] theorem toPolynomial₂_add (p q : DensePoly (DensePoly R)) :
    toPolynomial₂ (p + q) = toPolynomial₂ p + toPolynomial₂ q := by
  rw [toPolynomial₂, toPolynomial_add, Polynomial.map_add]
  rfl

@[simp] theorem toPolynomial₂_sub (p q : DensePoly (DensePoly R)) :
    toPolynomial₂ (p - q) = toPolynomial₂ p - toPolynomial₂ q := by
  rw [toPolynomial₂, toPolynomial_sub, Polynomial.map_sub]
  rfl

@[simp] theorem toPolynomial₂_mul (p q : DensePoly (DensePoly R)) :
    toPolynomial₂ (p * q) = toPolynomial₂ p * toPolynomial₂ q := by
  rw [toPolynomial₂, toPolynomial_mul, Polynomial.map_mul]
  rfl

/-- The bridge sends inner-polynomial constants to `Polynomial.C` of the bridged inner
polynomial. -/
@[simp] theorem toPolynomial₂_C (c : DensePoly R) :
    toPolynomial₂ (C c : DensePoly (DensePoly R)) = Polynomial.C (toPolynomial c) := by
  rw [toPolynomial₂, toPolynomial_C, Polynomial.map_C]
  rfl

/-- The bridge preserves the (outer) degree. -/
theorem toPolynomial₂_natDegree (p : DensePoly (DensePoly R)) :
    (toPolynomial₂ p).natDegree = (toPolynomial p).natDegree :=
  Polynomial.natDegree_map_eq_of_injective (RingEquiv.injective _) _

/-- The bridge transports outer resultants: reading a resultant over `DensePoly R` through
`toPolynomial` computes the resultant of the bridged bivariate polynomials. -/
theorem toPolynomial_resultant₂ (p q : DensePoly (DensePoly R)) (m n : ℕ) :
    toPolynomial (Polynomial.resultant (toPolynomial p) (toPolynomial q) m n)
      = Polynomial.resultant (toPolynomial₂ p) (toPolynomial₂ q) m n := by
  rw [toPolynomial₂, toPolynomial₂, Polynomial.resultant_map_map]
  rfl

/-- The bridge reflects zero. -/
theorem toPolynomial₂_ne_zero {p : DensePoly (DensePoly R)} (hp : p ≠ 0) :
    toPolynomial₂ p ≠ 0 :=
  fun h => hp (toPolynomial₂_injective (by rw [h, toPolynomial₂_zero]))

end DensePoly

end DeepWiki.CAlgebra
