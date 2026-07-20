import DeepWiki.CAlgebra.Poly.Derivative
import DeepWiki.CAlgebra.Gcd
import Mathlib.FieldTheory.Perfect

/-! # Squarefreeness of dense polynomials

The squarefree kernel over a perfect field (in particular any field of characteristic zero):
the derivative criterion `Squarefree p ↔ IsCoprime p (deriv p)` by transport through the bridge
and Mathlib's `separable_iff_squarefree`, the resulting **decidability of `Squarefree`** (a gcd
size test, hypothesis-free), and the squarefree part `sqfreePart p = p / gcd(p, deriv p)` with its
exact-division satellites. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

/-! ### Bridge transports for unit, squarefree, and coprimality predicates -/

/-- Units correspond across the bridge. -/
theorem isUnit_toPolynomial_iff {p : DensePoly R} : IsUnit (toPolynomial p) ↔ IsUnit p := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h.exists_right_inv
    refine ⟨⟨p, ofPolynomial y, ?_, ?_⟩, rfl⟩
    · exact toPolynomial_injective (by
        rw [toPolynomial_mul, toPolynomial_ofPolynomial, toPolynomial_one, hy])
    · exact toPolynomial_injective (by
        rw [toPolynomial_mul, toPolynomial_ofPolynomial, toPolynomial_one, mul_comm]
        exact hy)
  · exact fun h => h.map (equiv (R := R)).toRingHom

/-- Squarefreeness corresponds across the bridge. -/
theorem squarefree_toPolynomial_iff {p : DensePoly R} :
    Squarefree (toPolynomial p) ↔ Squarefree p := by
  constructor
  · intro h x hx
    exact isUnit_toPolynomial_iff.mp
      (h (toPolynomial x) (by rw [← toPolynomial_mul]; exact toPolynomial_dvd hx))
  · intro h X hX
    rw [← toPolynomial_ofPolynomial X] at hX ⊢
    exact isUnit_toPolynomial_iff.mpr
      (h (ofPolynomial X) (dvd_of_toPolynomial_dvd (by rwa [toPolynomial_mul])))

/-- Coprimality corresponds across the bridge. -/
theorem isCoprime_toPolynomial_iff {p q : DensePoly R} :
    IsCoprime (toPolynomial p) (toPolynomial q) ↔ IsCoprime p q := by
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨ofPolynomial a, ofPolynomial b, toPolynomial_injective ?_⟩
    rw [toPolynomial_add, toPolynomial_mul, toPolynomial_mul, toPolynomial_ofPolynomial,
      toPolynomial_ofPolynomial, toPolynomial_one]
    exact hab
  · exact fun h => h.map (equiv (R := R)).toRingHom

/-- Derivative criterion for squarefreeness over a perfect field (e.g. characteristic zero):
`p` is squarefree iff it is coprime to its derivative. Hypothesis-free: at `p = 0` both sides
fail. -/
theorem squarefree_iff_isCoprime_deriv [PerfectField R] {p : DensePoly R} :
    Squarefree p ↔ IsCoprime p (deriv p) := by
  rw [← squarefree_toPolynomial_iff, ← PerfectField.separable_iff_squarefree,
    Polynomial.separable_def, ← toPolynomial_deriv, isCoprime_toPolynomial_iff]

/-- Squarefreeness is a gcd size test: `p` is squarefree iff `gcd(p, deriv p)` is a constant. -/
theorem squarefree_iff_gcd_deriv_size [PerfectField R] [DensePolyGcd R] {p : DensePoly R} :
    Squarefree p ↔ (DensePolyGcd.gcd p (deriv p)).size = 1 := by
  rw [squarefree_iff_isCoprime_deriv, DensePolyGcd.isCoprime_iff_isUnit_gcd,
    isUnit_iff_size_eq_one]

/-- Squarefreeness of dense polynomials is decidable (compute the gcd, test its size). -/
instance [PerfectField R] [DensePolyGcd R] :
    DecidablePred (Squarefree : DensePoly R → Prop) := fun _ =>
  decidable_of_iff _ squarefree_iff_gcd_deriv_size.symm

variable [DensePolyGcd R]

/-- The squarefree part: `p` divided by `gcd(p, deriv p)`. -/
def sqfreePart (p : DensePoly R) : DensePoly R := div p (DensePolyGcd.gcd p (deriv p))

/-- The gcd with the derivative reconstructs `p` against the squarefree part (exact division). -/
theorem gcd_deriv_mul_sqfreePart {p : DensePoly R} (hp : p ≠ 0) :
    DensePolyGcd.gcd p (deriv p) * sqfreePart p = p :=
  EuclideanDomain.mul_div_cancel' (DensePolyGcd.gcd_ne_zero_of_left hp _)
    (DensePolyGcd.gcd_dvd_left p (deriv p))

/-- The squarefree part divides `p`. -/
theorem sqfreePart_dvd (p : DensePoly R) : sqfreePart p ∣ p := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact dvd_zero _
  · exact ⟨DensePolyGcd.gcd p (deriv p),
      (gcd_deriv_mul_sqfreePart hp).symm.trans (mul_comm _ _)⟩

/-- The squarefree part of a nonzero polynomial is nonzero. -/
theorem sqfreePart_ne_zero {p : DensePoly R} (hp : p ≠ 0) : sqfreePart p ≠ 0 := fun h0 =>
  hp (by rw [← gcd_deriv_mul_sqfreePart hp, h0, mul_zero])

end DensePoly

end DeepWiki.CAlgebra
