import DeepWiki.CAlgebra.PolyBridge.Basic

/-! # `CommRing (DensePoly R)` and divisibility reflection

The normalized dense polynomials form a commutative ring, pulled back along the injective
`toPolynomial`. The computable core (`+`, `-`, `*`) is the arithmetic from `Operations`; the
rarely-computed auxiliary operations (`•`, `^`, casts) are defined through the bridge so their
homomorphism laws are immediate. With the ring in place, `equiv` upgrades to a genuine isomorphism
of rings, and divisibility both preserves and *reflects* (`toPolynomial_dvd_iff`) — the first
concrete instance of completeness-by-reverse-transport. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

noncomputable section

/-- Scalar action of `ℕ`, defined through the bridge. -/
instance : SMul ℕ (DensePoly R) where smul n a := ofPolynomial (n • toPolynomial a)
/-- Scalar action of `ℤ`, defined through the bridge. -/
instance : SMul ℤ (DensePoly R) where smul n a := ofPolynomial (n • toPolynomial a)
/-- Natural-number power, defined through the bridge. -/
instance : Pow (DensePoly R) ℕ where pow a n := ofPolynomial (toPolynomial a ^ n)
/-- Natural-number cast, defined through the bridge. -/
instance : NatCast (DensePoly R) where natCast n := ofPolynomial (n : Polynomial R)
/-- Integer cast, defined through the bridge. -/
instance : IntCast (DensePoly R) where intCast n := ofPolynomial (n : Polynomial R)

/-- `toPolynomial` intertwines subtraction. -/
@[simp] theorem toPolynomial_sub (p q : DensePoly R) :
    toPolynomial (p - q) = toPolynomial p - toPolynomial q := by
  ext n; simp [Polynomial.coeff_sub, DensePoly.coeff_sub]

/-- The commutative ring structure on dense polynomials, pulled back along injective
`toPolynomial`; the ring operations agree with Mathlib's via the homomorphism squares. -/
instance : CommRing (DensePoly R) :=
  toPolynomial_injective.commRing toPolynomial
    toPolynomial_zero toPolynomial_one toPolynomial_add toPolynomial_mul toPolynomial_neg
    toPolynomial_sub
    (fun n a => toPolynomial_ofPolynomial (n • toPolynomial a))
    (fun n a => toPolynomial_ofPolynomial (n • toPolynomial a))
    (fun a n => toPolynomial_ofPolynomial (toPolynomial a ^ n))
    (fun n => toPolynomial_ofPolynomial (n : Polynomial R))
    (fun n => toPolynomial_ofPolynomial (n : Polynomial R))

/-- `equiv` as a ring isomorphism between the two commutative rings. -/
theorem toPolynomial_ringHom_apply (p : DensePoly R) : equiv p = toPolynomial p := rfl

/-! ### Divisibility transports and reflects -/

/-- Divisibility is preserved by `toPolynomial` (soundness direction). -/
theorem toPolynomial_dvd {p q : DensePoly R} (h : p ∣ q) : toPolynomial p ∣ toPolynomial q := by
  rcases h with ⟨r, rfl⟩; exact ⟨toPolynomial r, by rw [toPolynomial_mul]⟩

/-- Divisibility is reflected by `toPolynomial` (completeness direction, via reverse transport). -/
theorem dvd_of_toPolynomial_dvd {p q : DensePoly R}
    (h : toPolynomial p ∣ toPolynomial q) : p ∣ q := by
  rcases h with ⟨s, hs⟩
  refine ⟨ofPolynomial s, toPolynomial_injective ?_⟩
  rw [toPolynomial_mul, toPolynomial_ofPolynomial, hs]

/-- `toPolynomial` both preserves and reflects divisibility: dense polynomials divide one another
exactly when their Mathlib images do. This is the reflection the ring isomorphism buys. -/
@[simp] theorem toPolynomial_dvd_iff {p q : DensePoly R} :
    toPolynomial p ∣ toPolynomial q ↔ p ∣ q :=
  ⟨dvd_of_toPolynomial_dvd, toPolynomial_dvd⟩

/-- Validation: `equiv` preserves the ring `1` and the reflection holds as an iff. -/
example : equiv (1 : DensePoly R) = 1 := map_one equiv
example (p q : DensePoly R) : p ∣ q ↔ toPolynomial p ∣ toPolynomial q := toPolynomial_dvd_iff.symm

end

end DeepWiki.CAlgebra
