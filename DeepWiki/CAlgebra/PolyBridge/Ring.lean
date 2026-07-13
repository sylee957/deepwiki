import DeepWiki.CAlgebra.PolyBridge.Basic

/-! # `CommRing (DensePoly R)` and divisibility reflection

The normalized dense polynomials form a commutative ring. It is **hand-built and fully computable**:
the arithmetic fields are the computable `Operations` (`+`/`-`/`*`/`neg`), the ring axioms are proved
by transport through injective `toPolynomial`, and the auxiliary ops (`•`/`^`/casts) fall to Lean's
computable defaults (`nsmulRec`/`npowRec`/`Nat.unaryCast`) — deliberately NOT the noncomputable
`Function.Injective.commRing` (which has no compiled path). So nothing noncomputable is bundled onto
the compute type, matching Hex's discipline. With the ring in place, `equiv` is a ring isomorphism and
divisibility both preserves and *reflects* (`toPolynomial_dvd_iff`). -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- `toPolynomial` intertwines subtraction. -/
@[simp] theorem toPolynomial_sub (p q : DensePoly R) :
    toPolynomial (p - q) = toPolynomial p - toPolynomial q := by
  ext n; simp [Polynomial.coeff_sub, DensePoly.coeff_sub]

/-- The commutative ring structure on dense polynomials — hand-built and computable. Arithmetic
fields are the `Operations` instances; axioms are proved by transport through `toPolynomial`;
`nsmul`/`zsmul`/`npow`/`natCast`/`intCast` fall to Lean's computable defaults. -/
instance : CommRing (DensePoly R) where
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  sub := (· - ·)
  zero := 0
  one := 1
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := toPolynomial_injective (by simp only [toPolynomial_add]; ring)
  zero_add a := toPolynomial_injective (by simp)
  add_zero a := toPolynomial_injective (by simp)
  add_comm a b := toPolynomial_injective (by simp only [toPolynomial_add]; ring)
  mul_assoc a b c := toPolynomial_injective (by simp only [toPolynomial_mul]; ring)
  one_mul a := toPolynomial_injective (by simp)
  mul_one a := toPolynomial_injective (by simp)
  left_distrib a b c := toPolynomial_injective (by simp only [toPolynomial_add, toPolynomial_mul]; ring)
  right_distrib a b c := toPolynomial_injective (by simp only [toPolynomial_add, toPolynomial_mul]; ring)
  mul_comm a b := toPolynomial_injective (by simp only [toPolynomial_mul]; ring)
  neg_add_cancel a :=
    toPolynomial_injective (by simp only [toPolynomial_add, toPolynomial_neg, toPolynomial_zero]; ring)
  zero_mul a := toPolynomial_injective (by simp)
  mul_zero a := toPolynomial_injective (by simp)
  sub_eq_add_neg a b := rfl

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

end DeepWiki.CAlgebra
