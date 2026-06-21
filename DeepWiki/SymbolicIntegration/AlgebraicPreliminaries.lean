import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Tactic

/-! # Algebraic preliminaries — the gcd predicate
Bronstein's Chapter 1 is standard constructive algebra, almost all of which is Mathlib's. The
one notion the book states as a *predicate* — rather than a chosen operation, as in Mathlib's
`GCDMonoid` — is the greatest common divisor of Definition 1.1.4. We add it here with its
satellite API and the uniqueness-up-to-units property (Theorem 1.1.1). -/

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommMonoidWithZero R]

/-- **Definition 1.1.4** (gcd): `z` is a greatest common divisor of `x` and `y` if it divides
both and every common divisor of `x` and `y` divides it. -/
def IsGCD (x y z : R) : Prop := z ∣ x ∧ z ∣ y ∧ ∀ t, t ∣ x → t ∣ y → t ∣ z

/-- A gcd divides its first argument. -/
theorem IsGCD.dvd_left {x y z : R} (h : IsGCD x y z) : z ∣ x := h.1

/-- A gcd divides its second argument. -/
theorem IsGCD.dvd_right {x y z : R} (h : IsGCD x y z) : z ∣ y := h.2.1

/-- A gcd is divisible by every common divisor. -/
theorem IsGCD.dvd {x y z t : R} (h : IsGCD x y z) (hx : t ∣ x) (hy : t ∣ y) : t ∣ z :=
  h.2.2 t hx hy

/-- The gcd predicate is symmetric in its two arguments. -/
theorem IsGCD.symm {x y z : R} (h : IsGCD x y z) : IsGCD y x z :=
  ⟨h.2.1, h.1, fun t hy hx => h.2.2 t hx hy⟩

/-- **Theorem 1.1.1**: a gcd is unique up to multiplication by a unit (i.e. two gcds of the same
pair are `Associated`). -/
theorem IsGCD.associated [IsCancelMulZero R] {x y z t : R} (hz : IsGCD x y z) (ht : IsGCD x y t) :
    Associated z t :=
  associated_of_dvd_dvd (ht.dvd hz.dvd_left hz.dvd_right) (hz.dvd ht.dvd_left ht.dvd_right)

end DeepWiki.SymbolicIntegration
