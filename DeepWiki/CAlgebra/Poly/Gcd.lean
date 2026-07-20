import DeepWiki.CAlgebra.Poly.Division
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Polynomial gcd via the Euclidean algorithm

`gcd p q` iterates `mod` to the last nonzero remainder; its universal property
(`gcd_dvd_left`/`gcd_dvd_right`/`dvd_gcd`) and the `Associated` correspondence to Mathlib's
`EuclideanDomain.gcd`, proved by transporting the universal property across the bridge. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

/-- Polynomial gcd via the Euclidean algorithm (last nonzero remainder). -/
def gcd (p q : DensePoly R) : DensePoly R :=
  if q.size = 0 then p else gcd q (mod p q)
  termination_by q.size
  decreasing_by
    rename_i h
    exact mod_size_lt h p

/-- The Euclidean gcd divides both arguments (soundness half of the gcd universal property). -/
theorem gcd_dvd (p q : DensePoly R) : gcd p q ∣ p ∧ gcd p q ∣ q := by
  induction p, q using gcd.induct with
  | case1 p q h =>
      rw [gcd.eq_def, if_pos h]
      exact ⟨dvd_refl p, by rw [eq_zero_of_size_zero h]; exact dvd_zero p⟩
  | case2 p q h ih =>
      rw [gcd.eq_def, if_neg h]
      refine ⟨?_, ih.1⟩
      have hp : div p q * q + mod p q = p := divMod_spec p q
      have key : gcd q (mod p q) ∣ div p q * q + mod p q :=
        dvd_add (ih.1.mul_left (div p q)) ih.2
      rwa [hp] at key

/-- The Euclidean gcd divides its left argument. -/
theorem gcd_dvd_left (p q : DensePoly R) : gcd p q ∣ p := (gcd_dvd p q).1

/-- The Euclidean gcd divides its right argument. -/
theorem gcd_dvd_right (p q : DensePoly R) : gcd p q ∣ q := (gcd_dvd p q).2

/-- The gcd of a pair with nonzero right argument is nonzero. -/
theorem gcd_ne_zero_of_right {q : DensePoly R} (hq : q ≠ 0) (p : DensePoly R) : gcd p q ≠ 0 :=
  fun h0 => hq (zero_dvd_iff.mp (h0 ▸ gcd_dvd_right p q))

/-- Any common divisor divides the gcd (greatest / completeness half of the universal property). -/
theorem dvd_gcd {d : DensePoly R} : ∀ p q, d ∣ p → d ∣ q → d ∣ gcd p q := by
  intro p q
  induction p, q using gcd.induct with
  | case1 p q h => intro hp _; rw [gcd.eq_def, if_pos h]; exact hp
  | case2 p q h ih =>
      intro hp hq
      rw [gcd.eq_def, if_neg h]
      refine ih hq ?_
      rw [mod_eq_sub]
      exact dvd_sub hp (hq.mul_left (div p q))

end DensePoly

/-! ### gcd correspondence to Mathlib's `EuclideanDomain.gcd` -/

open Polynomial in
variable {R : Type u} [Field R] [DecidableEq R] in
/-- The executable gcd is `Associated` to Mathlib's normalized polynomial gcd under `toPolynomial`:
it divides the same things (soundness, forward transport) and is divisible by every common divisor
(completeness, reverse transport). Up to `Associated` since the raw remainder isn't normalized. -/
theorem toPolynomial_gcd_associated (p q : DensePoly R) :
    Associated (toPolynomial (DensePoly.gcd p q))
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  apply associated_of_dvd_dvd
  · apply EuclideanDomain.dvd_gcd
    · exact toPolynomial_dvd (DensePoly.gcd_dvd_left p q)
    · exact toPolynomial_dvd (DensePoly.gcd_dvd_right p q)
  · have hgp : ofPolynomial (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) ∣ p :=
      dvd_of_toPolynomial_dvd (by rw [toPolynomial_ofPolynomial]; exact EuclideanDomain.gcd_dvd_left _ _)
    have hgq : ofPolynomial (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) ∣ q :=
      dvd_of_toPolynomial_dvd (by rw [toPolynomial_ofPolynomial]; exact EuclideanDomain.gcd_dvd_right _ _)
    have hfin := toPolynomial_dvd (DensePoly.dvd_gcd p q hgp hgq)
    rwa [toPolynomial_ofPolynomial] at hfin

end DeepWiki.CAlgebra
