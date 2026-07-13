import DeepWiki.CAlgebra.Poly.Euclid
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # gcd correspondence: the executable Euclidean gcd matches Mathlib's

The computable `DensePoly.gcd` is transported through `toPolynomial` to Mathlib's
`EuclideanDomain.gcd`. The correspondence is up to `Associated` (a unit multiple), not equality:
the executable gcd returns the raw last Euclidean remainder, while `EuclideanDomain.gcd` is
normalized. The proof needs no new gcd theory — it transports the intrinsic universal property
(`gcd_dvd_left`/`gcd_dvd_right`/`dvd_gcd`) across the divisibility reflection `toPolynomial_dvd_iff`,
which is exactly the completeness-by-reverse-transport the canonical representation buys. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Field R] [DecidableEq R]

noncomputable section

/-- The executable gcd is `Associated` to Mathlib's normalized polynomial gcd under `toPolynomial`:
it divides the same things (soundness, forward transport) and is divisible by every common divisor
(completeness, reverse transport). -/
theorem toPolynomial_gcd_associated (p q : DensePoly R) :
    Associated (toPolynomial (DensePoly.gcd p q))
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  apply associated_of_dvd_dvd
  · -- soundness: the executable gcd divides both images, so divides their Mathlib gcd
    apply EuclideanDomain.dvd_gcd
    · exact toPolynomial_dvd (DensePoly.gcd_dvd_left p q)
    · exact toPolynomial_dvd (DensePoly.gcd_dvd_right p q)
  · -- completeness: pull Mathlib's gcd back, use the executable greatest property, push forward
    have hgp : ofPolynomial (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) ∣ p :=
      dvd_of_toPolynomial_dvd (by rw [toPolynomial_ofPolynomial]; exact EuclideanDomain.gcd_dvd_left _ _)
    have hgq : ofPolynomial (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) ∣ q :=
      dvd_of_toPolynomial_dvd (by rw [toPolynomial_ofPolynomial]; exact EuclideanDomain.gcd_dvd_right _ _)
    have hfin := toPolynomial_dvd (DensePoly.dvd_gcd p q hgp hgq)
    rwa [toPolynomial_ofPolynomial] at hfin

/-- Ring-equivalence form: `equiv` sends the executable gcd to a polynomial associated to Mathlib's
normalized gcd. -/
theorem equiv_gcd_associated (p q : DensePoly R) :
    Associated (equiv (DensePoly.gcd p q)) (EuclideanDomain.gcd (equiv p) (equiv q)) := by
  simpa using toPolynomial_gcd_associated p q

/-- Validation: the executable gcd and Mathlib's gcd divide each other (are associated). -/
example (p q : DensePoly R) :
    toPolynomial (DensePoly.gcd p q) ∣ EuclideanDomain.gcd (toPolynomial p) (toPolynomial q) ∧
    EuclideanDomain.gcd (toPolynomial p) (toPolynomial q) ∣ toPolynomial (DensePoly.gcd p q) :=
  ⟨(toPolynomial_gcd_associated p q).dvd, (toPolynomial_gcd_associated p q).symm.dvd⟩

end

end DeepWiki.CAlgebra
