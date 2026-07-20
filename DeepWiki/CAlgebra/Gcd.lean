import DeepWiki.CAlgebra.Gcd.Euclid
import DeepWiki.CAlgebra.Gcd.Subresultant

/-! # The dense-polynomial gcd interface (`DensePolyGcd`)

Algorithm-selection class for the gcd of dense polynomials: instances choose an algorithm per
coefficient carrier, and the class fields are the gcd universal property, so any two instances'
outputs are associated and no consumer can distinguish them — algorithm choice is a pure
performance decision, invisible to every proof. The generic default is the subresultant PRS;
`ℚ` overrides to the Euclidean algorithm. Carrier-specific overrides are one-line
higher-priority instances. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Field R] [DecidableEq R]

/-- Algorithm-selection class for the dense-polynomial gcd: the fields are the gcd universal
property, so all instances agree up to units. -/
class DensePolyGcd (R : Type u) [Field R] [DecidableEq R] where
  /-- The selected gcd algorithm. -/
  gcd : DensePoly R → DensePoly R → DensePoly R
  /-- The selected gcd divides its left argument. -/
  gcd_dvd_left : ∀ p q, gcd p q ∣ p
  /-- The selected gcd divides its right argument. -/
  gcd_dvd_right : ∀ p q, gcd p q ∣ q
  /-- Any common divisor divides the selected gcd. -/
  dvd_gcd : ∀ {d} p q, d ∣ p → d ∣ q → d ∣ gcd p q

/-- Default algorithm for any carrier: the subresultant PRS. -/
instance (priority := 100) : DensePolyGcd R where
  gcd := DensePoly.gcdSubresultant
  gcd_dvd_left := DensePoly.gcdSubresultant_dvd_left
  gcd_dvd_right := DensePoly.gcdSubresultant_dvd_right
  dvd_gcd := fun p q h1 h2 => DensePoly.dvd_gcdSubresultant p q h1 h2

/-- `ℚ` override: the Euclidean algorithm (measured faster on cheap-coefficient carriers). -/
instance (priority := 200) : DensePolyGcd ℚ where
  gcd := DensePoly.gcdEuclid
  gcd_dvd_left := DensePoly.gcdEuclid_dvd_left
  gcd_dvd_right := DensePoly.gcdEuclid_dvd_right
  dvd_gcd := fun p q h1 h2 => DensePoly.dvd_gcdEuclid p q h1 h2

namespace DensePolyGcd

variable [DensePolyGcd R]

/-- The selected gcd of a pair with nonzero right argument is nonzero. -/
theorem gcd_ne_zero_of_right {q : DensePoly R} (hq : q ≠ 0) (p : DensePoly R) : gcd p q ≠ 0 :=
  fun h0 => hq (zero_dvd_iff.mp (h0 ▸ gcd_dvd_right p q))

/-- Every instance's gcd is associated to Mathlib's generic Euclidean-domain gcd. -/
theorem associated_euclideanDomain_gcd (p q : DensePoly R) :
    Associated (EuclideanDomain.gcd p q) (gcd p q) :=
  associated_of_dvd_dvd
    (dvd_gcd p q (EuclideanDomain.gcd_dvd_left p q) (EuclideanDomain.gcd_dvd_right p q))
    (EuclideanDomain.dvd_gcd (gcd_dvd_left p q) (gcd_dvd_right p q))

/-- Every instance's gcd is associated to the Euclidean reference algorithm (so any two
instances' outputs are associated to each other). -/
theorem gcd_associated_gcdEuclid (p q : DensePoly R) :
    Associated (gcd p q) (DensePoly.gcdEuclid p q) :=
  associated_of_dvd_dvd
    (DensePoly.dvd_gcdEuclid p q (gcd_dvd_left p q) (gcd_dvd_right p q))
    (dvd_gcd p q (DensePoly.gcdEuclid_dvd_left p q) (DensePoly.gcdEuclid_dvd_right p q))

end DensePolyGcd

open Polynomial in
/-- The selected gcd is `Associated` to Mathlib's polynomial gcd under `toPolynomial` — soundness
by forward transport, completeness by reverse transport, independent of the chosen instance. -/
theorem toPolynomial_gcd_associated [DensePolyGcd R] (p q : DensePoly R) :
    Associated (toPolynomial (DensePolyGcd.gcd p q))
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  apply associated_of_dvd_dvd
  · apply EuclideanDomain.dvd_gcd
    · exact toPolynomial_dvd (DensePolyGcd.gcd_dvd_left p q)
    · exact toPolynomial_dvd (DensePolyGcd.gcd_dvd_right p q)
  · have hgp : ofPolynomial (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) ∣ p :=
      dvd_of_toPolynomial_dvd (by rw [toPolynomial_ofPolynomial]; exact EuclideanDomain.gcd_dvd_left _ _)
    have hgq : ofPolynomial (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) ∣ q :=
      dvd_of_toPolynomial_dvd (by rw [toPolynomial_ofPolynomial]; exact EuclideanDomain.gcd_dvd_right _ _)
    have hfin := toPolynomial_dvd (DensePolyGcd.dvd_gcd p q hgp hgq)
    rwa [toPolynomial_ofPolynomial] at hfin

end DeepWiki.CAlgebra
