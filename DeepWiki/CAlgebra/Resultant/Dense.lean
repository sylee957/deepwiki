import DeepWiki.CAlgebra.Resultant.Euclidean

/-! # Switchable resultant for `DensePoly`

`DensePolyResultant` packages a resultant algorithm with its contract — agreement with
Mathlib's Sylvester-determinant `Polynomial.resultant` on valid degree bounds — so consumers
depend only on the spec while instance priority selects the algorithm: the Euclidean-descent
pseudo-remainder sequence where the coefficients form a computable Euclidean domain
(polynomial-time), the Sylvester determinant as the total fallback. -/

namespace DeepWiki.CAlgebra

universe u

/-- A resultant algorithm together with its contract: it agrees with Mathlib's
`Polynomial.resultant` **at the canonical degree bounds** — the normalized representation
always knows the exact degrees, so no bound parameters and no side conditions. -/
class DensePolyResultant (S : Type u) [CommRing S] [DecidableEq S] where
  /-- The resultant of `p, q` (at their exact degrees). -/
  resultant : DensePoly S → DensePoly S → S
  /-- Agreement with the Sylvester-determinant resultant at the canonical bounds. -/
  resultant_eq : ∀ p q, resultant p q
    = (toPolynomial p).resultant (toPolynomial q)
        (toPolynomial p).natDegree (toPolynomial q).natDegree

/-- Default algorithm: the Sylvester determinant (total; factorial-time). -/
instance (priority := 100) {S : Type u} [CommRing S] [DecidableEq S] :
    DensePolyResultant S where
  resultant := DeepWiki.CAlgebra.resultant
  resultant_eq := toPolynomial_resultant

/-- Euclidean-descent algorithm: the pseudo-remainder sequence, where the coefficients form
a computable Euclidean domain — polynomial-time, wins the dispatch. -/
instance (priority := 200) prsDensePolyResultant {S : Type u} [EuclideanDomain S]
    [DecidableEq S] : DensePolyResultant S where
  resultant := DensePoly.resultantPRS
  resultant_eq := DensePoly.resultantPRS_eq

end DeepWiki.CAlgebra
