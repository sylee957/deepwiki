import DeepWiki.CAlgebra.Resultant.Euclidean

/-! # Switchable resultant for `DensePoly`

`DensePolyResultant` packages a resultant algorithm with its contract — agreement with
Mathlib's Sylvester-determinant `Polynomial.resultant` on valid degree bounds — so consumers
depend only on the spec while instance priority selects the algorithm: the Euclidean-descent
pseudo-remainder sequence where the coefficients form a computable Euclidean domain
(polynomial-time), the Sylvester determinant as the total fallback. -/

namespace DeepWiki.CAlgebra

universe u

/-- A resultant algorithm together with its contract: on valid degree bounds it agrees with
Mathlib's `Polynomial.resultant` of the bridged polynomials. -/
class DensePolyResultant (S : Type u) [CommRing S] [DecidableEq S] where
  /-- The resultant of `p, q` under degree bounds `m, n`. -/
  resultant : DensePoly S → DensePoly S → ℕ → ℕ → S
  /-- Agreement with the Sylvester-determinant resultant on valid bounds. -/
  resultant_eq : ∀ p q m n, (toPolynomial p).natDegree ≤ m →
    (toPolynomial q).natDegree ≤ n →
    resultant p q m n = (toPolynomial p).resultant (toPolynomial q) m n

/-- Default algorithm: the Sylvester determinant (total; factorial-time). -/
instance (priority := 100) {S : Type u} [CommRing S] [DecidableEq S] :
    DensePolyResultant S where
  resultant := DeepWiki.CAlgebra.resultant
  resultant_eq p q m n _ _ := toPolynomial_resultant p q m n

/-- Euclidean-descent algorithm: the pseudo-remainder sequence, where the coefficients form
a computable Euclidean domain — polynomial-time, wins the dispatch. -/
instance (priority := 200) prsDensePolyResultant {S : Type u} [EuclideanDomain S]
    [DecidableEq S] : DensePolyResultant S where
  resultant := DensePoly.resultantPRS
  resultant_eq p q m n hm hn := DensePoly.resultantPRS_eq p q m n hm hn

end DeepWiki.CAlgebra
