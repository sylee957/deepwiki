import DeepWiki.CAlgebra.Resultant.Euclidean

/-! # Switchable resultant for `DensePoly`

`DensePolyResultant` packages a resultant algorithm with its contract — agreement with
Mathlib's Sylvester-determinant `Polynomial.resultant` on valid degree bounds — so consumers
depend only on the spec while instance priority selects the algorithm: the Euclidean-descent
pseudo-remainder sequence where the coefficients form a computable Euclidean domain
(polynomial-time), the Sylvester determinant as the total fallback. -/

namespace DeepWiki.CAlgebra

universe u

/-- The normalized representation commits the degree: `size − 1` is `natDegree`,
unconditionally (`0` included, by `ℕ`-subtraction). -/
private theorem natDeg_eq_size_sub_one {S : Type u} [CommRing S] [DecidableEq S]
    (p : DensePoly S) : (toPolynomial p).natDegree = p.size - 1 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [toPolynomial_zero, DensePoly.size_zero]
  · rw [natDegree_toPolynomial, DensePoly.degree?,
      if_neg (fun h0 => hp (DensePoly.eq_zero_of_size_zero h0))]
    rfl

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
  resultant p q := DeepWiki.CAlgebra.resultant p q (p.size - 1) (q.size - 1)
  resultant_eq p q := by
    rw [natDeg_eq_size_sub_one p, natDeg_eq_size_sub_one q]
    exact toPolynomial_resultant p q _ _

/-- Euclidean-descent algorithm: the pseudo-remainder sequence, where the coefficients form
a computable Euclidean domain — polynomial-time, wins the dispatch. -/
instance (priority := 200) prsDensePolyResultant {S : Type u} [EuclideanDomain S]
    [DecidableEq S] : DensePolyResultant S where
  resultant p q := DensePoly.resultantPRS p q (p.size - 1) (q.size - 1)
  resultant_eq p q := by
    rw [natDeg_eq_size_sub_one p, natDeg_eq_size_sub_one q]
    exact DensePoly.resultantPRS_eq p q _ _
      (le_of_eq (natDeg_eq_size_sub_one p)) (le_of_eq (natDeg_eq_size_sub_one q))

end DeepWiki.CAlgebra
