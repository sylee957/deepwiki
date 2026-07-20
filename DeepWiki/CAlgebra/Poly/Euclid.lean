import DeepWiki.CAlgebra.Poly.Gcd

/-! # `DensePoly` over a field as a Euclidean domain

The computable `EuclideanDomain (DensePoly R)` instance — division data is the executable
`div`/`mod`, the Euclidean measure is `size` — with the size lemmas backing it, and the agreement
of Mathlib's generic `EuclideanDomain.gcd` with the executable `gcd`. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

/-- `size` reads as Mathlib's `natDegree + 1` on nonzero polynomials. -/
theorem size_eq_natDegree_add_one {p : DensePoly R} (hp : p ≠ 0) :
    p.size = (toPolynomial p).natDegree + 1 := by
  have h := natDegree_toPolynomial p
  have hs : p.size ≠ 0 := fun h0 => hp (eq_zero_of_size_zero h0)
  simp only [degree?, if_neg hs, Option.getD_some] at h
  omega

/-- Sizes of nonzero polynomials are additive under multiplication (minus the shared constant). -/
theorem size_mul {p q : DensePoly R} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).size = p.size + q.size - 1 := by
  rw [size_eq_natDegree_add_one (mul_ne_zero hp hq), size_eq_natDegree_add_one hp,
    size_eq_natDegree_add_one hq, toPolynomial_mul,
    Polynomial.natDegree_mul (toPolynomial_ne_zero hp) (toPolynomial_ne_zero hq)]
  omega

/-- `DensePoly` over a field is a Euclidean domain: division data is the executable `div`/`mod`,
the Euclidean measure is `size`. Mathlib's generic `EuclideanDomain.gcd`/`xgcd` and Bézout theory
then apply to the dense carrier — and compute, since the instance data is computable. -/
instance : EuclideanDomain (DensePoly R) :=
  { (inferInstance : CommRing (DensePoly R)),
    (inferInstance : Nontrivial (DensePoly R)) with
    quotient := div
    quotient_zero := fun p => by
      simp only [div, divMod]
      rw [divModAux.eq_def, if_pos (Or.inr size_zero)]
    remainder := mod
    quotient_mul_add_remainder_eq := fun a b => by
      rw [mul_comm]; exact divMod_spec a b
    r := fun a b => a.size < b.size
    r_wellFounded := (measure size).wf
    remainder_lt := fun a {b} hb => mod_size_lt (fun h0 => hb (eq_zero_of_size_zero h0)) a
    mul_left_not_lt := fun a {b} hb => by
      rcases eq_or_ne a 0 with rfl | ha
      · rw [zero_mul]; exact lt_irrefl _
      · have hs := size_mul ha hb
        have hbs : b.size ≠ 0 := fun h0 => hb (eq_zero_of_size_zero h0)
        omega }

/-- Mathlib's generic Euclidean-domain gcd and the executable `gcd` agree up to a unit (both
satisfy the same universal property). -/
theorem euclideanDomain_gcd_associated_gcd (p q : DensePoly R) :
    Associated (EuclideanDomain.gcd p q) (gcd p q) :=
  associated_of_dvd_dvd
    (dvd_gcd p q (EuclideanDomain.gcd_dvd_left p q) (EuclideanDomain.gcd_dvd_right p q))
    (EuclideanDomain.dvd_gcd (gcd_dvd_left p q) (gcd_dvd_right p q))

end DensePoly

end DeepWiki.CAlgebra
