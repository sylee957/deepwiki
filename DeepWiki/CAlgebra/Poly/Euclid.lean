import DeepWiki.CAlgebra.Poly.Division
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # `DensePoly` over a field as a Euclidean domain

The computable `EuclideanDomain (DensePoly R)` instance — division data is the executable
`div`/`mod`, the Euclidean measure is `size` — with the size lemmas backing it. -/

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

/-- Units of the dense polynomial ring over a field are exactly the nonzero constants. -/
theorem exists_C_of_isUnit {u : DensePoly R} (hu : IsUnit u) : ∃ c : R, c ≠ 0 ∧ u = C c := by
  obtain ⟨w, hw⟩ := hu
  have hmul : u * ↑w⁻¹ = 1 := by rw [← hw]; exact w.mul_inv
  have hu0 : u ≠ 0 := fun h0 => by rw [h0, zero_mul] at hmul; exact zero_ne_one hmul
  have hv0 : (↑w⁻¹ : DensePoly R) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hmul; exact zero_ne_one hmul
  have hsize := size_mul hu0 hv0
  rw [hmul, size_one] at hsize
  have hupos : u.size ≠ 0 := fun h0 => hu0 (eq_zero_of_size_zero h0)
  have hvpos : (↑w⁻¹ : DensePoly R).size ≠ 0 := fun h0 => hv0 (eq_zero_of_size_zero h0)
  have hu1 : u.size = 1 := by omega
  refine ⟨u.coeff 0, ?_, eq_C_of_size_eq_one hu1⟩
  have hlast := coeff_last_ne_zero_of_pos_size u (by omega)
  rwa [hu1] at hlast

/-- Divisors of a nonzero polynomial have no larger size. -/
theorem size_le_size_of_dvd {p q : DensePoly R} (hq : q ≠ 0) (hpq : p ∣ q) : p.size ≤ q.size := by
  have hp : p ≠ 0 := fun h0 => hq (by simpa [h0] using zero_dvd_iff.mp (h0 ▸ hpq))
  have h := Polynomial.natDegree_le_of_dvd (toPolynomial_dvd hpq) (toPolynomial_ne_zero hq)
  have h1 := size_eq_natDegree_add_one hp
  have h2 := size_eq_natDegree_add_one hq
  omega

/-- Units of the dense polynomial ring are exactly the size-`1` polynomials. -/
theorem isUnit_iff_size_eq_one {u : DensePoly R} : IsUnit u ↔ u.size = 1 := by
  constructor
  · intro hu
    obtain ⟨c, hc, rfl⟩ := exists_C_of_isUnit hu
    exact size_C hc
  · intro hs
    have hc : u.coeff 0 ≠ 0 := by
      have h := coeff_last_ne_zero_of_pos_size u (by omega)
      simpa [hs] using h
    rw [eq_C_of_size_eq_one hs]
    exact isUnit_C hc

/-- `toPolynomial` transports the leading coefficient of a nonzero polynomial. -/
theorem leadingCoeff_toPolynomial {p : DensePoly R} (hp : p ≠ 0) :
    (toPolynomial p).leadingCoeff = p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, coeff_toPolynomial, DensePoly.leadingCoeff]
  congr 1
  have := size_eq_natDegree_add_one hp
  omega

/-- Leading coefficients are multiplicative (nonzero polynomials over a field). -/
theorem leadingCoeff_mul {p q : DensePoly R} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).leadingCoeff = p.leadingCoeff * q.leadingCoeff := by
  rw [← leadingCoeff_toPolynomial (mul_ne_zero hp hq), ← leadingCoeff_toPolynomial hp,
    ← leadingCoeff_toPolynomial hq, toPolynomial_mul, Polynomial.leadingCoeff_mul]

/-- `DensePoly` over a field is a Euclidean domain: division data is the executable `div`/`mod`,
the Euclidean measure is `size`. Mathlib's generic `EuclideanDomain.gcd`/`xgcd` and Bézout theory
then apply to the dense carrier — and compute, since the instance data is computable. -/
instance : EuclideanDomain (DensePoly R) :=
  { (inferInstance : CommRing (DensePoly R)),
    (inferInstance : Nontrivial (DensePoly R)) with
    quotient := div
    quotient_zero := div_zero
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


end DensePoly

end DeepWiki.CAlgebra
