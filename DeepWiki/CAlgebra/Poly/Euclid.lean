import DeepWiki.CAlgebra.Poly.Operations
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Euclidean division of normalized dense polynomials

Polynomial long division over a field: `divMod p q` returns `(quotient, remainder)` with
`quotient * q + remainder = p`. Defined by well-founded recursion on the remainder size; the
termination proof is the leading-term cancellation lemma `divStep_size_lt`. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

/-- One division step strictly decreases the remainder size (leading-term cancellation). -/
theorem divStep_size_lt {q r : DensePoly R} (hq : q.size ≠ 0) (hr : q.size ≤ r.size) :
    (r - monomial (r.size - q.size) (leadingCoeff r / leadingCoeff q) * q).size < r.size := by
  have hrpos : 0 < r.size := by omega
  have hqlc : leadingCoeff q ≠ 0 := leadingCoeff_ne_zero hq
  have hstep : ∀ j, r.size - 1 ≤ j →
      (r - monomial (r.size - q.size) (leadingCoeff r / leadingCoeff q) * q).coeff j = 0 := by
    intro j hj
    rw [coeff_sub, coeff_monomial_mul]
    rcases Nat.lt_or_ge j r.size with hjr | hjr
    · -- j = r.size - 1: leading terms cancel
      have hjeq : j = r.size - 1 := by omega
      subst hjeq
      rw [if_pos (show r.size - q.size ≤ r.size - 1 by omega),
        show r.size - 1 - (r.size - q.size) = q.size - 1 by omega]
      show leadingCoeff r - leadingCoeff r / leadingCoeff q * leadingCoeff q = 0
      rw [div_mul_cancel₀ (leadingCoeff r) hqlc, sub_self]
    · -- j ≥ r.size: both terms already zero
      rw [coeff_eq_zero_of_size_le r hjr]
      by_cases hkj : r.size - q.size ≤ j
      · rw [if_pos hkj, coeff_eq_zero_of_size_le q (by omega), mul_zero, sub_zero]
      · rw [if_neg hkj, sub_zero]
  have hsize := size_le_of_coeff_zero hstep
  omega

/-- Long-division accumulator: subtract leading terms until the remainder drops below `q`. -/
def divModAux (q : DensePoly R) (r quot : DensePoly R) : DensePoly R × DensePoly R :=
  if r.size < q.size ∨ q.size = 0 then (quot, r)
  else
    divModAux q (r - monomial (r.size - q.size) (leadingCoeff r / leadingCoeff q) * q)
              (quot + monomial (r.size - q.size) (leadingCoeff r / leadingCoeff q))
  termination_by r.size
  decreasing_by
    rename_i h
    simp only [not_or] at h
    exact divStep_size_lt h.2 (Nat.not_lt.mp h.1)

/-- Polynomial long division: `(quotient, remainder)`. Division by `0` returns `(0, p)`. -/
def divMod (p q : DensePoly R) : DensePoly R × DensePoly R := divModAux q p 0

/-- Quotient of polynomial long division. -/
def div (p q : DensePoly R) : DensePoly R := (divMod p q).1

/-- Remainder of polynomial long division. -/
def mod (p q : DensePoly R) : DensePoly R := (divMod p q).2

/-- The accumulator invariant: `Q * q + R = quot * q + r`. -/
theorem divModAux_spec (q r quot : DensePoly R) :
    (divModAux q r quot).1 * q + (divModAux q r quot).2 = quot * q + r := by
  induction r, quot using divModAux.induct (q := q) with
  | case1 r quot h => rw [divModAux.eq_def, if_pos h]
  | case2 r quot h ih => rw [divModAux.eq_def, if_neg h, ih]; ring

/-- Division reconstructs the dividend: `div p q * q + mod p q = p`. -/
theorem divMod_spec (p q : DensePoly R) : (divMod p q).1 * q + (divMod p q).2 = p := by
  rw [divMod, divModAux_spec]; simp

/-- Validation: `div`/`mod` reconstruct the dividend (the Euclidean division spec). -/
example (p q : DensePoly R) : div p q * q + mod p q = p := divMod_spec p q

/-- The remainder produced by `divModAux` has size below the divisor (for a nonzero divisor). -/
theorem divModAux_rem_size_lt {q : DensePoly R} (hq : q.size ≠ 0) (r quot : DensePoly R) :
    (divModAux q r quot).2.size < q.size := by
  induction r, quot using divModAux.induct (q := q) with
  | case1 r quot h => rw [divModAux.eq_def, if_pos h]; exact h.resolve_right hq
  | case2 r quot h ih => rw [divModAux.eq_def, if_neg h]; exact ih

/-- The remainder of polynomial division has strictly smaller size than a nonzero divisor. -/
theorem mod_size_lt {q : DensePoly R} (hq : q.size ≠ 0) (p : DensePoly R) :
    (mod p q).size < q.size :=
  divModAux_rem_size_lt hq p 0

/-- `mod p q = p - (p / q) * q`, the remainder as an explicit difference. -/
theorem mod_eq_sub (p q : DensePoly R) : mod p q = p - div p q * q :=
  eq_sub_of_add_eq' (divMod_spec p q)

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

/-! ### The Euclidean-domain instance and Mathlib's generic gcd -/

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
