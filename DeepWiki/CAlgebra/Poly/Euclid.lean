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

/-- The leading (top-degree) coefficient; `0` for the zero polynomial. -/
def leadingCoeff (p : DensePoly R) : R := p.coeff (p.size - 1)

/-- A nonzero polynomial has nonzero leading coefficient. -/
theorem leadingCoeff_ne_zero {p : DensePoly R} (hp : p.size ≠ 0) : leadingCoeff p ≠ 0 :=
  coeff_last_ne_zero_of_pos_size p (Nat.pos_of_ne_zero hp)

/-- If every coefficient from index `n` upward vanishes, the size is at most `n`. -/
theorem size_le_of_coeff_zero {p : DensePoly R} {n : Nat} (h : ∀ j, n ≤ j → p.coeff j = 0) :
    p.size ≤ n := by
  by_contra hlt
  have hpos : 0 < p.size := by omega
  exact coeff_last_ne_zero_of_pos_size p hpos (h (p.size - 1) (by omega))

/-- Coefficient of `monomial k c * q`: a `k`-shifted, `c`-scaled read of `q`. -/
theorem coeff_monomial_mul (k : Nat) (c : R) (q : DensePoly R) (n : Nat) :
    (monomial k c * q).coeff n = if k ≤ n then c * q.coeff (n - k) else 0 := by
  rw [coeff_mul]
  simp only [coeff_monomial, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range (n + 1)) k (fun i => c * q.coeff (n - i))]
  simp [Finset.mem_range]

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

/-- Polynomial gcd via the Euclidean algorithm (last nonzero remainder). -/
def gcd (p q : DensePoly R) : DensePoly R :=
  if q.size = 0 then p else gcd q (mod p q)
  termination_by q.size
  decreasing_by
    rename_i h
    exact mod_size_lt h p

/-- A size-zero polynomial is the zero polynomial. -/
theorem eq_zero_of_size_zero {p : DensePoly R} (h : p.size = 0) : p = 0 := by
  ext i; rw [coeff_zero]; exact coeff_eq_zero_of_size_le p (by omega)

/-- `mod p q = p - (p / q) * q`, the remainder as an explicit difference. -/
theorem mod_eq_sub (p q : DensePoly R) : mod p q = p - div p q * q :=
  eq_sub_of_add_eq' (divMod_spec p q)

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

/-- Validation: the gcd is a genuine greatest common divisor. -/
example (p q : DensePoly R) : gcd p q ∣ p ∧ gcd p q ∣ q ∧
    ∀ d, d ∣ p → d ∣ q → d ∣ gcd p q :=
  ⟨gcd_dvd_left p q, gcd_dvd_right p q, fun _ hp hq => dvd_gcd p q hp hq⟩

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

variable {R : Type u} [Field R] [DecidableEq R] in
/-- Validation: the executable gcd and Mathlib's gcd divide each other (are associated). -/
example (p q : DensePoly R) :
    toPolynomial (DensePoly.gcd p q) ∣ EuclideanDomain.gcd (toPolynomial p) (toPolynomial q) ∧
    EuclideanDomain.gcd (toPolynomial p) (toPolynomial q) ∣ toPolynomial (DensePoly.gcd p q) :=
  ⟨(toPolynomial_gcd_associated p q).dvd, (toPolynomial_gcd_associated p q).symm.dvd⟩

end DeepWiki.CAlgebra
