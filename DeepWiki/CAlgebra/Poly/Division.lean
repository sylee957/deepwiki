import DeepWiki.CAlgebra.Poly.Operations
import Mathlib.Algebra.Field.Basic

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
private def divModAux (q : DensePoly R) (r quot : DensePoly R) : DensePoly R × DensePoly R :=
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
private theorem divModAux_spec (q r quot : DensePoly R) :
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
private theorem divModAux_rem_size_lt {q : DensePoly R} (hq : q.size ≠ 0) (r quot : DensePoly R) :
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

/-- Division by zero yields quotient `0` (the `(0, p)` convention). -/
theorem div_zero (p : DensePoly R) : div p 0 = 0 := by
  simp only [div, divMod]
  rw [divModAux.eq_def, if_pos (Or.inr size_zero)]

end DensePoly

end DeepWiki.CAlgebra
