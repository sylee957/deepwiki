import DeepWiki.CAlgebra.PolyBridge.Ring
import Mathlib.Algebra.Field.Basic

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

end DensePoly

end DeepWiki.CAlgebra
