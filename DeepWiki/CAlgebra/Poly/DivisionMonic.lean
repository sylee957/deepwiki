import DeepWiki.CAlgebra.Poly.Monic

/-! # Division by a monic polynomial

Long division by a monic divisor needs no leading-coefficient division — each step subtracts
`monomial δ (leadingCoeff r) * q` directly — so it works over any nontrivial commutative
coefficient ring and saves one field division per step on expensive carriers. Over a field it
agrees with the general division **exactly** (`divModMonic_eq_divMod`, by uniqueness of Euclidean
division), not merely up to units. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

section CommRing

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- One monic-division step strictly decreases the remainder size: the leading terms cancel
because the divisor's leading coefficient is `1` — no division, no zero-divisor caveats. -/
theorem divStepMonic_size_lt {q r : DensePoly R} (hm : q.leadingCoeff = 1) (hq : q.size ≠ 0)
    (hr : q.size ≤ r.size) :
    (r - monomial (r.size - q.size) r.leadingCoeff * q).size < r.size := by
  have hrpos : 0 < r.size := by omega
  have hstep : ∀ j, r.size - 1 ≤ j →
      (r - monomial (r.size - q.size) r.leadingCoeff * q).coeff j = 0 := by
    intro j hj
    rw [coeff_sub, coeff_monomial_mul]
    rcases Nat.lt_or_ge j r.size with hjr | hjr
    · have hjeq : j = r.size - 1 := by omega
      subst hjeq
      rw [if_pos (show r.size - q.size ≤ r.size - 1 by omega),
        show r.size - 1 - (r.size - q.size) = q.size - 1 by omega]
      show r.leadingCoeff - r.leadingCoeff * q.leadingCoeff = 0
      rw [hm, mul_one, sub_self]
    · rw [coeff_eq_zero_of_size_le r hjr]
      by_cases hkj : r.size - q.size ≤ j
      · rw [if_pos hkj, coeff_eq_zero_of_size_le q (by omega), mul_zero, sub_zero]
      · rw [if_neg hkj, sub_zero]
  have hsize := size_le_of_coeff_zero hstep
  omega

/-- Monic-division accumulator: subtract `monomial δ (leadingCoeff r) * q` until the remainder
drops below the divisor — no coefficient division anywhere. -/
private def divModMonicAux [Nontrivial R] (q : DensePolyMonic R) (r quot : DensePoly R) :
    DensePoly R × DensePoly R :=
  if r.size < q.toPoly.size then (quot, r)
  else
    divModMonicAux q (r - monomial (r.size - q.toPoly.size) r.leadingCoeff * q.toPoly)
      (quot + monomial (r.size - q.toPoly.size) r.leadingCoeff)
  termination_by r.size
  decreasing_by
    rename_i h
    exact divStepMonic_size_lt q.monic
      (fun h0 => q.ne_zero (eq_zero_of_size_zero h0)) (Nat.not_lt.mp h)

/-- Long division by a monic divisor: `(quotient, remainder)`, division-free in the coefficients,
over any nontrivial commutative ring. -/
def divModMonic [Nontrivial R] (p : DensePoly R) (q : DensePolyMonic R) : DensePoly R × DensePoly R :=
  divModMonicAux q p 0

/-- Quotient of division by a monic polynomial. -/
def divMonic [Nontrivial R] (p : DensePoly R) (q : DensePolyMonic R) : DensePoly R := (divModMonic p q).1

/-- Remainder of division by a monic polynomial. -/
def modMonic [Nontrivial R] (p : DensePoly R) (q : DensePolyMonic R) : DensePoly R := (divModMonic p q).2

/-- The accumulator invariant: `Q * q + R = quot * q + r`. -/
private theorem divModMonicAux_spec [Nontrivial R] (q : DensePolyMonic R) (r quot : DensePoly R) :
    (divModMonicAux q r quot).1 * q.toPoly + (divModMonicAux q r quot).2
      = quot * q.toPoly + r := by
  induction r, quot using divModMonicAux.induct (q := q) with
  | case1 r quot h => rw [divModMonicAux.eq_def, if_pos h]
  | case2 r quot h ih => rw [divModMonicAux.eq_def, if_neg h, ih]; ring

/-- Monic division reconstructs the dividend. -/
theorem divModMonic_spec [Nontrivial R] (p : DensePoly R) (q : DensePolyMonic R) :
    (divModMonic p q).1 * q.toPoly + (divModMonic p q).2 = p := by
  rw [divModMonic, divModMonicAux_spec]; simp

/-- The accumulator's remainder ends below the divisor. -/
private theorem divModMonicAux_rem_size_lt [Nontrivial R] (q : DensePolyMonic R) (r quot : DensePoly R) :
    (divModMonicAux q r quot).2.size < q.toPoly.size := by
  induction r, quot using divModMonicAux.induct (q := q) with
  | case1 r quot h => rw [divModMonicAux.eq_def, if_pos h]; exact h
  | case2 r quot h ih => rw [divModMonicAux.eq_def, if_neg h]; exact ih

/-- The remainder of monic division has strictly smaller size than the divisor. -/
theorem modMonic_size_lt [Nontrivial R] (p : DensePoly R) (q : DensePolyMonic R) :
    (modMonic p q).size < q.toPoly.size :=
  divModMonicAux_rem_size_lt q p 0

end CommRing

/-! ### Exact agreement with the general division over a field -/

section Field

variable {R : Type u} [Field R] [DecidableEq R]

/-- Euclidean division is unique, so monic division agrees with the general division **exactly**
— the same quotient and the same remainder, not merely associates: if two decompositions
`Q·q + r` have remainders below the divisor, a differing quotient would make the left side's
size at least `q`'s (`size_mul`) while the remainder difference stays below it. -/
theorem divModMonic_eq_divMod (p : DensePoly R) (q : DensePolyMonic R) :
    divModMonic p q = divMod p q.toPoly := by
  have hqt : q.toPoly ≠ 0 := q.ne_zero
  have hqs : q.toPoly.size ≠ 0 := fun h0 => hqt (eq_zero_of_size_zero h0)
  have hA := divModMonic_spec p q
  have hC := divMod_spec p q.toPoly
  have hB : (divModMonic p q).2.size < q.toPoly.size := modMonic_size_lt p q
  have hD : (divMod p q.toPoly).2.size < q.toPoly.size := mod_size_lt hqs p
  have key : ((divModMonic p q).1 - (divMod p q.toPoly).1) * q.toPoly
      = (divMod p q.toPoly).2 - (divModMonic p q).2 := by
    rw [sub_mul, sub_eq_sub_iff_add_eq_add]
    exact (hA.trans hC.symm).trans (add_comm _ _)
  have hac : (divModMonic p q).1 = (divMod p q.toPoly).1 := by
    by_contra hne
    have hsub : (divModMonic p q).1 - (divMod p q.toPoly).1 ≠ 0 := sub_ne_zero.mpr hne
    have hsz1 : q.toPoly.size
        ≤ (((divModMonic p q).1 - (divMod p q.toPoly).1) * q.toPoly).size := by
      rw [size_mul hsub hqt]
      have hs0 : ((divModMonic p q).1 - (divMod p q.toPoly).1).size ≠ 0 :=
        fun h0 => hsub (eq_zero_of_size_zero h0)
      omega
    have hsz2 : (((divModMonic p q).1 - (divMod p q.toPoly).1) * q.toPoly).size
        < q.toPoly.size := by
      rw [key]
      have hle : ((divMod p q.toPoly).2 - (divModMonic p q).2).size ≤ q.toPoly.size - 1 := by
        apply size_le_of_coeff_zero
        intro j hj
        rw [coeff_sub, coeff_eq_zero_of_size_le ((divMod p q.toPoly).2) (by omega),
          coeff_eq_zero_of_size_le ((divModMonic p q).2) (by omega), sub_zero]
      omega
    omega
  have hbd : (divModMonic p q).2 = (divMod p q.toPoly).2 := by
    have h := hA.trans hC.symm
    rw [hac] at h
    exact add_left_cancel h
  exact Prod.ext_iff.mpr ⟨hac, hbd⟩

/-- The monic quotient is the general quotient. -/
theorem divMonic_eq_div (p : DensePoly R) (q : DensePolyMonic R) :
    divMonic p q = div p q.toPoly :=
  congrArg Prod.fst (divModMonic_eq_divMod p q)

/-- The monic remainder is the general remainder. -/
theorem modMonic_eq_mod (p : DensePoly R) (q : DensePolyMonic R) :
    modMonic p q = mod p q.toPoly :=
  congrArg Prod.snd (divModMonic_eq_divMod p q)

end Field

end DensePoly

end DeepWiki.CAlgebra
