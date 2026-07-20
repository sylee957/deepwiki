import DeepWiki.CAlgebra.Poly.Operations

/-! # Pseudo-division of normalized dense polynomials

Pseudo-division over any commutative coefficient ring: `pseudoDivMod p q` returns `(quotient,
remainder)` with `C (q.leadingCoeff ^ (p.size + 1 - q.size)) * p = quotient * q + remainder` and
`remainder.size < q.size` — long division with each leading-coefficient division replaced by a
premultiplication, so no `Field` is needed. The step count is the exact power `p.size + 1 - q.size`
(structural recursion); the identity is proved by transport through `toPolynomial`. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- Pseudo-division accumulator: `n` premultiplications by `b` remain; once the remainder drops
below the divisor the unused ones are applied at once, keeping the total power exact. -/
def pseudoDivModAux (q : DensePoly R) (b : R) :
    Nat → DensePoly R → DensePoly R → DensePoly R × DensePoly R
  | 0, quot, r => (quot, r)
  | n + 1, quot, r =>
    if r.size < q.size then (C (b ^ (n + 1)) * quot, C (b ^ (n + 1)) * r)
    else
      pseudoDivModAux q b n (C b * quot + monomial (r.size - q.size) r.leadingCoeff)
        (C b * r - monomial (r.size - q.size) r.leadingCoeff * q)

/-- Pseudo-division: `(quotient, remainder)` of `p` by `q` after premultiplying `p` by
`q.leadingCoeff ^ (p.size + 1 - q.size)`. Division by `0` returns `(0, p)`. -/
def pseudoDivMod (p q : DensePoly R) : DensePoly R × DensePoly R :=
  if q.size = 0 then (0, p)
  else pseudoDivModAux q q.leadingCoeff (p.size + 1 - q.size) 0 p

/-- Quotient of pseudo-division. -/
def pseudoDiv (p q : DensePoly R) : DensePoly R := (pseudoDivMod p q).1

/-- Remainder of pseudo-division. -/
def pseudoMod (p q : DensePoly R) : DensePoly R := (pseudoDivMod p q).2

/-- The accumulator invariant: the result pair reconstructs `b ^ n` times the input state. -/
theorem pseudoDivModAux_spec (q : DensePoly R) (b : R) (n : Nat) :
    ∀ quot r, (pseudoDivModAux q b n quot r).1 * q + (pseudoDivModAux q b n quot r).2
      = C (b ^ n) * (quot * q + r) := by
  induction n with
  | zero =>
      intro quot r
      apply toPolynomial_injective
      simp only [pseudoDivModAux, toPolynomial_mul, toPolynomial_add, toPolynomial_C, pow_zero,
        map_one]
      ring
  | succ n ih =>
      intro quot r
      simp only [pseudoDivModAux]
      split
      · apply toPolynomial_injective
        simp only [toPolynomial_mul, toPolynomial_add, toPolynomial_C]
        ring
      · rw [ih]
        apply toPolynomial_injective
        simp only [toPolynomial_mul, toPolynomial_add, toPolynomial_sub, toPolynomial_C,
          toPolynomial_monomial, pow_succ, map_mul]
        ring

/-- The pseudo-division identity: quotient and remainder reconstruct the premultiplied dividend. -/
theorem pseudoDivMod_spec {q : DensePoly R} (hq : q.size ≠ 0) (p : DensePoly R) :
    (pseudoDivMod p q).1 * q + (pseudoDivMod p q).2
      = C (q.leadingCoeff ^ (p.size + 1 - q.size)) * p := by
  rw [pseudoDivMod, if_neg hq, pseudoDivModAux_spec]
  apply toPolynomial_injective
  simp only [toPolynomial_mul, toPolynomial_add, toPolynomial_C, toPolynomial_zero]
  ring

/-- `pseudoMod p q` as an explicit difference (the pseudo-division identity rearranged). -/
theorem pseudoMod_eq_sub {q : DensePoly R} (hq : q.size ≠ 0) (p : DensePoly R) :
    pseudoMod p q = C (q.leadingCoeff ^ (p.size + 1 - q.size)) * p - pseudoDiv p q * q :=
  eq_sub_of_add_eq' (pseudoDivMod_spec hq p)

/-- One pseudo-division step strictly decreases the remainder size (leading-term cancellation,
using commutativity in place of a leading-coefficient division). -/
theorem pseudoStep_size_lt {q r : DensePoly R} (hq : q.size ≠ 0) (hr : q.size ≤ r.size) :
    (C q.leadingCoeff * r - monomial (r.size - q.size) r.leadingCoeff * q).size < r.size := by
  have hrpos : 0 < r.size := lt_of_lt_of_le (Nat.pos_of_ne_zero hq) hr
  have hstep : ∀ j, r.size - 1 ≤ j →
      (C q.leadingCoeff * r - monomial (r.size - q.size) r.leadingCoeff * q).coeff j = 0 := by
    intro j hj
    rw [coeff_sub, coeff_C_mul, coeff_monomial_mul]
    rcases Nat.lt_or_ge j r.size with hjr | hjr
    · have hjeq : j = r.size - 1 := by omega
      subst hjeq
      rw [if_pos (show r.size - q.size ≤ r.size - 1 by omega),
        show r.size - 1 - (r.size - q.size) = q.size - 1 by omega]
      show q.leadingCoeff * r.leadingCoeff - r.leadingCoeff * q.leadingCoeff = 0
      ring
    · rw [coeff_eq_zero_of_size_le r hjr, mul_zero]
      by_cases hkj : r.size - q.size ≤ j
      · rw [if_pos hkj, coeff_eq_zero_of_size_le q (by omega), mul_zero, sub_zero]
      · rw [if_neg hkj, sub_zero]
  have hsize := size_le_of_coeff_zero hstep
  omega

/-- The accumulator's remainder drops below the divisor once enough steps are available. -/
theorem pseudoDivModAux_rem_size_lt {q : DensePoly R} (hq : q.size ≠ 0) (n : Nat) :
    ∀ quot r, r.size < q.size + n →
      (pseudoDivModAux q q.leadingCoeff n quot r).2.size < q.size := by
  induction n with
  | zero =>
      intro quot r h
      simpa [pseudoDivModAux] using h
  | succ n ih =>
      intro quot r h
      simp only [pseudoDivModAux]
      split
      · rename_i hlt
        exact lt_of_le_of_lt (size_C_mul_le _ _) hlt
      · rename_i hge
        have hge' : q.size ≤ r.size := Nat.not_lt.mp hge
        exact ih _ _ (by have := pseudoStep_size_lt hq hge'; omega)

/-- The pseudo-remainder has strictly smaller size than a nonzero divisor. -/
theorem pseudoMod_size_lt {q : DensePoly R} (hq : q.size ≠ 0) (p : DensePoly R) :
    (pseudoMod p q).size < q.size := by
  rw [pseudoMod, pseudoDivMod, if_neg hq]
  exact pseudoDivModAux_rem_size_lt hq _ 0 p (by omega)

end DensePoly

/-! ### Mathlib correspondence -/

variable {R : Type u} [CommRing R] [DecidableEq R]

open Polynomial in
/-- The pseudo-division identity in Mathlib terms, transported through `toPolynomial` (Mathlib has
no pseudo-division of its own, so the transported identity is the bridge statement). -/
theorem toPolynomial_pseudoDivMod {q : DensePoly R} (hq : q.size ≠ 0) (p : DensePoly R) :
    toPolynomial (DensePoly.pseudoDiv p q) * toPolynomial q
        + toPolynomial (DensePoly.pseudoMod p q)
      = Polynomial.C (q.leadingCoeff ^ (p.size + 1 - q.size)) * toPolynomial p := by
  rw [DensePoly.pseudoDiv, DensePoly.pseudoMod, ← toPolynomial_C, ← toPolynomial_mul,
    ← toPolynomial_mul, ← toPolynomial_add, DensePoly.pseudoDivMod_spec hq]

end DeepWiki.CAlgebra
