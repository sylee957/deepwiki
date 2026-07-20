import DeepWiki.CAlgebra.Poly.DivisionPseudo
import DeepWiki.CAlgebra.Poly.Gcd

/-! # Polynomial gcd via the subresultant pseudo-remainder sequence

`gcdSubresultant p q` iterates pseudo-division, dividing each pseudo-remainder by the subresultant
factor `β = (−1)^(δ+1) · g · h^δ` (`g` the previous divisor's leading coefficient, `h` the running
subresultant `h`-value, `δ` the degree drop). Over a field every `β` is a nonzero constant — a unit
`C β` of `DensePoly R` — so the sequence satisfies the same gcd universal property as the Euclidean
`gcd`, and the two algorithms **agree up to a unit**: `gcdSubresultant_associated_gcd`. The Mathlib
correspondence is derived by composing that agreement with the Euclidean gcd's bridge. The
`β`-bookkeeping keeps intermediate coefficients small when the field elements are themselves big
objects (tower carriers). -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

/-- Constant-unit cancellation: `d ∣ C c * p → d ∣ p` for `c ≠ 0`. -/
theorem dvd_of_dvd_C_mul {c : R} (hc : c ≠ 0) {d p : DensePoly R} (hd : d ∣ C c * p) : d ∣ p := by
  have hp : p = C c⁻¹ * (C c * p) := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, ← one_def, one_mul]
  exact hp ▸ hd.mul_left (C c⁻¹)

/-- Subresultant-PRS accumulator: `g` is the previous divisor's leading coefficient and `h` the
running subresultant `h`-value; each pseudo-remainder is divided by `β = (−1)^(δ+1) · g · h^δ`. -/
private def gcdSubAux (r₁ r₂ : DensePoly R) (g h : R) : DensePoly R :=
  if r₂.size = 0 then r₁
  else
    gcdSubAux r₂
      (C ((-1 : R) ^ (r₁.size - r₂.size + 1) * g * h ^ (r₁.size - r₂.size))⁻¹ * pseudoMod r₁ r₂)
      r₂.leadingCoeff
      (if r₁.size - r₂.size = 0 then h
       else r₂.leadingCoeff ^ (r₁.size - r₂.size) / h ^ (r₁.size - r₂.size - 1))
  termination_by r₂.size
  decreasing_by
    rename_i hr
    exact lt_of_le_of_lt (size_C_mul_le _ _) (pseudoMod_size_lt hr r₁)

/-- Polynomial gcd by the subresultant pseudo-remainder sequence. -/
def gcdSubresultant (p q : DensePoly R) : DensePoly R := gcdSubAux p q 1 1

/-- The accumulator divides both sequence entries when `g` and `h` are nonzero (each `β` is then a
unit constant, so pseudo-division steps preserve divisors up to units). -/
private theorem gcdSubAux_dvd (r₁ r₂ : DensePoly R) (g h : R) (hg : g ≠ 0) (hh : h ≠ 0) :
    gcdSubAux r₁ r₂ g h ∣ r₁ ∧ gcdSubAux r₁ r₂ g h ∣ r₂ := by
  revert hg hh
  induction r₁, r₂, g, h using gcdSubAux.induct with
  | case1 r₁ r₂ g h hr =>
      intro _ _
      rw [gcdSubAux.eq_def, if_pos hr]
      exact ⟨dvd_refl r₁, by rw [eq_zero_of_size_zero hr]; exact dvd_zero r₁⟩
  | case2 r₁ r₂ g h hr ih =>
      intro hg hh
      have hg' : r₂.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hr
      have hh' : (if r₁.size - r₂.size = 0 then h
          else r₂.leadingCoeff ^ (r₁.size - r₂.size) / h ^ (r₁.size - r₂.size - 1)) ≠ 0 := by
        split
        · exact hh
        · exact div_ne_zero (pow_ne_zero _ hg') (pow_ne_zero _ hh)
      have hβ : ((-1 : R) ^ (r₁.size - r₂.size + 1) * g * h ^ (r₁.size - r₂.size)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hg)
          (pow_ne_zero _ hh)
      obtain ⟨ih₂, ihrem⟩ := ih hg' hh'
      rw [gcdSubAux.eq_def, if_neg hr]
      refine ⟨?_, ih₂⟩
      apply dvd_of_dvd_C_mul (pow_ne_zero (r₁.size + 1 - r₂.size) hg')
      rw [← pseudoDivMod_spec hr r₁]
      exact dvd_add (ih₂.mul_left _) (dvd_of_dvd_C_mul (inv_ne_zero hβ) ihrem)

/-- Any common divisor of the sequence entries divides the accumulator (no side conditions:
this direction never cancels a constant). -/
private theorem dvd_gcdSubAux {d : DensePoly R} (r₁ r₂ : DensePoly R) (g h : R)
    (h₁ : d ∣ r₁) (h₂ : d ∣ r₂) : d ∣ gcdSubAux r₁ r₂ g h := by
  revert h₁ h₂
  induction r₁, r₂, g, h using gcdSubAux.induct with
  | case1 r₁ r₂ g h hr =>
      intro h₁ _
      rw [gcdSubAux.eq_def, if_pos hr]
      exact h₁
  | case2 r₁ r₂ g h hr ih =>
      intro h₁ h₂
      rw [gcdSubAux.eq_def, if_neg hr]
      refine ih h₂ ?_
      have hrem : d ∣ pseudoMod r₁ r₂ := by
        rw [pseudoMod_eq_sub hr]
        exact dvd_sub (h₁.mul_left _) (h₂.mul_left _)
      exact hrem.mul_left _

/-- The subresultant-PRS gcd divides its left argument. -/
theorem gcdSubresultant_dvd_left (p q : DensePoly R) : gcdSubresultant p q ∣ p :=
  (gcdSubAux_dvd p q 1 1 one_ne_zero one_ne_zero).1

/-- The subresultant-PRS gcd divides its right argument. -/
theorem gcdSubresultant_dvd_right (p q : DensePoly R) : gcdSubresultant p q ∣ q :=
  (gcdSubAux_dvd p q 1 1 one_ne_zero one_ne_zero).2

/-- Any common divisor divides the subresultant-PRS gcd. -/
theorem dvd_gcdSubresultant {d : DensePoly R} (p q : DensePoly R) (h₁ : d ∣ p) (h₂ : d ∣ q) :
    d ∣ gcdSubresultant p q :=
  dvd_gcdSubAux p q 1 1 h₁ h₂

/-- **Agreement of the two gcd algorithms**: the subresultant-PRS gcd and the Euclidean `gcd`
divide each other — both satisfy the same universal property, so they coincide up to a unit. -/
theorem gcdSubresultant_associated_gcd (p q : DensePoly R) :
    Associated (gcdSubresultant p q) (gcd p q) :=
  associated_of_dvd_dvd
    (dvd_gcd p q (gcdSubresultant_dvd_left p q) (gcdSubresultant_dvd_right p q))
    (dvd_gcdSubresultant p q (gcd_dvd_left p q) (gcd_dvd_right p q))

end DensePoly

/-! ### Mathlib correspondence, via the agreement with the Euclidean gcd -/

open Polynomial in
variable {R : Type u} [Field R] [DecidableEq R] in
/-- The subresultant-PRS gcd is `Associated` to Mathlib's polynomial gcd — derived by carrying the
algorithm-agreement `gcdSubresultant_associated_gcd` through the ring iso and composing with the
Euclidean gcd's bridge. -/
theorem toPolynomial_gcdSubresultant_associated (p q : DensePoly R) :
    Associated (toPolynomial (DensePoly.gcdSubresultant p q))
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) :=
  ((DensePoly.gcdSubresultant_associated_gcd p q).map (equiv (R := R)).toRingHom).trans
    (toPolynomial_gcd_associated p q)

end DeepWiki.CAlgebra
