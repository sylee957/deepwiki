import DeepWiki.CAlgebra.Poly.DivisionPseudo
import DeepWiki.CAlgebra.Poly.Euclid
import DeepWiki.CAlgebra.Resultant.Descent
import DeepWiki.CAlgebra.Resultant.Euclidean

/-! # The subresultant clean policy: gcd and resultant from one engine

The subresultant pseudo-remainder sequence as a `clean` policy for the descent engine
(`DeepWiki/CAlgebra/Resultant/Euclidean`): state `(g, h)` carries the previous divisor's
leading coefficient and the running subresultant `h`-value, and each pseudo-remainder is
divided by `β = (−1)^(δ+1) · g · h^δ`. Over a field every `β` is a nonzero constant — a unit
`C β` — so one policy powers both engine projections: `gcdDescent` gives `gcdSubresultant`
(the gcd universal property, agreeing up to a unit with Mathlib's Euclidean-domain gcd and
bridging to the `Polynomial` gcd under `toPolynomial`), `resultantDescent` gives
`resultantPRSSubresultant`. The `β`-bookkeeping keeps intermediate coefficients small when
the field elements are themselves big objects (tower carriers). -/

namespace DeepWiki.CAlgebra

universe u v

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

/-- **The subresultant clean policy**: divide the pseudo-remainder by
`β = (−1)^(δ+1) · g · h^δ` (`δ` the degree drop), threading the state
`(divisor leading coefficient, subresultant h-value)`. -/
def cleanSubresultant (st : R × R) (f g r : DensePoly R) : R × DensePoly R × (R × R) :=
  ((-1 : R) ^ (f.size - g.size + 1) * st.1 * st.2 ^ (f.size - g.size),
   C ((-1 : R) ^ (f.size - g.size + 1) * st.1 * st.2 ^ (f.size - g.size))⁻¹ * r,
   (g.leadingCoeff,
    if f.size - g.size = 0 then st.2
    else g.leadingCoeff ^ (f.size - g.size) / st.2 ^ (f.size - g.size - 1)))

/-- The cleaned remainder is no larger. -/
theorem cleanSubresultant_size (st : R × R) (f g r : DensePoly R) :
    (cleanSubresultant st f g r).2.1.size ≤ r.size := size_C_mul_le _ _

/-- On nonzero states, the policy's `β` is nonzero and the strip reconstructs:
`C β * cleaned = r`. -/
theorem cleanSubresultant_spec (st : R × R) (f g r : DensePoly R)
    (hI : st.1 ≠ 0 ∧ st.2 ≠ 0) :
    (cleanSubresultant st f g r).1 ≠ 0 ∧
      C (cleanSubresultant st f g r).1 * (cleanSubresultant st f g r).2.1 = r := by
  have hβ : ((-1 : R) ^ (f.size - g.size + 1) * st.1 * st.2 ^ (f.size - g.size)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hI.1)
      (pow_ne_zero _ hI.2)
  refine ⟨hβ, ?_⟩
  show C ((-1 : R) ^ (f.size - g.size + 1) * st.1 * st.2 ^ (f.size - g.size))
      * (C ((-1 : R) ^ (f.size - g.size + 1) * st.1 * st.2 ^ (f.size - g.size))⁻¹ * r) = r
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hβ, ← one_def, one_mul]

/-- Nonzero states persist across the policy's state update. -/
theorem cleanSubresultant_step (st : R × R) (f g r : DensePoly R) (hg0 : g.size ≠ 0)
    (hI : st.1 ≠ 0 ∧ st.2 ≠ 0) :
    (cleanSubresultant st f g r).2.2.1 ≠ 0 ∧ (cleanSubresultant st f g r).2.2.2 ≠ 0 := by
  refine ⟨leadingCoeff_ne_zero hg0, ?_⟩
  show (if f.size - g.size = 0 then st.2
      else g.leadingCoeff ^ (f.size - g.size) / st.2 ^ (f.size - g.size - 1)) ≠ 0
  split
  · exact hI.2
  · exact div_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero hg0)) (pow_ne_zero _ hI.2)

/-! ### The subresultant-PRS gcd -/

/-- Polynomial gcd by the subresultant pseudo-remainder sequence: the subresultant clean
policy run through the engine's gcd projection, from the entry state `(1, 1)`. -/
def gcdSubresultant (p q : DensePoly R) : DensePoly R :=
  gcdDescent cleanSubresultant cleanSubresultant_size (1, 1) p q

private theorem subresStateNZ_clean (st : R × R) (f g : DensePoly R) (_ : g.size ≠ 0)
    (hI : st.1 ≠ 0 ∧ st.2 ≠ 0) :
    (cleanSubresultant st f g (pseudoMod f g)).1 ≠ 0 ∧
      C (cleanSubresultant st f g (pseudoMod f g)).1
          * (cleanSubresultant st f g (pseudoMod f g)).2.1 = pseudoMod f g :=
  cleanSubresultant_spec st f g (pseudoMod f g) hI

private theorem subresStateNZ_step (st : R × R) (f g : DensePoly R) (hg0 : g.size ≠ 0)
    (hI : st.1 ≠ 0 ∧ st.2 ≠ 0) :
    (cleanSubresultant st f g (pseudoMod f g)).2.2.1 ≠ 0 ∧
      (cleanSubresultant st f g (pseudoMod f g)).2.2.2 ≠ 0 :=
  cleanSubresultant_step st f g (pseudoMod f g) hg0 hI

/-- The subresultant-PRS gcd divides its left argument. -/
theorem gcdSubresultant_dvd_left (p q : DensePoly R) : gcdSubresultant p q ∣ p :=
  (gcdDescent_dvd cleanSubresultant cleanSubresultant_size
    (fun st _ _ => st.1 ≠ 0 ∧ st.2 ≠ 0) subresStateNZ_clean subresStateNZ_step
    (1, 1) p q ⟨one_ne_zero, one_ne_zero⟩).1

/-- The subresultant-PRS gcd divides its right argument. -/
theorem gcdSubresultant_dvd_right (p q : DensePoly R) : gcdSubresultant p q ∣ q :=
  (gcdDescent_dvd cleanSubresultant cleanSubresultant_size
    (fun st _ _ => st.1 ≠ 0 ∧ st.2 ≠ 0) subresStateNZ_clean subresStateNZ_step
    (1, 1) p q ⟨one_ne_zero, one_ne_zero⟩).2

/-- Any common divisor divides the subresultant-PRS gcd. -/
theorem dvd_gcdSubresultant {d : DensePoly R} (p q : DensePoly R) (h₁ : d ∣ p) (h₂ : d ∣ q) :
    d ∣ gcdSubresultant p q :=
  dvd_gcdDescent cleanSubresultant cleanSubresultant_size
    (fun st _ _ => st.1 ≠ 0 ∧ st.2 ≠ 0) subresStateNZ_clean subresStateNZ_step
    (1, 1) p q ⟨one_ne_zero, one_ne_zero⟩ h₁ h₂

/-! ### The resultant projection of the same policy -/

/-- **Resultant by the true subresultant pseudo-remainder sequence** over a field — the same
clean policy as `gcdSubresultant`, run through the engine's resultant projection. -/
def resultantPRSSubresultant (f g : DensePoly R) : R :=
  resultantDescent cleanSubresultant cleanSubresultant_size (1, 1) f g
    (f.size - 1) (g.size - 1)

/-- The subresultant-PRS resultant agrees with the Sylvester-determinant resultant at the
canonical degrees — hypothesis-free over a field (every `β` is a unit; the nonzero-state
invariant discharges the strips). -/
theorem resultantPRSSubresultant_eq (f g : DensePoly R) :
    resultantPRSSubresultant f g = (toPolynomial f).resultant (toPolynomial g)
      (toPolynomial f).natDegree (toPolynomial g).natDegree := by
  rw [resultantPRSSubresultant, natDegree_toPolynomial_eq_size_sub_one,
    natDegree_toPolynomial_eq_size_sub_one]
  refine resultantDescent_eq_of_invariant cleanSubresultant cleanSubresultant_size
    (fun st _ _ => st.1 ≠ 0 ∧ st.2 ≠ 0) ?_ ?_ ?_ (1, 1) f g _ _
    ⟨one_ne_zero, one_ne_zero⟩
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one f))
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one g))
  · intro st f' g' hg2 hgf hI
    exact (cleanSubresultant_spec st f' g' (pseudoMod f' g') hI).2
  · intro st f' g' hg2 hgf hI
    exact cleanSubresultant_step st f' g' (pseudoMod f' g') (by omega) hI
  · intro st f' g' _ hI
    exact hI

/-- **Agreement with Mathlib's generic Euclidean-domain gcd**: both satisfy the same universal
property, so they coincide up to a unit. -/
theorem gcdSubresultant_associated_euclideanDomainGcd (p q : DensePoly R) :
    Associated (gcdSubresultant p q) (EuclideanDomain.gcd p q) :=
  associated_of_dvd_dvd
    (EuclideanDomain.dvd_gcd (gcdSubresultant_dvd_left p q) (gcdSubresultant_dvd_right p q))
    (dvd_gcdSubresultant p q (EuclideanDomain.gcd_dvd_left p q) (EuclideanDomain.gcd_dvd_right p q))

end DensePoly

/-! ### Mathlib correspondence, via the agreement with the Euclidean gcd -/

open Polynomial in
variable {R : Type u} [Field R] [DecidableEq R] in
/-- The subresultant-PRS gcd is `Associated` to Mathlib's polynomial gcd under `toPolynomial`
(soundness by forward transport, completeness by reverse transport). -/
theorem toPolynomial_gcdSubresultant_associated (p q : DensePoly R) :
    Associated (toPolynomial (DensePoly.gcdSubresultant p q))
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  apply associated_of_dvd_dvd
  · apply EuclideanDomain.dvd_gcd
    · exact toPolynomial_dvd (DensePoly.gcdSubresultant_dvd_left p q)
    · exact toPolynomial_dvd (DensePoly.gcdSubresultant_dvd_right p q)
  · have hgp : ofPolynomial (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) ∣ p :=
      dvd_of_toPolynomial_dvd (by rw [toPolynomial_ofPolynomial]; exact EuclideanDomain.gcd_dvd_left _ _)
    have hgq : ofPolynomial (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) ∣ q :=
      dvd_of_toPolynomial_dvd (by rw [toPolynomial_ofPolynomial]; exact EuclideanDomain.gcd_dvd_right _ _)
    have hfin := toPolynomial_dvd (DensePoly.dvd_gcdSubresultant p q hgp hgq)
    rwa [toPolynomial_ofPolynomial] at hfin

end DeepWiki.CAlgebra
