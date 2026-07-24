import DeepWiki.SymbolicIntegration.RiobooLogToReal

/-! # Real/imaginary splits for real rational logarithms
The polynomial split `R(u+i·v) = P + i·Q` (and its bivariate form), the conjugate-product bridge
`A²+B² = S(a+i·b)·S(a−i·b)`, and the conjugate-root selection criterion, over a ring with `i² = −1`. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

section Split
variable {S : Type*} [CommRing S] {K : Type*} [CommRing K] [Algebra K S]

/-- Real/imaginary split: for `R ∈ K[t]` with `i² = −1` there are `P, Q` with `aeval (u+i·v) R = P + i·Q`
and the conjugate `aeval (u−i·v) R = P − i·Q`. -/
theorem exists_realImag_split (i : S) (hi : i ^ 2 = -1) (u v : S) (R : K[X]) :
    ∃ P Q : S, aeval (u + i * v) R = P + i * Q ∧ aeval (u - i * v) R = P - i * Q := by
  induction R using Polynomial.induction_on with
  | C a => exact ⟨algebraMap K S a, 0, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨Pp, Qp, hp1, hp2⟩ := hp
    obtain ⟨Pq, Qq, hq1, hq2⟩ := hq
    exact ⟨Pp + Pq, Qp + Qq, by rw [map_add, hp1, hq1]; ring,
      by rw [map_add, hp2, hq2]; ring⟩
  | monomial n a ih =>
    obtain ⟨P, Q, h1, h2⟩ := ih
    refine ⟨P * u - Q * v, P * v + Q * u, ?_, ?_⟩
    · rw [pow_succ, ← mul_assoc, map_mul, h1, aeval_X]
      linear_combination (Q * v) * hi
    · rw [pow_succ, ← mul_assoc, map_mul, h2, aeval_X]
      linear_combination (Q * v) * hi

end Split

section Bivariate
variable {S : Type*} [CommRing S] {K : Type*} [CommRing K]

/-- Bivariate real/imaginary split: for `Sxt : (K[X])[X]` with `i² = −1`,
`aeval (u±i·v) Sxt = A ± i·B` for real-form `A, B`. -/
theorem exists_realImag_split_bivariate {E : Type*} [CommRing E] [Algebra (K[X]) E]
    (i : E) (hi : i ^ 2 = -1) (u v : E) (Sxt : (K[X])[X]) :
    ∃ A B : E, aeval (u + i * v) Sxt = A + i * B ∧ aeval (u - i * v) Sxt = A - i * B :=
  exists_realImag_split i hi u v Sxt

end Bivariate

section Bridge
variable {S : Type*} [CommRing S]

/-- Conjugate-product bridge: `A² + B² = sPlus·sMinus` when `sPlus = A + i·B`, `sMinus = A − i·B`,
`i² = −1`. -/
theorem sq_add_sq_eq_mul_conj (i A B sPlus sMinus : S) (hi : i ^ 2 = -1)
    (hP : sPlus = A + i * B) (hM : sMinus = A - i * B) :
    A ^ 2 + B ^ 2 = sPlus * sMinus := by
  rw [hP, hM]; linear_combination (B ^ 2) * hi

end Bridge

section RootCriterion
variable {S : Type*} [Field S] [CharZero S]

/-- In a char-`0` field with `i² = −1`, `P + i·Q = 0` and `P − i·Q = 0` force `P = 0 ∧ Q = 0`. -/
theorem eq_zero_and_eq_zero_of_add_imag_eq_zero {i P Q : S} (hi : i ^ 2 = -1)
    (h1 : P + i * Q = 0) (h2 : P - i * Q = 0) : P = 0 ∧ Q = 0 := by
  have hi0 : (i : S) ≠ 0 := by rintro rfl; simp at hi
  have hP : (2 : S) * P = 0 := by linear_combination h1 + h2
  have hiQ : (2 : S) * (i * Q) = 0 := by linear_combination h1 - h2
  refine ⟨(mul_eq_zero.mp hP).resolve_left two_ne_zero, ?_⟩
  have hiQz : i * Q = 0 := (mul_eq_zero.mp hiQ).resolve_left two_ne_zero
  exact (mul_eq_zero.mp hiQz).resolve_left hi0

/-- Conjugate-root selection criterion: with a conjugation `σ` (`σ i = −i`) fixing real `P, Q` and the
split `vPlus = P + i·Q`, `vPlus = 0 ↔ P = 0 ∧ Q = 0`. -/
theorem aeval_eq_zero_iff_realImag_eq_zero {i P Q vPlus : S} (hi : i ^ 2 = -1)
    (σ : S →+* S) (hσi : σ i = -i) (hσP : σ P = P) (hσQ : σ Q = Q)
    (hP : vPlus = P + i * Q) :
    vPlus = 0 ↔ P = 0 ∧ Q = 0 := by
  refine ⟨fun h => ?_, fun ⟨hP0, hQ0⟩ => by rw [hP, hP0, hQ0]; ring⟩
  have h1 : P + i * Q = 0 := hP ▸ h
  -- conjugate `P + i·Q = 0` to get the conjugate root `P − i·Q = 0`
  have h2 : P - i * Q = 0 := by
    have hc := congrArg σ h1
    rw [map_add, map_mul, hσi, hσP, hσQ, map_zero, neg_mul] at hc
    linear_combination hc
  exact eq_zero_and_eq_zero_of_add_imag_eq_zero hi h1 h2

end RootCriterion

section ConjugatePairFromSplit
variable {R : Type*} [Field R] [Differential R]

/-- Conjugate-pair real form from the split: `(a+i·b)·logDeriv sPlus + (a−i·b)·logDeriv sMinus
= a·logDeriv(A²+B²) + b·(i·logDeriv((A+i·B)/(A−i·B)))` (`sPlus = A+i·B`, `sMinus = A−i·B`, `A²+B² ≠ 0`). -/
theorem logToReal_conjugate_pair_of_split {i a b A B sPlus sMinus : R} (hi : i ^ 2 = -1)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) (hP : sPlus = A + i * B) (hM : sMinus = A - i * B) :
    (a + i * b) * Differential.logDeriv sPlus + (a - i * b) * Differential.logDeriv sMinus
      = a * Differential.logDeriv (A ^ 2 + B ^ 2)
        + b * (i * Differential.logDeriv ((A + i * B) / (A - i * B))) := by
  rw [hP, hM]
  exact logToReal_conjugate_pair hi hAB

end ConjugatePairFromSplit


end DeepWiki.SymbolicIntegration
