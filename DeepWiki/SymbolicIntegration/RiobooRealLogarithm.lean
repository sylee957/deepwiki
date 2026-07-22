import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.LogArctan
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! # Foundations for real rational logarithms
Two `√−1`-free facts behind rewriting `log((u+i)/(u−i))` as a real arctangent: if `x²+1` is
irreducible over `K` then `P² + Q² = 0 ⟹ P = Q = 0`, and the log-derivative identity
`i · logDeriv((u+i)/(u−i)) = 2·u'/(1+u²)` in a differential field. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

section PolynomialSquares
variable {K : Type*} [Field K]

/-- A root of `X² + 1` over `K` is exactly a square root of `−1`: `IsSquare (-1 : K)` iff `X²+1`
has a root. -/
theorem isSquare_neg_one_iff_exists_isRoot :
    IsSquare (-1 : K) ↔ ∃ r : K, (X ^ 2 + 1 : K[X]).IsRoot r := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
    linear_combination -hs
  · rintro ⟨r, hr⟩
    have hr' : r ^ 2 + 1 = 0 := by simpa [IsRoot, eval_add, eval_pow] using hr
    exact ⟨r, by linear_combination -hr'⟩

/-- If `X²+1` is irreducible over `K` then `−1` is not a square in `K`. -/
theorem not_isSquare_neg_one_of_irreducible (h : Irreducible (X ^ 2 + 1 : K[X])) :
    ¬ IsSquare (-1 : K) := by
  intro hsq
  obtain ⟨r, hr⟩ := isSquare_neg_one_iff_exists_isRoot.mp hsq
  have hne : (X ^ 2 + 1 : K[X]) ≠ 0 := by
    intro hz; simpa using congrArg (eval 0) hz
  have hdeg : (X ^ 2 + 1 : K[X]).natDegree = 2 := by compute_degree!
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)] at h
  rw [Multiset.eq_zero_iff_forall_notMem] at h
  exact h r (by rw [mem_roots hne]; exact hr)

/-- If `X²+1` is irreducible over `K`, then `P² + Q² = 0 ⟹ P = 0 ∧ Q = 0` for `P, Q ∈ K[X]`. -/
theorem sq_add_sq_eq_zero_of_irreducible (h : Irreducible (X ^ 2 + 1 : K[X]))
    {P Q : K[X]} (hPQ : P ^ 2 + Q ^ 2 = 0) : P = 0 ∧ Q = 0 := by
  have hnsq := not_isSquare_neg_one_of_irreducible h
  -- It suffices to rule out `Q ≠ 0`; then `P² = 0` forces `P = 0`.
  suffices hQ : Q = 0 by
    refine ⟨?_, hQ⟩
    have : P ^ 2 = 0 := by rw [hQ] at hPQ; simpa using hPQ
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  by_contra hQ
  -- From `P² = −Q²`, compare leading coefficients.
  have hsq : P ^ 2 = -Q ^ 2 := by linear_combination hPQ
  have hlc : (P.leadingCoeff) ^ 2 = -(Q.leadingCoeff) ^ 2 := by
    have := congrArg leadingCoeff hsq
    rwa [leadingCoeff_pow, leadingCoeff_neg, leadingCoeff_pow] at this
  have hQlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  -- Then `−1 = (lc P / lc Q)²` is a square in `K`.
  refine absurd ⟨P.leadingCoeff / Q.leadingCoeff, ?_⟩ hnsq
  field_simp
  linear_combination -hlc

end PolynomialSquares

section ImaginaryLogDerivative
variable {R : Type*} [Field R] [Differential R]

/-- With `i² = −1` in a char-`0` differential field, `i · logDeriv((u+i)/(u−i)) = 2·(u′/(1+u²))`. -/
theorem logDeriv_imagQuot_eq_arctanDeriv_of_sq [CharZero R] {i u : R} (hi : i ^ 2 = -1)
    (h1 : u + i ≠ 0) (h2 : u - i ≠ 0) :
    i * Differential.logDeriv ((u + i) / (u - i)) = 2 * (u′ / (1 + u ^ 2)) :=
  logDeriv_imagQuot_eq_arctanDeriv hi (deriv_eq_zero_of_sq_eq_neg_one hi) h1 h2

example {K : Type*} [Field K] (h : Irreducible (X ^ 2 + 1 : K[X])) (P Q : K[X])
    (hPQ : P ^ 2 + Q ^ 2 = 0) : P = 0 ∧ Q = 0 :=
  sq_add_sq_eq_zero_of_irreducible h hPQ

example {R : Type*} [Field R] [Differential R] [CharZero R] (i u : R) (hi : i ^ 2 = -1)
    (h1 : u + i ≠ 0) (h2 : u - i ≠ 0) :
    i * Differential.logDeriv ((u + i) / (u - i)) = 2 * (u′ / (1 + u ^ 2)) :=
  logDeriv_imagQuot_eq_arctanDeriv_of_sq hi h1 h2

end ImaginaryLogDerivative

section RealLogRecursion
variable {R : Type*} [Field R] [Differential R]

omit [Differential R] in
/-- If `a² + b² ≠ 0` and `i² = −1`, then `a − i·b ≠ 0`. -/
theorem sub_imag_ne_zero {i a b : R} (hi : i ^ 2 = -1) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    a - i * b ≠ 0 := by
  intro h
  apply hab
  have hmul : (a - i * b) * (a + i * b) = a ^ 2 + b ^ 2 := by linear_combination (- b ^ 2) * hi
  rw [h, zero_mul] at hmul
  exact hmul.symm

omit [Differential R] in
/-- If `a² + b² ≠ 0` and `i² = −1`, then `a + i·b ≠ 0`. -/
theorem add_imag_ne_zero {i a b : R} (hi : i ^ 2 = -1) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    a + i * b ≠ 0 := by
  intro h
  apply hab
  have hmul : (a + i * b) * (a - i * b) = a ^ 2 + b ^ 2 := by linear_combination (- b ^ 2) * hi
  rw [h, zero_mul] at hmul
  exact hmul.symm

omit [Differential R] in
/-- With `G = B·D − A·C ≠ 0` and `P = (A·D + B·C)/G`, `P² + 1 ≠ 0` whenever `A²+B² ≠ 0` and
`C²+D² ≠ 0`. -/
theorem sq_add_one_ne_zero_of_quot {A B C D G : R} (hG : B * D - A * C = G) (hG0 : G ≠ 0)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) (hCD : C ^ 2 + D ^ 2 ≠ 0) :
    ((A * D + B * C) / G) ^ 2 + 1 ≠ 0 := by
  have hPG : ((A * D + B * C) / G) * G = A * D + B * C := div_mul_cancel₀ _ hG0
  set P := (A * D + B * C) / G with hP
  intro h
  -- `(P²+1)·G² = (A²+B²)(C²+D²) ≠ 0`, but `P²+1 = 0`.
  apply mul_ne_zero hAB hCD
  have key : (P ^ 2 + 1) * G ^ 2 = (A ^ 2 + B ^ 2) * (C ^ 2 + D ^ 2) := by
    have hkey : (P * G) ^ 2 + G ^ 2 = (A ^ 2 + B ^ 2) * (C ^ 2 + D ^ 2) := by
      rw [hPG]; linear_combination (-(G + B * D - A * C)) * hG
    rw [← hkey]; ring
  rw [h, zero_mul] at key
  exact key.symm

/-- For `A, B` with `A²+B² ≠ 0` and `i² = −1`,
`logDeriv((A+iB)/(A−iB)) = logDeriv((−B+iA)/(−B−iA))`. -/
theorem logDeriv_imagQuot_eq_imagQuot_swap [CharZero R] {i A B : R} (hi : i ^ 2 = -1)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) :
    Differential.logDeriv ((A + i * B) / (A - i * B))
      = Differential.logDeriv ((-B + i * A) / (-B - i * A)) := by
  have hAmB : A - i * B ≠ 0 := sub_imag_ne_zero hi hAB
  -- `−B + i·A ≠ 0` and `−B − i·A ≠ 0`: `(-B)² + A² = A² + B² ≠ 0`.
  have hBA : (-B) ^ 2 + A ^ 2 ≠ 0 := fun h => hAB (by linear_combination h)
  have hmBmA : -B - i * A ≠ 0 := sub_imag_ne_zero hi hBA
  have hmBpA : -B + i * A ≠ 0 := add_imag_ne_zero hi hBA
  have hderivm1 : ((-1 : R))′ = 0 := by
    rw [map_neg, (Differential.deriv : Derivation ℤ R R).map_one_eq_zero, neg_zero]
  have hlogm1 : Differential.logDeriv (-1 : R) = 0 :=
    (Differential.logDeriv_eq_zero (-1 : R)).mpr hderivm1
  -- `(A+iB)/(A−iB) = (−1)·((−B+iA)/(−B−iA))`.
  have hquot : (A + i * B) / (A - i * B) = (-1) * ((-B + i * A) / (-B - i * A)) := by
    rw [neg_one_mul, ← neg_div, div_eq_div_iff hAmB hmBmA]
    linear_combination (-2 * A * B) * hi
  rw [hquot, Differential.logDeriv_mul (-1 : R) _ (by norm_num) (div_ne_zero hmBpA hmBmA),
    hlogm1, zero_add]

/-- Real logarithm recursion step: for `A²+B² ≠ 0`, `i² = −1`, `G := B·D − A·C ≠ 0`, `C²+D² ≠ 0`, and
`P := (A·D + B·C)/G`, `i · logDeriv((A+iB)/(A−iB)) = 2·(P′/(1+P²)) + i · logDeriv((D+iC)/(D−iC))`. -/
theorem logDeriv_imagQuot_eq_arctan_add_imagQuot [CharZero R] {i A B C D G : R} (hi : i ^ 2 = -1)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) (hCD : C ^ 2 + D ^ 2 ≠ 0)
    (hG : B * D - A * C = G) (hG0 : G ≠ 0) :
    i * Differential.logDeriv ((A + i * B) / (A - i * B))
      = 2 * (((A * D + B * C) / G)′ / (1 + ((A * D + B * C) / G) ^ 2))
        + i * Differential.logDeriv ((D + i * C) / (D - i * C)) := by
  have hAmB : A - i * B ≠ 0 := sub_imag_ne_zero hi hAB
  have hDC : D ^ 2 + C ^ 2 ≠ 0 := fun h => hCD (by linear_combination h)
  have hDmC : D - i * C ≠ 0 := sub_imag_ne_zero hi hDC
  have hDpC : D + i * C ≠ 0 := add_imag_ne_zero hi hDC
  have hP1 : ((A * D + B * C) / G) ^ 2 + 1 ≠ 0 := sq_add_one_ne_zero_of_quot hG hG0 hAB hCD
  have hPG : ((A * D + B * C) / G) * G = A * D + B * C := div_mul_cancel₀ _ hG0
  set P := (A * D + B * C) / G with hPdef
  have hPpi : P + i ≠ 0 := by
    intro h; apply hP1
    have hmul : (P + i) * (P - i) = P ^ 2 + 1 := by linear_combination (-1 : R) * hi
    rw [h, zero_mul] at hmul; exact hmul.symm
  have hPmi : P - i ≠ 0 := by
    intro h; apply hP1
    have hmul : (P - i) * (P + i) = P ^ 2 + 1 := by linear_combination (-1 : R) * hi
    rw [h, zero_mul] at hmul; exact hmul.symm
  -- The factoring `(A+iB)/(A−iB) = ((P+i)/(P−i))·((D+iC)/(D−iC))`, using `P·G = AD+BC`, `BD−AC = G`.
  have hfac : (A + i * B) / (A - i * B)
      = ((P + i) / (P - i)) * ((D + i * C) / (D - i * C)) := by
    rw [div_mul_div_comm, div_eq_div_iff hAmB (mul_ne_zero hPmi hDmC)]
    -- `(D−iC)(A+iB) = G(P+i)`, `(D+iC)(A−iB) = G(P−i)` (via `P·G = AD+BC`, `BD−AC = G`, `i²=−1`).
    have e1 : (D - i * C) * (A + i * B) = P * G + i * G := by
      rw [hPG]; linear_combination i * hG - B * C * hi
    have e2 : (D + i * C) * (A - i * B) = P * G - i * G := by
      rw [hPG]; linear_combination -i * hG - B * C * hi
    -- `(A+iB)(P−i)(D−iC) = (P−i)·G(P+i) = G(P²+1) = (P+i)·G(P−i) = (A−iB)(P+i)(D+iC)`.
    linear_combination (P - i) * e1 - (P + i) * e2
  rw [hfac,
    Differential.logDeriv_mul ((P + i) / (P - i)) ((D + i * C) / (D - i * C))
      (div_ne_zero hPpi hPmi) (div_ne_zero hDpC hDmC), mul_add]
  -- Apply the imaginary quotient identity to `P`.
  rw [logDeriv_imagQuot_eq_arctanDeriv_of_sq hi hPpi hPmi]

example {R : Type*} [Field R] [Differential R] [CharZero R] (i A B : R) (hi : i ^ 2 = -1)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) :
    Differential.logDeriv ((A + i * B) / (A - i * B))
      = Differential.logDeriv ((-B + i * A) / (-B - i * A)) :=
  logDeriv_imagQuot_eq_imagQuot_swap hi hAB

example {R : Type*} [Field R] [Differential R] [CharZero R] (i A B C D G : R) (hi : i ^ 2 = -1)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) (hCD : C ^ 2 + D ^ 2 ≠ 0) (hG : B * D - A * C = G) (hG0 : G ≠ 0) :
    i * Differential.logDeriv ((A + i * B) / (A - i * B))
      = 2 * (((A * D + B * C) / G)′ / (1 + ((A * D + B * C) / G) ^ 2))
        + i * Differential.logDeriv ((D + i * C) / (D - i * C)) :=
  logDeriv_imagQuot_eq_arctan_add_imagQuot hi hAB hCD hG hG0

end RealLogRecursion

end DeepWiki.SymbolicIntegration
