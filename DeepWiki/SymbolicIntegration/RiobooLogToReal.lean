import DeepWiki.SymbolicIntegration.RiobooLogToAtan

/-! # Rioboo's `LogToReal`: the conjugate-pair real-form identity
A conjugate pair `a ± i·b` with `S(a+ib, x) = A + i·B` contributes a real function via
`(a+ib)·logDeriv(A+iB) + (a−ib)·logDeriv(A−iB) = a·logDeriv(A²+B²) + b·(i·logDeriv((A+iB)/(A−iB)))`,
whose RHS is the derivative of `a·log(A²+B²) + b·LogToAtan(A, B)`. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

section LogToReal
variable {R : Type*} [Field R] [Differential R]

omit [Differential R] in
/-- With `i² = −1`, `(A+iB)·(A−iB) = A²+B²`. -/
theorem add_imag_mul_sub_imag {i A B : R} (hi : i ^ 2 = -1) :
    (A + i * B) * (A - i * B) = A ^ 2 + B ^ 2 := by
  linear_combination (-B ^ 2) * hi

/-- With `A²+B² ≠ 0`, `i² = −1`, `logDeriv(A+iB) + logDeriv(A−iB) = logDeriv(A²+B²)`. -/
theorem logDeriv_add_imag_add_logDeriv_sub_imag {i A B : R} (hi : i ^ 2 = -1)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) :
    Differential.logDeriv (A + i * B) + Differential.logDeriv (A - i * B)
      = Differential.logDeriv (A ^ 2 + B ^ 2) := by
  have hApiB : A + i * B ≠ 0 := add_imag_ne_zero hi hAB
  have hAmiB : A - i * B ≠ 0 := sub_imag_ne_zero hi hAB
  rw [← add_imag_mul_sub_imag hi,
    Differential.logDeriv_mul (A + i * B) (A - i * B) hApiB hAmiB]

/-- With `A²+B² ≠ 0`, `i² = −1`, `logDeriv(A+iB) − logDeriv(A−iB) = logDeriv((A+iB)/(A−iB))`. -/
theorem logDeriv_add_imag_sub_logDeriv_sub_imag {i A B : R} (hi : i ^ 2 = -1)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) :
    Differential.logDeriv (A + i * B) - Differential.logDeriv (A - i * B)
      = Differential.logDeriv ((A + i * B) / (A - i * B)) := by
  have hApiB : A + i * B ≠ 0 := add_imag_ne_zero hi hAB
  have hAmiB : A - i * B ≠ 0 := sub_imag_ne_zero hi hAB
  rw [Differential.logDeriv_div (A + i * B) (A - i * B) hApiB hAmiB]

/-- Conjugate-pair real-form identity: with `A²+B² ≠ 0`, `i² = −1`,
`(a+ib)·logDeriv(A+iB) + (a−ib)·logDeriv(A−iB) = a·logDeriv(A²+B²) + b·(i·logDeriv((A+iB)/(A−iB)))`. -/
theorem logToReal_conjugate_pair {i a b A B : R} (hi : i ^ 2 = -1)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) :
    (a + i * b) * Differential.logDeriv (A + i * B)
        + (a - i * b) * Differential.logDeriv (A - i * B)
      = a * Differential.logDeriv (A ^ 2 + B ^ 2)
        + b * (i * Differential.logDeriv ((A + i * B) / (A - i * B))) := by
  -- abbreviate the two conjugate logarithmic derivatives
  set X := Differential.logDeriv (A + i * B) with hX
  set Y := Differential.logDeriv (A - i * B) with hY
  -- the sum/difference laws
  have hsum : X + Y = Differential.logDeriv (A ^ 2 + B ^ 2) :=
    logDeriv_add_imag_add_logDeriv_sub_imag hi hAB
  have hdiff : X - Y = Differential.logDeriv ((A + i * B) / (A - i * B)) :=
    logDeriv_add_imag_sub_logDeriv_sub_imag hi hAB
  -- regroup LHS = a·(X+Y) + i·b·(X−Y) and substitute the sum/difference laws
  linear_combination a * hsum + b * i * hdiff

/-- Atan-substituted, `B = 1` case: `(a+ib)·logDeriv(A+i) + (a−ib)·logDeriv(A−i)
= a·logDeriv(A²+1²) + b·(2·A'/(1+A²))`. -/
theorem logToReal_conjugate_pair_atan [CharZero R] {i a b A : R} (hi : i ^ 2 = -1)
    (h1 : A + i ≠ 0) (h2 : A - i ≠ 0) :
    (a + i * b) * Differential.logDeriv (A + i * 1)
        + (a - i * b) * Differential.logDeriv (A - i * 1)
      = a * Differential.logDeriv (A ^ 2 + 1 ^ 2)
        + b * (2 * (A′ / (1 + A ^ 2))) := by
  -- A² + 1² ≠ 0 from A + i ≠ 0 (else A² = −1 = i² so (A−i)(A+i) = 0)
  have hAB : A ^ 2 + (1 : R) ^ 2 ≠ 0 := by
    intro h
    apply h2
    have hmul : (A - i) * (A + i) = A ^ 2 + 1 ^ 2 := by linear_combination (-1 : R) * hi
    rw [h, mul_eq_zero] at hmul
    rcases hmul with h' | h'
    · exact h'
    · exact absurd h' h1
  rw [logToReal_conjugate_pair hi hAB, mul_one,
    logDeriv_imagQuot_eq_arctanDeriv_of_sq hi h1 h2]

/-- Sum over conjugate pairs: `∑ₖ [(a k + i·b k)·logDeriv(A k + i·B k) + (a k − i·b k)·logDeriv(A k − i·B k)]
= ∑ₖ [a k·logDeriv((A k)²+(B k)²) + b k·(i·logDeriv((A k + i·B k)/(A k − i·B k)))]`, given `(A k)²+(B k)² ≠ 0`. -/
theorem logToReal_sum {ι : Type*} (s : Finset ι) {i : R} (hi : i ^ 2 = -1)
    (a b A B : ι → R) (hAB : ∀ k ∈ s, (A k) ^ 2 + (B k) ^ 2 ≠ 0) :
    ∑ k ∈ s, ((a k + i * b k) * Differential.logDeriv (A k + i * B k)
          + (a k - i * b k) * Differential.logDeriv (A k - i * B k))
      = ∑ k ∈ s, (a k * Differential.logDeriv ((A k) ^ 2 + (B k) ^ 2)
          + b k * (i * Differential.logDeriv ((A k + i * B k) / (A k - i * B k)))) :=
  Finset.sum_congr rfl fun k hk => logToReal_conjugate_pair hi (hAB k hk)

/-- Sum over conjugate pairs, atan-substituted `B = 1` case:
`∑ₖ [(a k + i·b k)·logDeriv(A k + i) + (a k − i·b k)·logDeriv(A k − i)]
= ∑ₖ [a k·logDeriv((A k)²+1²) + b k·(2·((A k)′/(1+(A k)²)))]`. -/
theorem logToReal_sum_atan [CharZero R] {ι : Type*} (s : Finset ι) {i : R} (hi : i ^ 2 = -1)
    (a b A : ι → R) (h1 : ∀ k ∈ s, A k + i ≠ 0) (h2 : ∀ k ∈ s, A k - i ≠ 0) :
    ∑ k ∈ s, ((a k + i * b k) * Differential.logDeriv (A k + i * 1)
          + (a k - i * b k) * Differential.logDeriv (A k - i * 1))
      = ∑ k ∈ s, (a k * Differential.logDeriv ((A k) ^ 2 + 1 ^ 2)
          + b k * (2 * ((A k)′ / (1 + (A k) ^ 2)))) :=
  Finset.sum_congr rfl fun k hk => logToReal_conjugate_pair_atan hi (h1 k hk) (h2 k hk)

end LogToReal

section LogToRealAtanRun
variable {R : Type*} [Field R] [Differential R] [CharZero R]
variable {K : Type*} [Field K] {φ : Polynomial K →+* R} {i : R}

/-- Full real output over conjugate pairs: with `A k = φ(Apoly k)`, `B k = φ(Bpoly k)` and per-pair runs
`IsLogToAtanRun φ i (Apoly k) (Bpoly k) (L k)`, the `i·logDeriv` term of each pair is replaced by
`atanDerivSum (L k)`, giving `∑ₖ [a k·logDeriv((φ(Apoly k))²+(φ(Bpoly k))²) + b k·atanDerivSum(L k)]`. -/
theorem logToReal_sum_atanRun (hi : i ^ 2 = -1) (hφneg : ∀ p : Polynomial K, φ (-p) = -φ p)
    {ι : Type*} (s : Finset ι) (a b : ι → R) (Apoly Bpoly : ι → Polynomial K) (L : ι → List R)
    (hAB : ∀ k ∈ s, (φ (Apoly k)) ^ 2 + (φ (Bpoly k)) ^ 2 ≠ 0)
    (hrun : ∀ k ∈ s, IsLogToAtanRun φ i (Apoly k) (Bpoly k) (L k)) :
    ∑ k ∈ s, ((a k + i * b k) * Differential.logDeriv (φ (Apoly k) + i * φ (Bpoly k))
          + (a k - i * b k) * Differential.logDeriv (φ (Apoly k) - i * φ (Bpoly k)))
      = ∑ k ∈ s, (a k * Differential.logDeriv ((φ (Apoly k)) ^ 2 + (φ (Bpoly k)) ^ 2)
          + b k * atanDerivSum (L k)) := by
  rw [logToReal_sum s hi a b (fun k => φ (Apoly k)) (fun k => φ (Bpoly k)) hAB]
  refine Finset.sum_congr rfl fun k hk => ?_
  -- replace the `i·logDeriv((φA+iφB)/(φA−iφB))` term with `atanDerivSum (L k)`
  rw [isLogToAtanRun_correct hi hφneg (hrun k hk), imagLog]

end LogToRealAtanRun

end DeepWiki.SymbolicIntegration
