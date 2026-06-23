import DeepWiki.SymbolicIntegration.RiobooLogToAtan

/-! # Rioboo's `LogToReal`: the conjugate-pair real-form identity (Bronstein §2.8, p.69)
`LogToReal(R, S)` turns a complex-log sum `∑_{α|R(α)=0} α·log(S(α, x))` into a real function by
pairing conjugate roots `α = a ± i·b` (`a, b ∈ K`, `b > 0`). Writing `S(a+ib, x) = A + i·B` with
real-form `A, B`, the contribution of a conjugate pair is real because of the **key algebraic
identity** (pure `logDeriv` algebra, `i² = −1`):

`(a+ib)·logDeriv(A+iB) + (a−ib)·logDeriv(A−iB) = a·logDeriv(A²+B²) + b·(i·logDeriv((A+iB)/(A−iB)))`,

whose RHS is the derivative of the real function `a·log(A²+B²) + b·LogToAtan(A, B)`. The two
ingredients are the sum/difference `logDeriv` laws
`logDeriv(A+iB) ± logDeriv(A−iB) = logDeriv(A²+B²) / logDeriv((A+iB)/(A−iB))` (using
`(A+iB)(A−iB) = A²+B²`). Composing with **Theorem 2.8.1** (`RiobooLogToAtan`) replaces the
`i·logDeriv((A+iB)/(A−iB))` term with the real arctan-derivative `2·P'/(1+P²)`, exhibiting the
fully-real `log(A²+B²) + arctan` shape of `LogToReal`'s output.

The full multivariate `LogToReal` recursion (the `R(u+iv) = P+iQ`, `S(u+iv,x) = A+iB` split, the
`b > 0` root selection, and the recursion over `R`'s roots) needs multivariate root machinery and
is out of scope here. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

section LogToReal
variable {R : Type*} [Field R] [Differential R]

omit [Differential R] in
/-- **Conjugate-product** (§2.8, behind `LogToReal`): with `i² = −1`, `(A+iB)·(A−iB) = A²+B²` — the
identity that makes the conjugate-pair sum real. -/
theorem add_imag_mul_sub_imag {i A B : R} (hi : i ^ 2 = -1) :
    (A + i * B) * (A - i * B) = A ^ 2 + B ^ 2 := by
  linear_combination (-B ^ 2) * hi

/-- **Sum of conjugate logarithmic derivatives** (§2.8, behind `LogToReal`): with `A²+B² ≠ 0` and
`i² = −1`, `logDeriv(A+iB) + logDeriv(A−iB) = logDeriv(A²+B²)` — because `logDeriv` is additive over
the product `(A+iB)(A−iB) = A²+B²`. -/
theorem logDeriv_add_imag_add_logDeriv_sub_imag {i A B : R} (hi : i ^ 2 = -1)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) :
    Differential.logDeriv (A + i * B) + Differential.logDeriv (A - i * B)
      = Differential.logDeriv (A ^ 2 + B ^ 2) := by
  have hApiB : A + i * B ≠ 0 := add_imag_ne_zero hi hAB
  have hAmiB : A - i * B ≠ 0 := sub_imag_ne_zero hi hAB
  rw [← add_imag_mul_sub_imag hi,
    Differential.logDeriv_mul (A + i * B) (A - i * B) hApiB hAmiB]

/-- **Difference of conjugate logarithmic derivatives** (§2.8, behind `LogToReal`): with `A²+B² ≠ 0`
and `i² = −1`, `logDeriv(A+iB) − logDeriv(A−iB) = logDeriv((A+iB)/(A−iB))` — by `logDeriv` over the
quotient. -/
theorem logDeriv_add_imag_sub_logDeriv_sub_imag {i A B : R} (hi : i ^ 2 = -1)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) :
    Differential.logDeriv (A + i * B) - Differential.logDeriv (A - i * B)
      = Differential.logDeriv ((A + i * B) / (A - i * B)) := by
  have hApiB : A + i * B ≠ 0 := add_imag_ne_zero hi hAB
  have hAmiB : A - i * B ≠ 0 := sub_imag_ne_zero hi hAB
  rw [Differential.logDeriv_div (A + i * B) (A - i * B) hApiB hAmiB]

/-- **Conjugate-pair real-form identity** (§2.8, p.69, the mathematical heart of `LogToReal`): for
`a, b ∈ K` and the real-form `A, B` of `S(a+ib, x) = A + iB` (`A²+B² ≠ 0`, `i² = −1`),
`(a+ib)·logDeriv(A+iB) + (a−ib)·logDeriv(A−iB) = a·logDeriv(A²+B²) + b·(i·logDeriv((A+iB)/(A−iB)))`.
The conjugate pair `a±ib` contributes a **real** function `a·log(A²+B²) + b·LogToAtan(A,B)`. Proof:
group the LHS as `a·(sum) + i·b·(difference)` and apply the sum/difference `logDeriv` laws. -/
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

/-- **Conjugate-pair real-form, atan-substituted** (§2.8, p.69, the `log + arctan` shape of
`LogToReal`'s output): substituting **Theorem 2.8.1** (`logDeriv_imagQuot_eq_arctanDeriv_of_sq`) for
the `i·logDeriv((A+iB)/(A−iB))` term, the conjugate-pair contribution is the fully real
`a·logDeriv(A²+B²) + b·(2·A'/(1+A²))` — i.e. `a·log(A²+B²) + b·2·arctan(A)` — in the single-step
case where `B = 1` (`B²+0` arctan argument, `LogToAtan(A, 1) = [A]`). The general step uses
`isLogToAtanRun_correct`/`atanDerivSum` for the multi-term arctan list. -/
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

/-- Restatement of the **conjugate-pair real-form identity** against the book wording (§2.8, p.69):
writing `S(a+ib, x) = A + iB` with `A, B` the real/imaginary parts and `a, b ∈ K`, the conjugate pair
`a±ib` contributes `(a+ib)·d/dx log(A+iB) + (a−ib)·d/dx log(A−iB)
= a·d/dx log(A²+B²) + b·d/dx (i·log((A+iB)/(A−iB)))`, a **real** function's derivative — the
`a·log(A²+B²) + b·LogToAtan(A,B)` summand of `LogToReal`. -/
example {R : Type*} [Field R] [Differential R] (i a b A B : R) (hi : i ^ 2 = -1)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) :
    (a + i * b) * Differential.logDeriv (A + i * B)
        + (a - i * b) * Differential.logDeriv (A - i * B)
      = a * Differential.logDeriv (A ^ 2 + B ^ 2)
        + b * (i * Differential.logDeriv ((A + i * B) / (A - i * B))) :=
  logToReal_conjugate_pair hi hAB

/-- **`LogToReal` sum-over-conjugate-pairs real form** (§2.8, p.69, the correctness heart of the full
algorithm): for a `Finset ι` of conjugate-pair data `(a k, b k, A k, B k)` with `(A k)²+(B k)² ≠ 0`,
`∑ₖ [(a k + i·b k)·logDeriv(A k + i·B k) + (a k − i·b k)·logDeriv(A k − i·B k)]
  = ∑ₖ [a k·logDeriv((A k)²+(B k)²) + b k·(i·logDeriv((A k + i·B k)/(A k − i·B k)))]` — fold of the
per-pair `logToReal_conjugate_pair` over the index set by `Finset.sum_congr`. The output is the real
function `∑ₖ [a k·log((A k)²+(B k)²) + b k·LogToAtan(A k, B k)]`. -/
theorem logToReal_sum {ι : Type*} (s : Finset ι) {i : R} (hi : i ^ 2 = -1)
    (a b A B : ι → R) (hAB : ∀ k ∈ s, (A k) ^ 2 + (B k) ^ 2 ≠ 0) :
    ∑ k ∈ s, ((a k + i * b k) * Differential.logDeriv (A k + i * B k)
          + (a k - i * b k) * Differential.logDeriv (A k - i * B k))
      = ∑ k ∈ s, (a k * Differential.logDeriv ((A k) ^ 2 + (B k) ^ 2)
          + b k * (i * Differential.logDeriv ((A k + i * B k) / (A k - i * B k)))) :=
  Finset.sum_congr rfl fun k hk => logToReal_conjugate_pair hi (hAB k hk)

/-- **`LogToReal` sum-over-conjugate-pairs, atan-substituted real form** (§2.8, p.69, the
`log + arctan` shape of `LogToReal`'s output): the single-`B=1` case of `logToReal_sum` with each
`i·logDeriv((A k + i)/(A k − i))` term replaced (via **Theorem 2.8.1**,
`logToReal_conjugate_pair_atan`) by the fully real `2·(A k)′/(1 + (A k)²)`:
`∑ₖ [(a k + i·b k)·logDeriv(A k + i·1) + (a k − i·b k)·logDeriv(A k − i·1)]
  = ∑ₖ [a k·logDeriv((A k)²+1²) + b k·(2·((A k)′/(1+(A k)²)))]` — a fold of
`logToReal_conjugate_pair_atan`. The full multi-term arctan list per pair uses
`isLogToAtanRun_correct`/`atanDerivSum`. -/
theorem logToReal_sum_atan [CharZero R] {ι : Type*} (s : Finset ι) {i : R} (hi : i ^ 2 = -1)
    (a b A : ι → R) (h1 : ∀ k ∈ s, A k + i ≠ 0) (h2 : ∀ k ∈ s, A k - i ≠ 0) :
    ∑ k ∈ s, ((a k + i * b k) * Differential.logDeriv (A k + i * 1)
          + (a k - i * b k) * Differential.logDeriv (A k - i * 1))
      = ∑ k ∈ s, (a k * Differential.logDeriv ((A k) ^ 2 + 1 ^ 2)
          + b k * (2 * ((A k)′ / (1 + (A k) ^ 2)))) :=
  Finset.sum_congr rfl fun k hk => logToReal_conjugate_pair_atan hi (h1 k hk) (h2 k hk)

/-- Restatement of the **`LogToReal` sum-over-conjugate-pairs real form** against the book wording
(§2.8, p.69): summing each conjugate pair's contribution over a family `(a k, b k, A k, B k)` yields a
**real** function's derivative `∑ₖ [a k·log((A k)²+(B k)²) + b k·LogToAtan(A k, B k)]` — the output of
Rioboo's `LogToReal`. -/
example {R : Type*} [Field R] [Differential R] {ι : Type*} (s : Finset ι) (i : R) (hi : i ^ 2 = -1)
    (a b A B : ι → R) (hAB : ∀ k ∈ s, (A k) ^ 2 + (B k) ^ 2 ≠ 0) :
    ∑ k ∈ s, ((a k + i * b k) * Differential.logDeriv (A k + i * B k)
          + (a k - i * b k) * Differential.logDeriv (A k - i * B k))
      = ∑ k ∈ s, (a k * Differential.logDeriv ((A k) ^ 2 + (B k) ^ 2)
          + b k * (i * Differential.logDeriv ((A k + i * B k) / (A k - i * B k)))) :=
  logToReal_sum s hi a b A B hAB

end LogToReal

end DeepWiki.SymbolicIntegration
