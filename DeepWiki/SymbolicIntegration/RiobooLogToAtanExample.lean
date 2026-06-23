import DeepWiki.SymbolicIntegration.RiobooLogToAtan

/-! # Worked `LogToAtan` example (Bronstein §2.8, Example 2.8.1, p.63–64)
Rioboo's `LogToAtan` applied to `A = x³−3x`, `B = x²−2` runs three branches (book table p.64) and
returns the arctan-argument list `[(x⁵−3x³+x)/2, x³, x]`, giving
`∫ (x⁴−3x²+6)/(x⁶−5x⁴+5x²+4) dx = arctan((x⁵−3x³+x)/2) + arctan(x³) + arctan(x)`
(up to a step function). We build the explicit `IsLogToAtanRun` for this input — supplying the
extended-Euclidean cofactors directly (integer-scaled so the Bézout relations `B·D − A·C = G` are pure
`ring` facts): step 1 `(C,D,G) = (x, x²−1, 2)`, step 2 `(1, x, 1)`, base `1 ∣ x` — and read off the
correctness `atanDerivSum [...] = i · logDeriv((φA+iφB)/(φA−iφB))` from `isLogToAtanRun_correct`. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

section Example281
variable {R : Type*} [Field R] [Differential R] [CharZero R]
variable {φ : ℚ[X] →+* R} {i : R}

/-- The three arctan arguments of Example 2.8.1's `LogToAtan(x³−3x, x²−2)` run (book table p.64):
`[(φx⁵−3φx³+φx)/2, (φx)³, φx]` as elements of `R`, written in the exact shape the `step`/`base`
constructors of `IsLogToAtanRun` produce (`(φA·φD+φB·φC)/φG` and `φA/φB`). -/
noncomputable def ex281_args (φ : ℚ[X] →+* R) : List R :=
  [(φ (X ^ 3 - 3 * X) * φ (X ^ 2 - 1) + φ (X ^ 2 - 2) * φ X) / φ 2,
   (φ (X ^ 2 - 1) * φ X + φ X * φ 1) / φ 1,
   φ X / φ 1]

omit [Differential R] [CharZero R] in

/-- **Example 2.8.1, the explicit `LogToAtan` run** (§2.8, p.63–64): `LogToAtan(x³−3x, x²−2)` realizes
the three-branch Rioboo recursion of the book table — step 1 with cofactors `(C,D,G) = (x, x²−1, 2)`
(`B·D − A·C = 2`), step 2 with `(1, x, 1)` (`B·D − A·C = 1`), base `1 ∣ x` — emitting the arctan
arguments `ex281_args`. Each Bézout relation is a `ring` fact (integer-scaled cofactors) and each
nonvanishing `(φP)²+(φQ)² = φ(P²+Q²) ≠ 0` follows from `φ` injective and the constant term being
nonzero. -/
theorem ex281_isLogToAtanRun (hφinj : Function.Injective φ) :
    IsLogToAtanRun φ i (X ^ 3 - 3 * X) (X ^ 2 - 2) (ex281_args φ) := by
  -- `φ` injective ⇒ `φ p ≠ 0` whenever the polynomial `p ≠ 0`.
  have hφ0 : ∀ p : ℚ[X], p ≠ 0 → φ p ≠ 0 := fun p hp h =>
    hp (hφinj (by rw [h, map_zero]))
  -- A polynomial with nonzero constant term is nonzero (`eval 0`).
  have hne : ∀ p : ℚ[X], eval 0 p ≠ 0 → p ≠ 0 := fun p hp h => hp (by rw [h, eval_zero])
  -- `(φ P)² + (φ Q)² = φ (P² + Q²)`, reduced to `φ (P²+Q²) ≠ 0` for the explicit sums.
  have hsum : ∀ P Q : ℚ[X], φ (P ^ 2 + Q ^ 2) ≠ 0 → (φ P) ^ 2 + (φ Q) ^ 2 ≠ 0 := by
    intro P Q h; rwa [map_add, map_pow, map_pow] at h
  -- Bézout relations, pushed to the polynomial level then mapped.
  have hbez1 : φ (X ^ 2 - 2) * φ (X ^ 2 - 1) - φ (X ^ 3 - 3 * X) * φ X = φ 2 := by
    rw [← map_mul, ← map_mul, ← map_sub]; congr 1; ring
  have hbez2 : φ X * φ X - φ (X ^ 2 - 1) * φ 1 = φ 1 := by
    rw [← map_mul, ← map_mul, ← map_sub]; congr 1; ring
  -- Step 1.
  refine IsLogToAtanRun.step
    (hsum _ _ (hφ0 _ (hne _ (by norm_num))))           -- (φA)²+(φB)² ≠ 0
    (hsum _ _ (hφ0 _ (hne _ (by norm_num))))           -- (φC)²+(φD)² ≠ 0  (C=X, D=X²−1)
    hbez1 (hφ0 _ (hne _ (by norm_num))) ?_             -- φ 2 ≠ 0
  -- Step 2 (on `(D₁, C₁) = (X²−1, X)`).
  refine IsLogToAtanRun.step
    (hsum _ _ (hφ0 _ (hne _ (by norm_num))))           -- (φ(X²−1))²+(φX)² ≠ 0
    (hsum _ _ (hφ0 _ (hne _ (by norm_num))))           -- (φ1)²+(φX)² ≠ 0  (C=1, D=X)
    hbez2 (hφ0 _ (hne _ (by norm_num))) ?_             -- φ 1 ≠ 0
  -- Base (on `(D₂, C₂) = (X, 1)`): `1 ∣ X`.
  exact IsLogToAtanRun.base (hφ0 _ (hne _ (by norm_num)))
    (hsum _ _ (hφ0 _ (hne _ (by norm_num)))) (one_dvd _)

/-- **Example 2.8.1, the `LogToAtan` correctness instance** (§2.8, p.63–64): the arctan-derivative sum
of the run's output equals the complex logarithm, `atanDerivSum (ex281_args φ) = i ·
logDeriv((φ(x³−3x)+i·φ(x²−2))/(φ(x³−3x)−i·φ(x²−2)))` — `isLogToAtanRun_correct` applied to
`ex281_isLogToAtanRun`. This is the differential-form of book eq (2.20):
`d/dx [arctan((x⁵−3x³+x)/2) + arctan(x³) + arctan(x)] = d/dx · i·log((A+iB)/(A−iB))`. -/
theorem ex281_logToAtan_correct (hi : i ^ 2 = -1) (hφinj : Function.Injective φ) :
    atanDerivSum (ex281_args φ)
      = i * Differential.logDeriv
          ((φ (X ^ 3 - 3 * X) + i * φ (X ^ 2 - 2)) / (φ (X ^ 3 - 3 * X) - i * φ (X ^ 2 - 2))) :=
  isLogToAtanRun_correct hi (map_neg φ) (ex281_isLogToAtanRun hφinj)

/-- Restatement of **Example 2.8.1** against the book's three-arctan answer (§2.8, eq 2.20, p.64): with
`A = x³−3x`, `B = x²−2`, the integrand `(x⁴−3x²+6)/(x⁶−5x⁴+5x²+4)` integrates to
`arctan((x⁵−3x³+x)/2) + arctan(x³) + arctan(x)` (up to a step function) — i.e. as derivatives, the
arctan-derivative sum `∑_{P∈[(x⁵−3x³+x)/2, x³, x]} 2·P'/(1+P²)` equals `i·logDeriv((A+iB)/(A−iB))`. The
three list entries are the run's emitted arguments `ex281_args` in the book table's `(AD+BC)/G` shape. -/
example (hi : i ^ 2 = -1) (hφinj : Function.Injective φ) :
    ((ex281_args φ).map fun P => 2 * (P′ / (1 + P ^ 2))).sum
      = i * Differential.logDeriv
          ((φ (X ^ 3 - 3 * X) + i * φ (X ^ 2 - 2)) / (φ (X ^ 3 - 3 * X) - i * φ (X ^ 2 - 2))) :=
  ex281_logToAtan_correct hi hφinj

end Example281

end DeepWiki.SymbolicIntegration
