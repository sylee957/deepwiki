import DeepWiki.SymbolicIntegration.RationalIntegration
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! # Rioboo's algorithm for real rational functions — the two reachable foundations (Bronstein §2.8)
The algebraic substrate of Rioboo's `LogToReal`/`LogToAtan` recursion, which rewrites a complex
logarithm `log((u+√−1)/(u−√−1))` as a real arctangent so a real integrand keeps a real
antiderivative. Two `√−1`-free, character-free facts:

* **Property (2.16)** — if `x²+1` is irreducible over `K` (equivalently `−1` is not a square),
  then `P² + Q² = 0 ⟹ P = Q = 0` for `P, Q ∈ K[x]`: the field has no `√−1`, so the two squares
  can only cancel trivially.
* **Lemma 2.8.1** (eq 2.17), the classical complex-log → real-arctan identity, stated as the
  purely algebraic logarithmic-derivative identity `i · logDeriv((u+i)/(u−i)) = 2·u'/(1+u²)`
  in a differential field. The underlying identity is
  `DeepWiki.SymbolicIntegration.logDeriv_imagQuot_eq_arctanDeriv`; here we supply the missing
  constant-`i` ingredient `deriv_i_eq_zero` (`i² = −1 ⟹ i′ = 0`) and restate the lemma against
  its book form. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

section Property216
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

/-- **Property (2.16), the field reformulation** (§2.8, p.60): if `X²+1` is irreducible over `K`
then `−1` is not a square in `K` (it has no square root, else `X²+1` would have a root). -/
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

/-- **Property (2.16)** (§2.8, p.60): if `X²+1` is irreducible over `K`, then for `P, Q ∈ K[x]`,
`P² + Q² = 0 ⟹ P = 0 ∧ Q = 0`. Proof: if `Q ≠ 0` then comparing leading coefficients of
`P² = −Q²` gives `(lc P)² = −(lc Q)²`, so `−1 = (lc P / lc Q)²` is a square in `K` — contradicting
that `X²+1` is irreducible (whence `−1` is not a square). -/
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

end Property216

section Lemma281
variable {R : Type*} [Field R] [Differential R]

/-- **Constant `√−1`** (§2.8, p.60): in a differential field, an element `i` with `i² = −1` is a
constant, `i′ = 0`. (Differentiating `i² = −1` gives `2·i·i′ = 0`; as `i ≠ 0` and `2 ≠ 0` in a
field of characteristic `0`, `i′ = 0`.) -/
theorem deriv_i_eq_zero [CharZero R] {i : R} (hi : i ^ 2 = -1) : i′ = 0 := by
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  -- Differentiate `i² = −1`: `(i²)′ = (−1)′`, i.e. `2·i·i′ = 0`.
  have hd : (2 : R) * i ^ 1 * i′ = 0 := by
    have hlhs : (i ^ 2)′ = (2 : R) * i ^ 1 * i′ := by
      rw [deriv_pow]; norm_num
    have hrhs : ((-1 : R))′ = 0 := by
      rw [show (-1 : R) = -(1 : R) by ring, map_neg,
        (Differential.deriv : Derivation ℤ R R).map_one_eq_zero, neg_zero]
    rw [← hlhs, hi, hrhs]
  rw [pow_one] at hd
  -- Cancel the nonzero factor `2·i`.
  have h2i : (2 : R) * i ≠ 0 := mul_ne_zero (by norm_num) hi0
  exact (mul_eq_zero.mp hd).resolve_left h2i

/-- **Lemma 2.8.1** (§2.8, p.60, eq 2.17): with `√−1 = i` constant derived from `i² = −1`, the
complex logarithm rewrites as a real arctangent, `i · logDeriv((u+i)/(u−i)) = 2·u'/(1+u²)` — the
constant-`i` hypothesis of `logDeriv_imagQuot_eq_arctanDeriv` discharged by `deriv_i_eq_zero`. -/
theorem logDeriv_imagQuot_eq_arctanDeriv_of_sq [CharZero R] {i u : R} (hi : i ^ 2 = -1)
    (h1 : u + i ≠ 0) (h2 : u - i ≠ 0) :
    i * Differential.logDeriv ((u + i) / (u - i)) = 2 * (u′ / (1 + u ^ 2)) :=
  logDeriv_imagQuot_eq_arctanDeriv hi (deriv_i_eq_zero hi) h1 h2

/-- Restatement of **Property (2.16)** against the book wording (§2.8, p.60): `x²+1` irreducible
over `K` ⟹ for `P, Q ∈ K[x]`, `P² + Q² = 0 ⟹ P = 0 ∧ Q = 0`. -/
example {K : Type*} [Field K] (h : Irreducible (X ^ 2 + 1 : K[X])) (P Q : K[X])
    (hPQ : P ^ 2 + Q ^ 2 = 0) : P = 0 ∧ Q = 0 :=
  sq_add_sq_eq_zero_of_irreducible h hPQ

/-- Restatement of **Lemma 2.8.1 / eq (2.17)** against the book wording: in a differential field
of characteristic `0`, with `√−1 = i` (`i² = −1`) and `u` with `u² ≠ −1`,
`√−1 · (d/dx) log((u+√−1)/(u−√−1)) = 2·(d/dx) arctan(u)` — i.e. as logarithmic derivatives,
`i · logDeriv((u+i)/(u−i)) = 2·(u'/(1+u²))`. -/
example {R : Type*} [Field R] [Differential R] [CharZero R] (i u : R) (hi : i ^ 2 = -1)
    (h1 : u + i ≠ 0) (h2 : u - i ≠ 0) :
    i * Differential.logDeriv ((u + i) / (u - i)) = 2 * (u′ / (1 + u ^ 2)) :=
  logDeriv_imagQuot_eq_arctanDeriv_of_sq hi h1 h2

end Lemma281

end DeepWiki.SymbolicIntegration
