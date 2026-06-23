import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Real (formally real) fields — Example 2.8.2 (Bronstein §2.8)
A field `K` is a **real field** (Definition 2.8.1) when `−1` is not a sum of squares of elements
of `K` — Mathlib's `IsFormallyReal`. This file collects the §2.8 examples: `ℝ`, `ℚ`, and any
subfield of a formally real field (e.g. `ℚ(ⁿ√p) ⊆ ℝ` for a prime `p ≥ 2`) are real, while
`ℚ(√−2)` is not (`−1 = 1² + (√−2)²`) and a positive-characteristic field is never real
(`−1 = ∑ 1²`). The workhorse is the pullback `isFormallyReal_of_injective`: formal reality
descends along any injective ring hom. -/

namespace DeepWiki.SymbolicIntegration

variable {K L : Type*}

/-- An injective ring hom maps a sum of squares of nonzero elements to one: `IsSumNonzeroSq x`
gives `IsSumNonzeroSq (f x)`, since `f` preserves `+`, `*` and (being injective) nonzeroness. -/
theorem isSumNonzeroSq_map [NonAssocSemiring K] [NonAssocSemiring L]
    (f : K →+* L) (hf : Function.Injective f) {x : K}
    (hx : IsSumNonzeroSq x) : IsSumNonzeroSq (f x) := by
  induction hx with
  | sq ha =>
    rw [map_mul]
    exact IsSumNonzeroSq.sq (fun hc => ha (hf (by rw [hc, map_zero])))
  | sq_add ha hs ih =>
    rw [map_add, map_mul]
    exact IsSumNonzeroSq.sq_add (fun hc => ha (hf (by rw [hc, map_zero]))) ih

/-- **Formal reality pulls back** along an injective ring hom: if `L` is real and `f : K →+* L`
is injective, then `K` is real. (A nontrivial sum of squares vanishing in `K` would map to one
in `L`.) Hence a subfield of a real field is real — the algebraic content of "`ℚ(ⁿ√p) ⊆ ℝ` is
real" in Example 2.8.2. -/
theorem isFormallyReal_of_injective [CommRing K] [CommRing L]
    [IsFormallyReal L] (f : K →+* L) (hf : Function.Injective f) :
    IsFormallyReal K where
  not_isSumNonzeroSq_zero hx := by
    have hmap : IsSumNonzeroSq (f 0) := isSumNonzeroSq_map f hf hx
    rw [map_zero] at hmap
    exact IsFormallyReal.not_isSumNonzeroSq_zero hmap

/-- **`ℝ` is a real field** (Example 2.8.2): a linearly ordered field is formally real. -/
example : IsFormallyReal ℝ := inferInstance

/-- **`ℚ` is a real field** (Example 2.8.2): a linearly ordered field is formally real. -/
example : IsFormallyReal ℚ := inferInstance

/-- **The real `n`-th root of a prime exists** (Example 2.8.2, the `ℚ(ⁿ√p) ⊆ ℝ` ingredient): for
`n ≠ 0` and any `p : ℕ`, `r := (p : ℝ) ^ (n⁻¹ : ℝ)` satisfies `r ^ n = p`. -/
theorem exists_real_nthRoot {n : ℕ} (hn : n ≠ 0) (p : ℕ) :
    ∃ r : ℝ, r ^ n = (p : ℝ) :=
  ⟨(p : ℝ) ^ ((n : ℝ)⁻¹), Real.rpow_inv_natCast_pow (by positivity) hn⟩

/-- **`ℚ(r)` for any real `r` is a real field** (Example 2.8.2): adjoining `r ∈ ℝ` to `ℚ` inside
`ℝ` gives an intermediate field `ℚ⟮r⟯` that embeds in `ℝ` (its `algebraMap` to `ℝ` is injective,
being a ring hom out of a field), so it is real. With `r = ⁿ√p` the real `n`-th root of a prime
(`exists_real_nthRoot`) this is the `ℚ(ⁿ√p)` of the example. -/
theorem isFormallyReal_qadjoin_real (r : ℝ) :
    IsFormallyReal (IntermediateField.adjoin ℚ ({r} : Set ℝ)) := by
  refine isFormallyReal_of_injective (algebraMap _ ℝ) ?_
  exact RingHom.injective _

/-- **`ℚ(√−2)` is NOT a real field** (Example 2.8.2): any characteristic-`0` ring containing an
element `j` with `j² = −2` fails formal reality, since `1² + (1² + j·j) = 1 + 1 + (−2) = 0` is a
sum of squares of nonzero elements vanishing — `−1 = 1² + (√−2)²`. -/
theorem not_isFormallyReal_of_sq_eq_neg_two [CommRing K] [CharZero K]
    {j : K} (hj : j ^ 2 = -2) : ¬ IsFormallyReal K := by
  intro h
  have h0 : IsSumNonzeroSq (0 : K) := by
    have e : (1 : K) * 1 + ((1 : K) * 1 + j * j) = 0 := by
      have hjj : j * j = j ^ 2 := by ring
      rw [hjj]; linear_combination hj
    rw [← e]
    refine IsSumNonzeroSq.sq_add one_ne_zero (IsSumNonzeroSq.sq_add one_ne_zero ?_)
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hj
      exact two_ne_zero (by linear_combination hj : (2 : K) = 0)
    exact IsSumNonzeroSq.sq hj0
  exact IsFormallyReal.not_isSumNonzeroSq_zero h0

/-- **A positive natCast is a sum of nonzero squares**: in a nontrivial semiring, `(n : K)` for
`n ≥ 1` is `1² + ⋯ + 1²` (`n` summands), hence `IsSumNonzeroSq (n : K)`. -/
theorem isSumNonzeroSq_natCast [NonAssocSemiring K] [Nontrivial K]
    {n : ℕ} (hn : 0 < n) : IsSumNonzeroSq ((n : K)) := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 : ((1 : ℕ) : K) = 1 * 1 := by simp
      rw [h1]; exact IsSumNonzeroSq.sq one_ne_zero
    · have hcast : ((m + 1 : ℕ) : K) = 1 * 1 + (m : K) := by
        rw [one_mul, Nat.cast_succ, add_comm]
      rw [hcast]
      exact IsSumNonzeroSq.sq_add one_ne_zero (ih hm)

/-- **A positive-characteristic field is never real** (Example 2.8.2): if `(p : K) = 0` with
`p ≥ 2` (e.g. `CharP K p`, `p` prime), then `0 = ∑_{i=1}^{p} 1²` is a vanishing sum of nonzero
squares, so `−1 = ∑_{i=1}^{p−1} 1²` is a sum of squares — `K` is not formally real. Hence every
real field has characteristic `0`. -/
theorem not_isFormallyReal_of_charP [NonAssocSemiring K] [Nontrivial K]
    (p : ℕ) (hp : 1 < p) [CharP K p] : ¬ IsFormallyReal K := by
  intro h
  have h0 : IsSumNonzeroSq (0 : K) := by
    have hz : ((p : K)) = 0 := CharP.cast_eq_zero K p
    rw [← hz]
    exact isSumNonzeroSq_natCast (by omega)
  exact IsFormallyReal.not_isSumNonzeroSq_zero h0

/-- Restatement of **Example 2.8.2** against the book wording (§2.8, p.65): `ℝ` and `ℚ` are real
fields, and `ℚ(ⁿ√p) ⊆ ℝ` (the field generated over `ℚ` by a real `n`-th root `r` of a prime,
`exists_real_nthRoot`) is real since it embeds in the real field `ℝ`. -/
example : IsFormallyReal ℝ ∧ IsFormallyReal ℚ ∧
    ∀ r : ℝ, IsFormallyReal (IntermediateField.adjoin ℚ ({r} : Set ℝ)) :=
  ⟨inferInstance, inferInstance, isFormallyReal_qadjoin_real⟩

/-- Restatement of the **non-examples / characteristic remark** of Example 2.8.2 (§2.8, p.65):
`ℚ(√−2)` is not real (`−1 = 1² + (√−2)²`), and a field of characteristic `p > 0` is not real
(`−1 = ∑_{i=1}^{p−1} 1²`). -/
example [CommRing K] [CharZero K] {j : K} (hj : j ^ 2 = -2) : ¬ IsFormallyReal K :=
  not_isFormallyReal_of_sq_eq_neg_two hj

end DeepWiki.SymbolicIntegration
