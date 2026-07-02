import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Real (formally real) fields
Examples and non-examples of formally real fields (`IsFormallyReal`, `−1` not a sum of squares):
`ℝ`, `ℚ`, and `ℚ(r)` for real `r` are real; `ℚ(√−2)` and positive-characteristic fields are not.
The workhorse is the pullback `isFormallyReal_of_injective` along an injective ring hom. -/

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

/-- Formal reality pulls back along an injective ring hom: if `L` is real and `f : K →+* L`
is injective, then `K` is real (a nontrivial sum of squares vanishing in `K` would map to one
in `L`). Hence a subfield of a real field is real. -/
theorem isFormallyReal_of_injective [CommRing K] [CommRing L]
    [IsFormallyReal L] (f : K →+* L) (hf : Function.Injective f) :
    IsFormallyReal K where
  not_isSumNonzeroSq_zero hx := by
    have hmap : IsSumNonzeroSq (f 0) := isSumNonzeroSq_map f hf hx
    rw [map_zero] at hmap
    exact IsFormallyReal.not_isSumNonzeroSq_zero hmap

-- `ℝ` is a real field: a linearly ordered field is formally real.
example : IsFormallyReal ℝ := inferInstance

-- `ℚ` is a real field: a linearly ordered field is formally real.
example : IsFormallyReal ℚ := inferInstance

/-- The real `n`-th root of a natural number exists: for `n ≠ 0` and any `p : ℕ`,
`r := (p : ℝ) ^ (n⁻¹ : ℝ)` satisfies `r ^ n = p`. -/
theorem exists_real_nthRoot {n : ℕ} (hn : n ≠ 0) (p : ℕ) :
    ∃ r : ℝ, r ^ n = (p : ℝ) :=
  ⟨(p : ℝ) ^ ((n : ℝ)⁻¹), Real.rpow_inv_natCast_pow (by positivity) hn⟩

/-- `ℚ(r)` for any real `r` is a real field: the intermediate field `ℚ⟮r⟯ ⊆ ℝ` embeds in `ℝ`
(its `algebraMap` is injective, being a ring hom out of a field), so formal reality pulls back.
With `r = ⁿ√p` (`exists_real_nthRoot`) this covers `ℚ(ⁿ√p)`. -/
theorem isFormallyReal_qadjoin_real (r : ℝ) :
    IsFormallyReal (IntermediateField.adjoin ℚ ({r} : Set ℝ)) := by
  refine isFormallyReal_of_injective (algebraMap _ ℝ) ?_
  exact RingHom.injective _

/-- A characteristic-`0` ring containing `j` with `j² = −2` (e.g. `ℚ(√−2)`) is not formally
real: `1² + (1² + j·j) = 1 + 1 + (−2) = 0` is a vanishing sum of squares of nonzero elements —
`−1 = 1² + (√−2)²`. -/
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

/-- A positive natCast is a sum of nonzero squares: in a nontrivial semiring, `(n : K)` for
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

/-- A positive-characteristic ring is never formally real: if `(p : K) = 0` with `p ≥ 2`, then
`0 = ∑_{i=1}^{p} 1²` is a vanishing sum of nonzero squares. Hence every real field has
characteristic `0`. -/
theorem not_isFormallyReal_of_charP [NonAssocSemiring K] [Nontrivial K]
    (p : ℕ) (hp : 1 < p) [CharP K p] : ¬ IsFormallyReal K := by
  intro h
  have h0 : IsSumNonzeroSq (0 : K) := by
    have hz : ((p : K)) = 0 := CharP.cast_eq_zero K p
    rw [← hz]
    exact isSumNonzeroSq_natCast (by omega)
  exact IsFormallyReal.not_isSumNonzeroSq_zero h0

-- `ℝ`, `ℚ`, and any `ℚ(r) ⊆ ℝ` are real fields.
example : IsFormallyReal ℝ ∧ IsFormallyReal ℚ ∧
    ∀ r : ℝ, IsFormallyReal (IntermediateField.adjoin ℚ ({r} : Set ℝ)) :=
  ⟨inferInstance, inferInstance, isFormallyReal_qadjoin_real⟩

-- `ℚ(√−2)` is not a real field (`−1 = 1² + (√−2)²`).
example [CommRing K] [CharZero K] {j : K} (hj : j ^ 2 = -2) : ¬ IsFormallyReal K :=
  not_isFormallyReal_of_sq_eq_neg_two hj

end DeepWiki.SymbolicIntegration
