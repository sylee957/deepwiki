import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Real (formally real) fields
Examples and non-examples of formally real fields (`IsFormallyReal`, `−1` not a sum of squares):
`ℝ`, `ℚ`, and `ℚ(r)` for real `r` are real; `ℚ(√−2)` and positive-characteristic fields are not.
The workhorse is the pullback `isFormallyReal_of_injective` along an injective ring hom. -/

namespace DeepWiki.SymbolicIntegration

variable {K L : Type*}

/-- An injective ring hom preserves sums of nonzero squares: `IsSumNonzeroSq x → IsSumNonzeroSq (f x)`. -/
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

/-- Formal reality pulls back along an injective ring hom `f : K →+* L`. -/
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

/-- For `n ≠ 0` and `p : ℕ`, some `r : ℝ` satisfies `r ^ n = p`. -/
theorem exists_real_nthRoot {n : ℕ} (hn : n ≠ 0) (p : ℕ) :
    ∃ r : ℝ, r ^ n = (p : ℝ) :=
  ⟨(p : ℝ) ^ ((n : ℝ)⁻¹), Real.rpow_inv_natCast_pow (by positivity) hn⟩

/-- `ℚ(r) ⊆ ℝ` for any real `r` is formally real. -/
theorem isFormallyReal_qadjoin_real (r : ℝ) :
    IsFormallyReal (IntermediateField.adjoin ℚ ({r} : Set ℝ)) := by
  refine isFormallyReal_of_injective (algebraMap _ ℝ) ?_
  exact RingHom.injective _

/-- A characteristic-`0` ring with `j² = −2` is not formally real. -/
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

/-- In a nontrivial semiring, `IsSumNonzeroSq (n : K)` for `n ≥ 1`. -/
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

/-- A positive-characteristic ring (`CharP K p`, `p > 1`) is never formally real. -/
theorem not_isFormallyReal_of_charP [NonAssocSemiring K] [Nontrivial K]
    (p : ℕ) (hp : 1 < p) [CharP K p] : ¬ IsFormallyReal K := by
  intro h
  have h0 : IsSumNonzeroSq (0 : K) := by
    have hz : ((p : K)) = 0 := CharP.cast_eq_zero K p
    rw [← hz]
    exact isSumNonzeroSq_natCast (by omega)
  exact IsFormallyReal.not_isSumNonzeroSq_zero h0

end DeepWiki.SymbolicIntegration
