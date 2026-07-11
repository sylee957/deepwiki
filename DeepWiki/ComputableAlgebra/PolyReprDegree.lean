import DeepWiki.ComputableAlgebra.PolyReprDenote

/-! # Representation-generic exact-degree layer for `CPoly` (Step 2)

`degBound` is only an *upper* bound. The exact-degree ops — `cisZero`, `cdeg` (honest degree), `clead`
(leading coefficient), `cnorm` (trailing-zero-free canonical form) — are defined on the interface from
the coefficient support (indices `< degBound` with a `CCommRing.isZero`-nonzero coefficient), and their
correctness is stated through the `toPoly` denotation. Representation-generic; needs the `CRingSpec`
`isZero_iff` law. See `docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.CPoly

variable {P : Type u → Type u} [CPoly P] {α : Type u} [CCommRing α]

/-- The coefficient support: indices `i < degBound p` whose coefficient is `isZero`-nonzero. -/
def support (p : P α) : List ℕ :=
  (List.range (degBound p)).filter (fun i => !CCommRing.isZero (coeff p i))

/-- Zero test: `true` iff no coefficient (below the bound) is nonzero. -/
def cisZero (p : P α) : Bool := (support p).isEmpty

/-- Honest degree: the largest support index (`0` for the zero polynomial). -/
def cdeg (p : P α) : ℕ := (support p).foldr max 0

/-- Leading coefficient: the coefficient at the honest degree. -/
def clead (p : P α) : α := coeff p (cdeg p)

/-- Canonical trailing-zero-free form: re-densify to exactly `cdeg + 1` coefficients (`[]` if zero). -/
def cnorm (p : P α) : P α := ofFn (if cisZero p then 0 else cdeg p + 1) (coeff p)

/-- Every list element is `≤` the `foldr max 0`. -/
theorem le_foldr_max (l : List ℕ) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a as ih =>
    intro x hx; rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih x h) (le_max_right _ _)

/-- For a nonempty `ℕ`-list, `foldr max 0` is achieved by a member. -/
theorem foldr_max_mem (l : List ℕ) (h : l ≠ []) : l.foldr max 0 ∈ l := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    rw [List.foldr_cons]
    rcases eq_or_ne as [] with rfl | hne
    · simp
    · rcases le_or_gt a (as.foldr max 0) with hle | hlt
      · rw [max_eq_right hle]; exact List.mem_cons_of_mem _ (ih hne)
      · rw [max_eq_left (le_of_lt hlt)]; exact List.mem_cons_self ..

section Spec
variable [CRingSpec α]

/-- A coefficient is `isZero` iff its denotation vanishes (unfolding `CRingSpec.isZero_iff`). -/
theorem toR_coeff_eq_zero_iff (p : P α) (i : ℕ) :
    CRingSpec.toR (coeff p i) = 0 ↔ CCommRing.isZero (coeff p i) = true :=
  (CRingSpec.isZero_iff _).symm

/-- Beyond the honest degree `cdeg`, coefficients denote to `0`. -/
theorem toR_coeff_gt_cdeg (p : P α) (k : ℕ) (h : cdeg p < k) : CRingSpec.toR (coeff p k) = 0 := by
  by_cases hk : k < degBound p
  · have hns : k ∉ support p := fun hm => absurd (le_foldr_max (support p) k hm) (Nat.not_le.mpr h)
    rw [support, List.mem_filter] at hns
    push Not at hns
    have : CCommRing.isZero (coeff p k) = true := by
      have := hns (List.mem_range.mpr hk); simpa using this
    exact (CRingSpec.isZero_iff _).mp this
  · rw [coeff_ge p k (by omega), CRingSpec.toR_zero]

/-- **`cisZero` correctness:** `cisZero p = true ↔ toPoly p = 0`. -/
theorem cisZero_iff (p : P α) : cisZero p = true ↔ toPoly p = 0 := by
  rw [cisZero, List.isEmpty_iff, support, List.filter_eq_nil_iff]
  constructor
  · intro h
    apply Polynomial.ext; intro k
    rw [coeff_toPoly, Polynomial.coeff_zero]
    rcases lt_or_ge k (degBound p) with hk | hk
    · have hik : CCommRing.isZero (coeff p k) = true := by
        have := h k (List.mem_range.mpr hk); simpa using this
      exact (CRingSpec.isZero_iff _).mp hik
    · rw [coeff_ge p k hk, CRingSpec.toR_zero]
  · intro h i _
    have hz : CRingSpec.toR (coeff p i) = 0 := by rw [← coeff_toPoly, h, Polynomial.coeff_zero]
    simp only [Bool.not_eq_true', Bool.not_eq_false]
    exact (toR_coeff_eq_zero_iff p i).mp hz

/-- **`cnorm` preserves the denotation:** `toPoly (cnorm p) = toPoly p` (stripping trailing zeros
does not change the polynomial). Representation-generic. -/
theorem toPoly_cnorm (p : P α) : toPoly (cnorm p) = toPoly p := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, coeff_toPoly, cnorm, coeff_ofFn]
  by_cases hz : cisZero p
  · rw [if_pos hz]
    simp only [Nat.not_lt_zero, if_false, CRingSpec.toR_zero]
    rw [← coeff_toPoly, (cisZero_iff p).mp hz, Polynomial.coeff_zero]
  · rw [if_neg hz]
    split
    · rfl
    · rename_i h; simp only [not_lt] at h
      rw [CRingSpec.toR_zero]; exact (toR_coeff_gt_cdeg p k (by omega)).symm

/-- **`cdeg` is the honest `natDegree`:** `cdeg p = (toPoly p).natDegree`. Representation-generic. -/
theorem cdeg_eq_natDegree (p : P α) : cdeg p = (toPoly p).natDegree := by
  refine le_antisymm ?_ ?_
  · by_cases hz : cisZero p
    · simp only [cisZero, List.isEmpty_iff] at hz; simp [cdeg, hz]
    · have hne : support p ≠ [] := by simpa [cisZero, List.isEmpty_iff] using hz
      have hmem : cdeg p ∈ support p := foldr_max_mem (support p) hne
      rw [support, List.mem_filter] at hmem
      have hpred : (!CCommRing.isZero (coeff p (cdeg p))) = true := hmem.2
      apply Polynomial.le_natDegree_of_ne_zero
      rw [coeff_toPoly]
      intro hc
      rw [(CRingSpec.isZero_iff _).mpr hc] at hpred
      simp at hpred
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm; rw [coeff_toPoly]; exact toR_coeff_gt_cdeg p m hm

/-- A nonzero represented polynomial's honest degree is strictly below its representation bound. -/
theorem cdeg_lt_degBound_of_toPoly_ne_zero (p : P α) (hp : toPoly p ≠ 0) :
    cdeg p < degBound p := by
  have hsupport : support p ≠ [] := by
    intro hnil
    apply hp
    rw [← cisZero_iff]
    simp [cisZero, hnil]
  have hmem : cdeg p ∈ support p := by
    simpa only [cdeg] using foldr_max_mem (support p) hsupport
  rw [support, List.mem_filter] at hmem
  exact List.mem_range.mp hmem.1

/-- **`clead` denotes the `leadingCoeff`:** `toR (clead p) = (toPoly p).leadingCoeff`. -/
theorem toR_clead_eq_leadingCoeff (p : P α) :
    CRingSpec.toR (clead p) = (toPoly p).leadingCoeff := by
  rw [clead, Polynomial.leadingCoeff, ← cdeg_eq_natDegree, coeff_toPoly]

end Spec

end DeepWiki.SymbolicIntegration.CPoly
