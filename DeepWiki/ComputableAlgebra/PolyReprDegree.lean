import DeepWiki.ComputableAlgebra.PolyReprDenote

/-! # Representation-generic exact-degree layer for `CPolyRepr` (Step 2)

`degBound` is only an *upper* bound. The exact-degree ops — `cisZero`, `cdeg` (honest degree), `clead`
(leading coefficient), `cnorm` (trailing-zero-free canonical form) — are defined on the interface from
the coefficient support (indices `< degBound` with a `CCommRing.isZero`-nonzero coefficient), and their
correctness is stated through the `toPoly` denotation. Representation-generic; needs the `CRingSpec`
`isZero_iff` law. See `docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.CPolyRepr

variable {P : Type u → Type u} [CPolyRepr P] {α : Type u} [CCommRing α]

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

end Spec

/-! ### `native_decide` showcase -/

/-- `cisZero` reduces: `[0, 0]` normalizes to zero. -/
example : cisZero ([0, 0] : List ℚ) = true := by native_decide
/-- `cdeg` reduces: honest degree of `[1, 2, 0]` is `1` (trailing zero stripped). -/
example : cdeg ([1, 2, 0] : List ℚ) = 1 := by native_decide
/-- `clead` reduces: leading coefficient of `[1, 2, 0]` is `2`. -/
example : clead ([1, 2, 0] : List ℚ) = 2 := by native_decide
/-- `cnorm` reduces: `[1, 2, 0, 0]` normalizes to `[1, 2]`. -/
example : cnorm ([1, 2, 0, 0] : List ℚ) = [1, 2] := by native_decide

end DeepWiki.SymbolicIntegration.CPolyRepr
