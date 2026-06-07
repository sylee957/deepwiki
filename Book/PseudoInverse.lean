import Book.RealCurvesConv

/-! # Pseudo-inverse
The (lower) pseudo-inverse of a non-decreasing curve `f : ℝ≥0 → ℝ≥0∞`,
`f⁻¹(x) = inf {t | f t ≥ x}`. The infimum is taken in `ℝ≥0∞`, so "no
admissible `t`" yields `⊤`. Core API: value at `0`, the admissibility/Galois
bounds, monotonicity, the `sup {t | f t < x}` characterization for
non-decreasing `f`, and the first-crossing computation on `delay`. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

/-- The admissible set `{t | f t ≥ x}` of times, in `ℝ≥0∞`. -/
def pseudoInvSet (f : ℝ≥0 → ℝ≥0∞) (x : ℝ≥0∞) : Set ℝ≥0∞ :=
  ENNReal.ofNNReal '' {t : ℝ≥0 | f t ≥ x}

/-- The strict set `{t | f t < x}` of times, in `ℝ≥0∞`. -/
def pseudoInvLtSet (f : ℝ≥0 → ℝ≥0∞) (x : ℝ≥0∞) : Set ℝ≥0∞ :=
  ENNReal.ofNNReal '' {t : ℝ≥0 | f t < x}

/-- `(t : ℝ≥0∞) ∈ pseudoInvSet f x` iff `f t ≥ x`. -/
theorem mem_pseudoInvSet {f : ℝ≥0 → ℝ≥0∞} {x : ℝ≥0∞} {t : ℝ≥0} :
    (t : ℝ≥0∞) ∈ pseudoInvSet f x ↔ f t ≥ x := by
  unfold pseudoInvSet
  rw [Set.mem_image]
  constructor
  · rintro ⟨s, hs, hst⟩
    rwa [ENNReal.coe_inj.mp hst] at hs
  · intro h; exact ⟨t, h, rfl⟩

/-- `(t : ℝ≥0∞) ∈ pseudoInvLtSet f x` iff `f t < x`. -/
theorem mem_pseudoInvLtSet {f : ℝ≥0 → ℝ≥0∞} {x : ℝ≥0∞} {t : ℝ≥0} :
    (t : ℝ≥0∞) ∈ pseudoInvLtSet f x ↔ f t < x := by
  unfold pseudoInvLtSet
  rw [Set.mem_image]
  constructor
  · rintro ⟨s, hs, hst⟩
    rwa [ENNReal.coe_inj.mp hst] at hs
  · intro h; exact ⟨t, h, rfl⟩

/-- Lower pseudo-inverse `f⁻¹(x) = inf {t | f t ≥ x}` (in `ℝ≥0∞`). -/
noncomputable def pseudoInv (f : ℝ≥0 → ℝ≥0∞) : ℝ≥0∞ → ℝ≥0∞ :=
  fun x => sInf (pseudoInvSet f x)

/-- Admissibility: if `x ≤ f t` then `f⁻¹ x ≤ t`. -/
theorem pseudoInv_le_of_le {f : ℝ≥0 → ℝ≥0∞} {x : ℝ≥0∞} {t : ℝ≥0}
    (h : x ≤ f t) : pseudoInv f x ≤ t :=
  sInf_le (mem_pseudoInvSet.mpr h)

/-- `d ≤ f⁻¹ x` when no time `≤ d` is admissible (`d` lower-bounds the set). -/
theorem le_pseudoInv {f : ℝ≥0 → ℝ≥0∞} {x : ℝ≥0∞} {d : ℝ≥0∞}
    (h : ∀ t : ℝ≥0, x ≤ f t → d ≤ t) : d ≤ pseudoInv f x := by
  refine le_sInf ?_
  rintro z ⟨t, ht, rfl⟩
  exact_mod_cast h t ht

/-- The pseudo-inverse is monotone in `x` (antitone admissible sets). -/
theorem pseudoInv_mono (f : ℝ≥0 → ℝ≥0∞) : Monotone (pseudoInv f) := by
  intro x y hxy
  refine sInf_le_sInf ?_
  rintro z ⟨t, ht, rfl⟩
  exact ⟨t, le_trans hxy ht, rfl⟩

/-- `f⁻¹ 0 = 0` (`0` is admissible for every `t`, in particular `t = 0`). -/
theorem pseudoInv_zero (f : ℝ≥0 → ℝ≥0∞) : pseudoInv f 0 = 0 :=
  le_antisymm (pseudoInv_le_of_le (t := 0) bot_le) bot_le

/-! ## The `sup`-of-`<` characterization

For a non-decreasing `f`, `f⁻¹(x) = inf {t | f t ≥ x} = sup {t | f t < x}`.
The two index sets `I_{≥x}` and `I_{<x}` partition `ℝ≥0`; monotonicity makes
`I_{≥x}` up-closed and `I_{<x}` down-closed, so their inf and sup coincide. -/

/-- Every strict time lies below every admissible time (for monotone `f`):
`f a < x ≤ f b ⇒ a ≤ b`. -/
theorem pseudoInvLtSet_le_pseudoInvSet {f : ℝ≥0 → ℝ≥0∞}
    (hf : Monotone f) (x : ℝ≥0∞)
    {a b : ℝ≥0∞} (ha : a ∈ pseudoInvLtSet f x)
    (hb : b ∈ pseudoInvSet f x) : a ≤ b := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  rw [ENNReal.coe_le_coe]
  by_contra hlt
  rw [not_le] at hlt
  exact absurd (lt_of_lt_of_le hs ht) (not_lt.mpr (hf hlt.le))

/-- `sup {t | f t < x} ≤ f⁻¹ x` for monotone `f` (easy partition direction). -/
theorem sSup_pseudoInvLtSet_le (f : ℝ≥0 → ℝ≥0∞) (hf : Monotone f)
    (x : ℝ≥0∞) :
    sSup (pseudoInvLtSet f x) ≤ pseudoInv f x := by
  refine sSup_le (fun a ha => ?_)
  refine le_sInf (fun b hb => ?_)
  exact pseudoInvLtSet_le_pseudoInvSet hf x ha hb

/-- `f⁻¹(x) = sup {t | f t < x}` for non-decreasing `f`. -/
theorem pseudoInv_eq_sSup_lt (f : ℝ≥0 → ℝ≥0∞) (hf : Monotone f)
    (x : ℝ≥0∞) :
    pseudoInv f x = sSup (pseudoInvLtSet f x) := by
  refine le_antisymm ?_ (sSup_pseudoInvLtSet_le f hf x)
  -- `inf I_{≥} ≤ sup I_{<}`: every value below the inf is below a strict time.
  refine le_of_forall_lt fun c hc => ?_
  -- `c < inf I_{≥}`: pick a coe time `t` with `c < t < inf I_{≥}`.
  obtain ⟨t, hct, htlt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hc
  -- `t < inf I_{≥}` forces `t ∉ I_{≥}`, so by the partition `f t < x`.
  have hnotmem : (t : ℝ≥0∞) ∉ pseudoInvSet f x := fun hmem =>
    absurd (sInf_le hmem) (not_le.mpr htlt)
  have hflt : f t < x := by
    by_contra hge
    exact hnotmem (mem_pseudoInvSet.mpr (not_lt.mp hge))
  -- so `t ∈ I_{<}`, hence `c < t ≤ sup I_{<}`.
  exact lt_of_lt_of_le hct
    (le_sSup (mem_pseudoInvLtSet.mpr hflt))

/-! ## First-crossing on `delay`

For a flat-then-jump curve, `f⁻¹(x) = inf {t | f t ≥ x}` is the first time the
level `x` is reached. The `delay d` curve is `0` on `[0, d]` then jumps to `⊤`,
so every positive level is first reached just past `d`: `(delay d)⁻¹ x = d`
for `x > 0`, while `(delay d)⁻¹ 0 = 0`. -/

/-- For `0 < x`, `x ≤ delay d t` holds exactly when `d < t`. -/
theorem le_delay_iff {d : ℝ≥0} {x : ℝ≥0∞} (hx : 0 < x) (t : ℝ≥0) :
    x ≤ delay d t ↔ d < t := by
  unfold delay
  rcases le_or_gt t d with ht | ht
  · simp only [if_pos ht]
    exact ⟨fun h => absurd (le_antisymm (h.trans bot_le) bot_le)
      hx.ne', fun h => absurd ht (not_le.mpr h)⟩
  · simp only [if_neg (not_le.mpr ht)]
    exact ⟨fun _ => ht, fun _ => le_top⟩

/-- First-crossing: `(delay d)⁻¹ x = d` for `0 < x` (the level is first
reached just past `d`). -/
theorem pseudoInv_delay_pos (d : ℝ≥0) {x : ℝ≥0∞} (hx : 0 < x) :
    pseudoInv (delay d) x = d := by
  apply le_antisymm
  · -- `d` is approached from above: every `d < t` is admissible.
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hε _
    have hadm : x ≤ delay d (d + ε) :=
      (le_delay_iff hx (d + ε)).mpr (by
        simpa using (lt_add_iff_pos_right (d : ℝ≥0)).mpr hε)
    refine le_trans (pseudoInv_le_of_le hadm) ?_
    rw [ENNReal.coe_add]
  · -- `d` lower-bounds the admissible set (`d < t ⇒ d ≤ t`).
    exact le_pseudoInv (fun t ht =>
      le_of_lt (by exact_mod_cast (le_delay_iff hx t).mp ht))

/-- `(delay d)⁻¹ 0 = 0`. -/
theorem pseudoInv_delay_zero (d : ℝ≥0) : pseudoInv (delay d) 0 = 0 :=
  pseudoInv_zero (delay d)

end DeepWiki
