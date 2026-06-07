import Book.RealCurvesConv

/-! # Pseudo-inverse
The (lower) pseudo-inverse of a non-decreasing `f : α → β`,
`f⁻¹(x) = inf {t | f t ≥ x}`, with the infimum taken in a `CompleteLattice`
domain `α` (so "no admissible `t`" yields `⊤`). Core API over
`[CompleteLattice α] [Preorder β]`: the admissibility/Galois bounds,
monotonicity, value at `⊥`. Over a densely-ordered complete linear `α` and
linearly-ordered `β`, the `sup {t | f t < x}` characterization. A worked
first-crossing computation on the `ℝ≥0∞`-domain `delayE` curve. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

variable {α β : Type*}

/-- The admissible set `{t | f t ≥ x}` of times. -/
def pseudoInvSet [LE α] [LE β] (f : α → β) (x : β) : Set α :=
  {t : α | f t ≥ x}

/-- The strict set `{t | f t < x}` of times. -/
def pseudoInvLtSet [LE α] [LT β] (f : α → β) (x : β) : Set α :=
  {t : α | f t < x}

/-- `t ∈ pseudoInvSet f x` iff `f t ≥ x`. -/
theorem mem_pseudoInvSet [LE α] [LE β] {f : α → β} {x : β} {t : α} :
    t ∈ pseudoInvSet f x ↔ f t ≥ x := Iff.rfl

/-- `t ∈ pseudoInvLtSet f x` iff `f t < x`. -/
theorem mem_pseudoInvLtSet [LE α] [LT β] {f : α → β} {x : β} {t : α} :
    t ∈ pseudoInvLtSet f x ↔ f t < x := Iff.rfl

/-- Lower pseudo-inverse `f⁻¹(x) = inf {t | f t ≥ x}`. -/
noncomputable def pseudoInv [CompleteLattice α] [LE β] (f : α → β) : β → α :=
  fun x => sInf (pseudoInvSet f x)

/-- Admissibility: if `x ≤ f t` then `f⁻¹ x ≤ t`. -/
theorem pseudoInv_le_of_le [CompleteLattice α] [LE β] {f : α → β} {x : β}
    {t : α} (h : x ≤ f t) : pseudoInv f x ≤ t :=
  sInf_le (mem_pseudoInvSet.mpr h)

/-- `d ≤ f⁻¹ x` when every admissible time is above `d`. -/
theorem le_pseudoInv [CompleteLattice α] [LE β] {f : α → β} {x : β} {d : α}
    (h : ∀ t : α, x ≤ f t → d ≤ t) : d ≤ pseudoInv f x :=
  le_sInf h

/-- The pseudo-inverse is monotone in `x` (antitone admissible sets). -/
theorem pseudoInv_mono [CompleteLattice α] [Preorder β] (f : α → β) :
    Monotone (pseudoInv f) := by
  intro x y hxy
  refine sInf_le_sInf (fun t ht => ?_)
  exact le_trans hxy ht

/-- `f⁻¹ ⊥ = ⊥` (`⊥` is admissible for every `t`). -/
theorem pseudoInv_bot [CompleteLattice α] [LE β] [OrderBot β] (f : α → β) :
    pseudoInv f ⊥ = ⊥ :=
  le_antisymm (pseudoInv_le_of_le (t := ⊥) bot_le) bot_le

/-! ## The `sup`-of-`<` characterization

For a non-decreasing `f`, `f⁻¹(x) = inf {t | f t ≥ x} = sup {t | f t < x}`.
The index sets `I_{≥x}` and `I_{<x}` partition `α`; monotonicity makes `I_{≥x}`
up-closed and `I_{<x}` down-closed, so on a densely-ordered complete linear
order their inf and sup coincide. -/

/-- Every strict time lies below every admissible time (for monotone `f`):
`f a < x ≤ f b ⇒ a ≤ b`. -/
theorem pseudoInvLtSet_le_pseudoInvSet [LinearOrder α] [Preorder β]
    {f : α → β} (hf : Monotone f) (x : β)
    {a b : α} (ha : a ∈ pseudoInvLtSet f x)
    (hb : b ∈ pseudoInvSet f x) : a ≤ b := by
  rw [mem_pseudoInvLtSet] at ha
  rw [mem_pseudoInvSet] at hb
  by_contra hlt
  rw [not_le] at hlt
  -- `b < a ⇒ f b ≤ f a`, contradicting `f a < x ≤ f b`.
  have hfab : f b ≤ f a := hf hlt.le
  exact absurd (lt_of_lt_of_le (lt_of_lt_of_le ha hb) hfab) (lt_irrefl _)

/-- `sup {t | f t < x} ≤ f⁻¹ x` for monotone `f` (easy partition direction). -/
theorem sSup_pseudoInvLtSet_le [CompleteLinearOrder α] [Preorder β]
    (f : α → β) (hf : Monotone f) (x : β) :
    sSup (pseudoInvLtSet f x) ≤ pseudoInv f x :=
  sSup_le (fun _ ha => le_sInf (fun _ hb =>
    pseudoInvLtSet_le_pseudoInvSet hf x ha hb))

/-- `f⁻¹(x) = sup {t | f t < x}` for non-decreasing `f` (on a densely-ordered
complete linear order). -/
theorem pseudoInv_eq_sSup_lt [CompleteLinearOrder α] [DenselyOrdered α]
    [LinearOrder β] (f : α → β) (hf : Monotone f) (x : β) :
    pseudoInv f x = sSup (pseudoInvLtSet f x) := by
  refine le_antisymm ?_ (sSup_pseudoInvLtSet_le f hf x)
  -- `inf I_{≥} ≤ sup I_{<}`: every value below the inf is below a strict time.
  refine le_of_forall_lt fun c hc => ?_
  -- density: pick a time `t` with `c < t < inf I_{≥}`.
  obtain ⟨t, hct, htlt⟩ := exists_between hc
  -- `t < inf I_{≥}` forces `t ∉ I_{≥}`, so by the partition `f t < x`.
  have hnotmem : t ∉ pseudoInvSet f x := fun hmem =>
    absurd (sInf_le hmem) (not_le.mpr htlt)
  have hflt : f t < x := by
    by_contra hge
    exact hnotmem (mem_pseudoInvSet.mpr (not_lt.mp hge))
  -- so `t ∈ I_{<}`, hence `c < t ≤ sup I_{<}`.
  exact lt_of_lt_of_le hct (le_sSup (mem_pseudoInvLtSet.mpr hflt))

/-! ## First-crossing of a delay

For the pure-delay curve `delay d` (`0` up to `d`, `⊤` beyond), `f⁻¹(x)` is the
first time the level `x` is reached. Over a densely-ordered complete linear
domain, every positive level is first reached just past `d`, so `f⁻¹ x = d`
for `x > 0`, while `f⁻¹ ⊥ = ⊥`. The `delayE`/`delayNN` curves are witnesses. -/

/-- First-crossing for the pure delay: `(delay d)⁻¹ x = d` for `0 < x`. -/
theorem pseudoInv_delay_pos [CompleteLinearOrder α] [DenselyOrdered α]
    [PartialOrder β] [Zero β] [OrderTop β]
    (d : α) {x : β} (hx : 0 < x) :
    pseudoInv (delay d) x = d := by
  apply le_antisymm
  · -- `d` is approached from above: every `d < c` is admissible.
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    exact pseudoInv_le_of_le ((le_delay_iff d hx c).mpr hc)
  · -- `d` lower-bounds the admissible set (`d < t ⇒ d ≤ t`).
    exact le_pseudoInv (fun t ht => le_of_lt ((le_delay_iff d hx t).mp ht))

/-- First-crossing: `(delayE d)⁻¹ x = d` for `0 < x`. -/
theorem pseudoInv_delayE_pos (d : ℝ≥0∞) {x : ℝ≥0∞} (hx : 0 < x) :
    pseudoInv (delayE d) x = d :=
  pseudoInv_delay_pos d hx

/-- `(delayE d)⁻¹ 0 = 0`. -/
theorem pseudoInv_delayE_zero (d : ℝ≥0∞) : pseudoInv (delayE d) 0 = 0 :=
  pseudoInv_bot (delayE d)

end DeepWiki
