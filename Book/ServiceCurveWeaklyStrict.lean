import Book.ServiceCurveStrict
import Book.ServiceCurveMinimal

/-! # Weakly strict service curves
Between the strict and min-plus service curves sits the weakly strict
type: the strict increment is required only from the start of the
backlogged period of each `t`,
`D(t) ≥ D(Start(t)) + β(t − Start(t))`. The hierarchy
`strict ⊆ weakly strict ⊆ min-plus` holds at the relation level — the
min-plus transport of the strict theory factors through this middle
layer, since it only ever uses strictness at the start. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- A weakly strict (minimal) service curve: every served pair gains
`beta` from the start of the backlogged period of each `t`,
`D(Start(t)) + β(t − Start(t)) ≤ D(t)`. -/
def IsWeaklyStrictServiceCurve (beta : ℝ≥0 → ℝ≥0)
    (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → ∀ t,
    D (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ D t

/-- The largest relation offering the weakly strict curve `beta`:
causality plus the start-anchored increment. -/
def weaklyStrictServiceRel (beta : ℝ≥0 → ℝ≥0) :
    Curve → Curve → Prop :=
  fun A D => D ≤ A ∧ ∀ t,
    D (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ D t

/-- `weaklyStrictServiceRel beta A D` unfolds to causality plus the
start-anchored bound. -/
theorem mem_weaklyStrictServiceRel_iff {beta : ℝ≥0 → ℝ≥0}
    {A D : Curve} :
    weaklyStrictServiceRel beta A D ↔
      D ≤ A ∧ ∀ t,
        D (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ D t :=
  Iff.rfl

/-- Each curve serves itself with any weakly strict curve null at the
origin: against itself the start is `t` itself (`start_self`). -/
theorem weaklyStrictServiceRel_self {beta : ℝ≥0 → ℝ≥0}
    (h0 : beta 0 = 0) (A : Curve) :
    weaklyStrictServiceRel beta A A := by
  refine ⟨fun _ => le_refl _, fun t => ?_⟩
  rw [start_self, tsub_self, h0, add_zero]

/-- When `beta 0 = 0`, `weaklyStrictServiceRel beta` is a server. -/
theorem isServer_weaklyStrictServiceRel {beta : ℝ≥0 → ℝ≥0}
    (h0 : beta 0 = 0) :
    IsServer (weaklyStrictServiceRel beta) :=
  ⟨fun _ _ hp => hp.1, fun A => ⟨A, weaklyStrictServiceRel_self h0 A⟩⟩

/-- The relation `weaklyStrictServiceRel beta` offers its own weakly
strict service curve. -/
theorem isWeaklyStrictServiceCurve_weaklyStrictServiceRel
    (beta : ℝ≥0 → ℝ≥0) :
    IsWeaklyStrictServiceCurve beta (weaklyStrictServiceRel beta) :=
  fun _ _ hp => hp.2

/-- Weakly strict service curves are antitone: a smaller `beta` is
still offered. -/
theorem IsWeaklyStrictServiceCurve.mono
    {S : Curve → Curve → Prop} {beta beta' : ℝ≥0 → ℝ≥0}
    (h : beta ≤ beta') (hβ : IsWeaklyStrictServiceCurve beta' S) :
    IsWeaklyStrictServiceCurve beta S :=
  fun A D hp t =>
    le_trans (add_le_add le_rfl (h _)) (hβ A D hp t)

/-- A causal `S` offers the weakly strict `beta` iff its pairs all lie
in `weaklyStrictServiceRel beta`. -/
theorem isWeaklyStrictServiceCurve_iff_subset
    {S : Curve → Curve → Prop} (hc : IsCausal S) {beta : ℝ≥0 → ℝ≥0} :
    IsWeaklyStrictServiceCurve beta S ↔
      ∀ A D : Curve, S A D → weaklyStrictServiceRel beta A D := by
  constructor
  · intro h A D hp
    exact ⟨hc A D hp, h A D hp⟩
  · intro h A D hp
    exact (h A D hp).2

/-- The weakly-strict relation is antitone in `beta`. -/
theorem weaklyStrictServiceRel_mono
    {beta beta' : ℝ≥0 → ℝ≥0} (h : beta' ≤ beta) :
    weaklyStrictServiceRel beta ≤ weaklyStrictServiceRel beta' := by
  intro A D hp
  exact ⟨hp.1,
    ((isWeaklyStrictServiceCurve_weaklyStrictServiceRel beta).mono h)
      A D hp⟩

/-- **A strict service curve is weakly strict**: the interval from the
start of the backlogged period of `t` is backlogged, so the strict
increment applies there. -/
theorem IsStrictMinimalServiceCurve.isWeaklyStrictServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S) :
    IsWeaklyStrictServiceCurve beta S :=
  fun A D hp t =>
    hβ A D hp (start ⇑A ⇑D t) t (start_le ⇑A ⇑D t)
      (isBacklogged_Ioc_start (fun x => hc A D hp x) t)

/-- Hierarchy, lower inclusion: the strict relation refines the weakly
strict one. -/
theorem strictServiceRel_le_weaklyStrictServiceRel
    (beta : ℝ≥0 → ℝ≥0) :
    strictServiceRel beta ≤ weaklyStrictServiceRel beta := by
  intro A D hp
  exact ⟨hp.1,
    (isStrictMinimalServiceCurve_strictServiceRel
      beta).isWeaklyStrictServiceCurve (fun _ _ hq => hq.1) A D hp⟩

/-- Output bound: a weakly-strict pair clears the arrivals present at
the start, `A(Start(t)) + β(t − Start(t)) ≤ D(t)`. -/
theorem weaklyStrictServiceRel_output_bound (beta : ℝ≥0 → ℝ≥0)
    (A D : Curve) (hp : weaklyStrictServiceRel beta A D) (t : ℝ≥0) :
    A (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ D t := by
  rw [A.apply_start_eq D (fun x => hp.1 x) t]
  exact hp.2 t

/-- **A weakly strict service curve is a min-plus service curve**: at
`s = start ⇑A ⇑D t` the output bound gives
`A s + beta (t - s) ≤ D t`, and the split `s + (t - s) = t` bounds the
convolution. -/
theorem IsWeaklyStrictServiceCurve.isMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0}
    (hβ : IsWeaklyStrictServiceCurve beta S) (hc : IsCausal S) :
    IsMinimalServiceCurve (liftEReal beta) S := by
  intro A D hp t
  have hst : start ⇑A ⇑D t ≤ t := start_le ⇑A ⇑D t
  have hbound : A (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ D t :=
    weaklyStrictServiceRel_output_bound beta A D
      ⟨hc A D hp, hβ A D hp⟩ t
  calc minConv (curveEReal A) (liftEReal beta) t
      ≤ curveEReal A (start ⇑A ⇑D t)
          + liftEReal beta (t - start ⇑A ⇑D t) :=
        minConv_le_add _ _ (add_tsub_cancel_of_le hst)
    _ ≤ curveEReal D t := by
        simp only [curveEReal_apply]
        exact_mod_cast hbound

/-- Hierarchy, upper inclusion: the weakly strict relation refines the
min-plus one. -/
theorem weaklyStrictServiceRel_le_minimalServiceRel
    (beta : ℝ≥0 → ℝ≥0) :
    weaklyStrictServiceRel beta ≤ minimalServiceRel (liftEReal beta) := by
  intro A D hp
  exact ⟨curveEReal_mono hp.1,
    (isWeaklyStrictServiceCurve_weaklyStrictServiceRel
      beta).isMinimalServiceCurve (fun _ _ hq => hq.1) A D hp⟩

/-! ## Book restatement (the middle of the service-curve hierarchy)
For every `β`, `S_strict(β) ⊆ S_wstrict(β) ⊆ S_mp(β)` — the two upper
inclusions of the hierarchy theorem (the bottom layer, variable
capacity nodes, is a separate chapter). The min-plus transport of the
strict theory factors through the weakly strict layer verbatim: the
strict hypothesis is only ever used at the start of backlogged
periods. -/
example (beta : ℝ≥0 → ℝ≥0) :
    strictServiceRel beta ≤ weaklyStrictServiceRel beta
      ∧ weaklyStrictServiceRel beta
        ≤ minimalServiceRel (liftEReal beta) :=
  ⟨strictServiceRel_le_weaklyStrictServiceRel beta,
    weaklyStrictServiceRel_le_minimalServiceRel beta⟩

end DeepWiki
