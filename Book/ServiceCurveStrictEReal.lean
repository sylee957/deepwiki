import Book.ServiceCurveStrict
import Book.ServiceCurveMinimal
import Book.RealCurves

/-! # Strict service curves with extended (`EReal`) curves
The strict-service relation `strictServiceRel` (`Book.ServiceCurveStrict`) takes
a finite `ℝ≥0`-valued curve, so it cannot express the pure-delay curve `δ_T`
(`+∞` past `T`). This chapter lifts it to `EReal`-valued curves — mirroring the
min-plus side `minimalServiceRel`, which already takes `ℝ≥0 → EReal` — and reads
the delay curve `δ_T` (`0` up to `T`, `+∞` past it; `δ_0` is the min-plus unit):
a pair is strictly served by `δ_T` exactly when every backlogged period has
length at most `T` (the server clears its backlog within `T`). The finite
relation is the special case `strictServiceRel β = strictServiceRelEReal
(liftEReal β)`. -/

namespace DeepWiki

open Set
open scoped Classical NNReal ENNReal

/-- Largest causal relation offering the `EReal` strict service curve `beta`:
`D s + beta (t − s) ≤ D t` (read through `curveEReal`) on each backlogged
period. A `beta` value of `⊤` forbids backlogged periods of that length. -/
def strictServiceRelEReal (beta : ℝ≥0 → EReal) : Curve → Curve → Prop :=
  fun A D => D ≤ A ∧ ∀ s t, s ≤ t →
    IsBacklogged (⇑A) (⇑D) (Set.Ioc s t) →
      curveEReal D s + beta (t - s) ≤ curveEReal D t

/-- `strictServiceRelEReal beta A D` unfolds to causality plus the `EReal`
strict bound on backlogged periods. -/
theorem mem_strictServiceRelEReal_iff {beta : ℝ≥0 → EReal} {A D : Curve} :
    strictServiceRelEReal beta A D ↔
      D ≤ A ∧ ∀ s t, s ≤ t → IsBacklogged (⇑A) (⇑D) (Set.Ioc s t) →
        curveEReal D s + beta (t - s) ≤ curveEReal D t :=
  Iff.rfl

/-- Each curve serves itself with any `EReal` strict curve `≤ 0` at the origin:
the backlogged periods of `(A, A)` are empty except at `s = t`, where the bound
is `beta 0 ≤ 0`. -/
theorem strictServiceRelEReal_self {beta : ℝ≥0 → EReal} (h0 : beta 0 ≤ 0)
    (A : Curve) : strictServiceRelEReal beta A A := by
  refine ⟨fun _ => le_refl _, fun s t hst hbl => ?_⟩
  by_cases h : (Set.Ioc s t).Nonempty
  · obtain ⟨u, hu⟩ := h
    exact absurd (hbl u hu) (lt_irrefl _)
  · rw [Set.not_nonempty_iff_eq_empty, Set.Ioc_eq_empty_iff] at h
    have hst' : s = t := le_antisymm hst (not_lt.mp h)
    subst hst'
    rw [tsub_self]
    exact le_trans (add_le_add le_rfl h0) (le_of_eq (add_zero _))

/-- When `beta 0 ≤ 0`, `strictServiceRelEReal beta` is a server. -/
theorem isServer_strictServiceRelEReal {beta : ℝ≥0 → EReal} (h0 : beta 0 ≤ 0) :
    IsServer (strictServiceRelEReal beta) :=
  ⟨fun _ _ hp => hp.1, fun A => ⟨A, strictServiceRelEReal_self h0 A⟩⟩

/-- The relation `strictServiceRelEReal beta` offers its own strict service
curve: every served pair meets the `EReal` strict bound. -/
theorem isStrictMinimalServiceCurveEReal_strictServiceRelEReal (beta : ℝ≥0 → EReal)
    {A D : Curve} (hp : strictServiceRelEReal beta A D) {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged (⇑A) (⇑D) (Set.Ioc s t)) :
    curveEReal D s + beta (t - s) ≤ curveEReal D t :=
  hp.2 s t hst hbl

/-- Extended strict service curves are antitone: a smaller `beta` is still
offered. -/
theorem strictServiceRelEReal_mono {beta beta' : ℝ≥0 → EReal} (h : beta' ≤ beta) :
    strictServiceRelEReal beta ≤ strictServiceRelEReal beta' := by
  intro A D hp
  exact ⟨hp.1, fun s t hst hbl =>
    le_trans (add_le_add le_rfl (h (t - s))) (hp.2 s t hst hbl)⟩

/-- **The extended relation extends the finite one**: for a finite curve `β`,
`strictServiceRel β = strictServiceRelEReal (liftEReal β)`. -/
theorem strictServiceRel_eq_strictServiceRelEReal_liftEReal {β : ℝ≥0 → ℝ≥0} :
    strictServiceRel β = strictServiceRelEReal (liftEReal β) := by
  funext A D
  apply propext
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨hc, fun s t hst hbl => ?_⟩
    rw [curveEReal_apply, curveEReal_apply]
    exact_mod_cast hb s t hst hbl
  · rintro ⟨hc, hb⟩
    refine ⟨hc, fun s t hst hbl => ?_⟩
    have hbnd := hb s t hst hbl
    rw [curveEReal_apply, curveEReal_apply] at hbnd
    exact_mod_cast hbnd

/-- **The hierarchy `strict ⊆ mp` for extended curves**: every `EReal`-strict
pair is min-plus served. Anchor the convolution at the start `σ` of `t`'s
backlogged period — where `A σ = D σ` — so
`A ∗ beta (t) ≤ A σ + beta (t − σ) = D σ + beta (t − σ) ≤ D t`. -/
theorem strictServiceRelEReal_le_minimalServiceRel {beta : ℝ≥0 → EReal} :
    strictServiceRelEReal beta ≤ minimalServiceRel beta := by
  intro A D hp
  have hc : ∀ x, D x ≤ A x := fun x => hp.1 x
  refine mem_minimalServiceRel_iff.mpr ⟨hp.1, fun t => ?_⟩
  calc minConv (curveEReal A) beta t
      ≤ curveEReal A (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) :=
        minConv_le_add _ _ (add_tsub_cancel_of_le (start_le ⇑A ⇑D t))
    _ = curveEReal D (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) := by
        rw [curveEReal_apply, curveEReal_apply, A.apply_start_eq D hc t]
    _ ≤ curveEReal D t :=
        hp.2 (start ⇑A ⇑D t) t (start_le ⇑A ⇑D t) (isBacklogged_Ioc_start hc t)

/-! ## The pure-delay curve `δ_T`
`delayEReal T` (`Book.RealCurves`, `= delay T`) is the pure-delay service curve
`δ_T`: `0` up to `T`, `⊤ = +∞` past it (`delay_eq_zero`/`delay_eq_top`); at
`T = 0` it is the min-plus unit `δ_0`. -/

/-- **`δ_T` strict service is a backlog bound**: a pair is strictly served by
`δ_T` iff it is causal and every backlogged period has length at most `T` — the
`⊤` past `T` forbids any longer backlogged period, while up to `T` the bound is
just monotonicity of `D`. -/
theorem mem_strictServiceRelEReal_delay_iff {T : ℝ≥0} {A D : Curve} :
    strictServiceRelEReal (delayEReal T) A D ↔
      D ≤ A ∧ ∀ s t, s ≤ t → IsBacklogged (⇑A) (⇑D) (Set.Ioc s t) → t - s ≤ T := by
  rw [mem_strictServiceRelEReal_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hb s t hst hbl
    by_contra hcon
    rw [not_le] at hcon
    have hbnd := hb s t hst hbl
    simp only [delayEReal] at hbnd
    rw [delay_eq_top T hcon, curveEReal_apply, curveEReal_apply,
      EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at hbnd
    exact absurd hbnd (not_le.mpr (EReal.coe_lt_top _))
  · intro hb s t hst hbl
    simp only [delayEReal]
    rw [delay_eq_zero T (hb s t hst hbl), add_zero]
    exact monotone_curveEReal D hst

/-- **The Prop 6.2 reduction step**: a finite strict curve `β` vanishing on
`[0, T]` is dominated by `δ_T`, so every `δ_T`-strict pair is `β`-strict —
`S_strict(δ_T) ⊆ S_strict(β)`. (A monotone `β` with `β T = 0` vanishes on
`[0, T]`.) -/
theorem strictServiceRelEReal_delay_le_strictServiceRel {β : ℝ≥0 → ℝ≥0} {T : ℝ≥0}
    (hβT : ∀ t, t ≤ T → β t = 0) :
    strictServiceRelEReal (delayEReal T) ≤ strictServiceRel β := by
  rw [strictServiceRel_eq_strictServiceRelEReal_liftEReal]
  refine strictServiceRelEReal_mono fun t => ?_
  rcases le_or_gt t T with ht | ht
  · simp only [delayEReal]
    rw [delay_eq_zero T ht]
    show ((β t : ℝ) : EReal) ≤ 0
    rw [hβT t ht]
    simp
  · simp only [delayEReal]
    rw [delay_eq_top T ht]
    exact le_top

/-- **Per-stage strictness via a time-warp** (the reverse-dilution core): if a
curve `D` is the time-warp `D τ = X (h τ)` of a curve `X` by a warp `h ≤ id` whose
below-diagonal set `{τ | h τ < τ}` has every backlogged window of length `≤ d`
(`hcatch`: any `(s, t]` on which `h τ < τ` throughout has `t − s ≤ d`), then
`(X, D) ∈ S_strict(δ_d)`. The backlog of `(X, X ∘ h)` is contained in
`{τ | h τ < τ}` for any monotone `X` (since `X (h τ) < X τ` forces `h τ < τ`), so
strictness reduces to a property of the warp alone — independent of `X`. This is
the per-server step of Lemma 9.5's reverse dilution: each tandem stage warps its
input by a staggered catch-up `h`, and the closure's pure delay `δ_d` is met
because the warp catches up to the identity within `d`. -/
theorem strictServiceRelEReal_delay_of_comp_warp {X D : Curve} {h : ℝ≥0 → ℝ≥0}
    {d : ℝ≥0} (hcomp : ∀ τ, D τ = X (h τ)) (hh_le : ∀ τ, h τ ≤ τ)
    (hcatch : ∀ s t, s ≤ t → (∀ τ ∈ Set.Ioc s t, h τ < τ) → t - s ≤ d) :
    strictServiceRelEReal (delayEReal d) X D := by
  refine mem_strictServiceRelEReal_delay_iff.mpr ⟨fun τ => ?_, fun s t hst hbl => ?_⟩
  · rw [hcomp τ]; exact X.mono (hh_le τ)
  · refine hcatch s t hst (fun τ hτ => ?_)
    have hb := hbl τ hτ
    rw [hcomp τ] at hb
    rcases (hh_le τ).lt_or_eq with hlt | heq
    · exact hlt
    · rw [heq] at hb; exact absurd hb (lt_irrefl _)

/-- **Catch-up density bounds backlogged windows**: if a warp `h` has a fixed point
(catch-up `h p = p`) in every half-open window `(x, x + d]`, then any interval
`(s, t]` on which `h τ < τ` throughout has length `t − s ≤ d`. A window longer than
`d` would contain a catch-up point `p ∈ (s, s + d] ⊆ (s, t]` with `h p = p`,
contradicting `h p < p`. -/
theorem catch_window_le {h : ℝ≥0 → ℝ≥0} {d : ℝ≥0}
    (hdense : ∀ x : ℝ≥0, ∃ p, x < p ∧ p ≤ x + d ∧ h p = p)
    {s t : ℝ≥0} (hst : s ≤ t) (hwin : ∀ τ ∈ Set.Ioc s t, h τ < τ) :
    t - s ≤ d := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨p, hsp, hpsd, hfix⟩ := hdense s
  have hsdt : s + d < t :=
    calc s + d < s + (t - s) := by gcongr
      _ = t := add_tsub_cancel_of_le hst
  have hb := hwin p ⟨hsp, (lt_of_le_of_lt hpsd hsdt).le⟩
  rw [hfix] at hb
  exact absurd hb (lt_irrefl p)

/-- **Per-stage strictness via a catch-up warp**: combining the warp core with
catch-up density — if `D τ = X (h τ)` for `h ≤ id` with a catch-up `h p = p` in
every window `(x, x + d]`, then `(X, D) ∈ S_strict(δ_d)`. This is the clean
per-server hypothesis for Lemma 9.5's reverse dilution: each tandem stage is a
continuous warp `h` of its input that catches up to the identity within `d`. -/
theorem strictServiceRelEReal_delay_of_comp_catchUp {X D : Curve} {h : ℝ≥0 → ℝ≥0}
    {d : ℝ≥0} (hcomp : ∀ τ, D τ = X (h τ)) (hh_le : ∀ τ, h τ ≤ τ)
    (hdense : ∀ x : ℝ≥0, ∃ p, x < p ∧ p ≤ x + d ∧ h p = p) :
    strictServiceRelEReal (delayEReal d) X D :=
  strictServiceRelEReal_delay_of_comp_warp hcomp hh_le
    (fun _ _ hst hwin => catch_window_le hdense hst hwin)

/-! ## Book restatement
`δ_T` (`+∞` past `T`) is unrepresentable for the finite `strictServiceRel`; over
`EReal` it reads exactly as the delay bound — a causal pair is in `S_strict(δ_T)`
iff its backlog never persists longer than `T`. The finite strict relation is the
extended one at a finite curve. -/
example {T : ℝ≥0} (A D : Curve) :
    strictServiceRelEReal (delayEReal T) A D ↔
      D ≤ A ∧ ∀ s t, s ≤ t → IsBacklogged (⇑A) (⇑D) (Set.Ioc s t) → t - s ≤ T :=
  mem_strictServiceRelEReal_delay_iff

example {β : ℝ≥0 → ℝ≥0} :
    strictServiceRel β = strictServiceRelEReal (liftEReal β) :=
  strictServiceRel_eq_strictServiceRelEReal_liftEReal

/-! The delay curve lands in the hierarchy: `S_strict(δ_T) ⊆ S_mp(δ_T)` — a
delay-bounded server is min-plus served by `δ_T`. -/
example (T : ℝ≥0) :
    strictServiceRelEReal (delayEReal T) ≤ minimalServiceRel (delayEReal T) :=
  strictServiceRelEReal_le_minimalServiceRel

end DeepWiki
