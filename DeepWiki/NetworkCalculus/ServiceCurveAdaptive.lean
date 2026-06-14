import DeepWiki.NetworkCalculus.ConvolutionMinimum
import DeepWiki.NetworkCalculus.ServiceCurveMinimal

/-! # Adaptive service curves
The two-curve adaptive type: `β` plays the min-plus role and `β̃` the
strict role — on every window `s ≤ t` the output gains either the
strict-type increment from `s` or the min-plus bound through the
window. With `β ≤ β̃` the type refines min-plus service; the
convolution output itself meets the adaptive pair `(β, β)` for
super-additive continuous `β` (the book states this for piecewise
linear convex `β`, whose content is exactly super-additivity with
attainment). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The adaptive service bound: on every window `s ≤ t` the output
gains the strict-type increment `D s + β̃ (t − s)` or the
min-plus-type bound through the window,
`min (D s + β̃ (t − s)) (inf_{s≤u≤t} (A u + β (t − u))) ≤ D t`. -/
def IsAdaptiveServiceBound (beta betaStrict A D : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ t, ∀ s ≤ t,
    min (D s + betaStrict (t - s))
      (⨅ u : {u : ℝ≥0 // s ≤ u ∧ u ≤ t}, A u.1 + beta (t - u.1))
      ≤ D t

/-- The largest relation offering the adaptive pair `(β, β̃)`:
causality plus the adaptive bound. -/
def adaptiveServiceRel (beta betaStrict : ℝ≥0 → ℝ≥0) :
    Curve → Curve → Prop :=
  fun A D => D ≤ A ∧ IsAdaptiveServiceBound beta betaStrict ⇑A ⇑D

/-- `adaptiveServiceRel beta betaStrict A D` unfolds to causality
plus the adaptive bound. -/
theorem mem_adaptiveServiceRel_iff {beta betaStrict : ℝ≥0 → ℝ≥0}
    {A D : Curve} :
    adaptiveServiceRel beta betaStrict A D ↔
      D ≤ A ∧ IsAdaptiveServiceBound beta betaStrict ⇑A ⇑D :=
  Iff.rfl

/-- Each curve serves itself adaptively for `beta` null at the
origin: the windowed infimum at `u = t` is `A t`. -/
theorem adaptiveServiceRel_self {beta betaStrict : ℝ≥0 → ℝ≥0}
    (h0 : beta 0 = 0) (A : Curve) :
    adaptiveServiceRel beta betaStrict A A := by
  refine ⟨fun _ => le_rfl, fun t s hst => ?_⟩
  refine le_trans (min_le_right _ _) ?_
  refine le_trans (ciInf_le (OrderBot.bddBelow _) ⟨t, hst, le_rfl⟩) ?_
  rw [tsub_self, h0, add_zero]

/-- When `beta 0 = 0`, `adaptiveServiceRel beta betaStrict` is a
server. -/
theorem isServer_adaptiveServiceRel {beta betaStrict : ℝ≥0 → ℝ≥0}
    (h0 : beta 0 = 0) :
    IsServer (adaptiveServiceRel beta betaStrict) :=
  ⟨fun _ _ hp => hp.1, fun A => ⟨A, adaptiveServiceRel_self h0 A⟩⟩

/-- The adaptive relation is antitone in both curves. -/
theorem adaptiveServiceRel_mono
    {beta beta' betaStrict betaStrict' : ℝ≥0 → ℝ≥0}
    (hβ : beta' ≤ beta) (hβs : betaStrict' ≤ betaStrict) :
    adaptiveServiceRel beta betaStrict
      ≤ adaptiveServiceRel beta' betaStrict' := by
  rintro A D ⟨hc, hb⟩
  refine ⟨hc, fun t s hst => le_trans (min_le_min
    (add_le_add le_rfl (hβs _))
    (ciInf_mono (OrderBot.bddBelow _)
      (fun u => add_le_add le_rfl (hβ _)))) (hb t s hst)⟩

/-- **An adaptive pair with `β ≤ β̃` is min-plus served at `β`**: at
`s = 0` both branches of the adaptive minimum dominate the
convolution — the strict branch via the `(0, t)` split and `β ≤ β̃`,
the windowed branch term by term. -/
theorem adaptiveServiceRel_le_minimalServiceRel
    {beta betaStrict : ℝ≥0 → ℝ≥0} (h : beta ≤ betaStrict) :
    adaptiveServiceRel beta betaStrict
      ≤ minimalServiceRel (liftEReal beta) := by
  rintro A D ⟨hc, hb⟩
  refine ⟨curveEReal_mono hc, fun t => ?_⟩
  have hbt := hb t 0 zero_le'
  rcases min_le_iff.mp hbt with hcase | hcase
  · -- strict branch: `D 0 + β̃ t ≤ D t`, and the convolution sits
    -- below `β t ≤ β̃ t` via the `(0, t)` split
    refine le_trans (minConv_le_add _ _ (zero_add t)) ?_
    rw [curveEReal_zero, zero_add, curveEReal_apply]
    have hval : beta t ≤ D t := by
      have hD0 : D 0 = 0 := D.zero
      rw [hD0, zero_add, tsub_zero] at hcase
      exact le_trans (h t) hcase
    show ((beta t : ℝ) : EReal) ≤ ((D t : ℝ) : EReal)
    exact_mod_cast hval
  · -- windowed branch: ε-room between the `ℝ≥0` infimum and the
    -- `EReal` convolution
    by_contra hcon
    rw [not_le] at hcon
    haveI : Nonempty {u : ℝ≥0 // 0 ≤ u ∧ u ≤ t} :=
      ⟨⟨0, zero_le', zero_le'⟩⟩
    obtain ⟨c, hc1, hc2⟩ := EReal.exists_between_coe_real hcon
    have hεpos : (0 : ℝ) < c - (D t : ℝ) := by
      refine sub_pos.mpr ?_
      have hc1' : (((D t : ℝ≥0) : ℝ) : EReal) < (c : EReal) := hc1
      exact_mod_cast hc1'
    have hlt : (⨅ u : {u : ℝ≥0 // 0 ≤ u ∧ u ≤ t},
        (A u.1 + beta (t - u.1)))
        < D t + (c - (D t : ℝ)).toNNReal :=
      lt_of_le_of_lt hcase
        (lt_add_of_pos_right _ (Real.toNNReal_pos.mpr hεpos))
    obtain ⟨u, hu⟩ := exists_lt_of_ciInf_lt hlt
    have huR : ((A u.1 + beta (t - u.1) : ℝ≥0) : ℝ) < c := by
      have h := (NNReal.coe_lt_coe.mpr hu :
        ((A u.1 + beta (t - u.1) : ℝ≥0) : ℝ) < _)
      push_cast [Real.coe_toNNReal _ hεpos.le] at h ⊢
      linarith
    have hchain : minConv (curveEReal A) (liftEReal beta) t
        ≤ (((A u.1 + beta (t - u.1) : ℝ≥0) : ℝ) : EReal) := by
      refine le_trans (minConv_le_add _ _
        (add_tsub_cancel_of_le u.2.2)) ?_
      rw [curveEReal_apply]
      push_cast
      exact le_rfl
    exact absurd (lt_of_le_of_lt hchain (by exact_mod_cast huR))
      (not_lt.mpr hc2.le)

/-- **The convolution output meets the adaptive pair `(β, β)`** for
super-additive continuous `β`: with the `t`-window minimum attained
at `v`, a window start `s ≤ v` puts `v` in the windowed infimum, and
`v < s` routes through the strict branch by super-additivity. -/
theorem isAdaptiveServiceBound_minConvProj {A beta : ℝ≥0 → ℝ≥0}
    (hmono : Monotone A) (hlc : IsLeftContinuous A)
    (hcont : Continuous beta) (hsup : IsSuperadditive beta) :
    IsAdaptiveServiceBound beta beta A (minConvProj A beta) := by
  intro t s hst
  obtain ⟨v, hvt, hterm, hval⟩ := exists_minConvProj_eq hmono hlc hcont t
  rcases le_or_gt s v with hsv | hvs
  · refine le_trans (min_le_right _ _) ?_
    rw [hval]
    exact ciInf_le_of_le (OrderBot.bddBelow _) ⟨v, hsv, hvt⟩ le_rfl
  · refine le_trans (min_le_left _ _) ?_
    have hDs : minConvProj A beta s ≤ A v + beta (s - v) :=
      minConvProj_le_add (add_tsub_cancel_of_le hvs.le)
    calc minConvProj A beta s + beta (t - s)
        ≤ (A v + beta (s - v)) + beta (t - s) := add_le_add hDs le_rfl
      _ = A v + (beta (s - v) + beta (t - s)) := add_assoc _ _ _
      _ ≤ A v + beta ((s - v) + (t - s)) :=
          add_le_add le_rfl (hsup _ _)
      _ = A v + beta (t - v) := by
          rw [show (s - v) + (t - s) = t - v from by
            rw [add_comm]
            exact tsub_add_tsub_cancel hst hvs.le]
      _ = minConvProj A beta t := hval.symm

/-! ## Book restatement (adaptive service curves)
A server offering the adaptive pair compares to a min-plus server:
if `β ≤ β̃` then `S_asc(β, β̃) ⊆ S_mp(β)`; and the convolution output
realizes the adaptive pair `(β, β)` — the book states the latter for
piecewise linear convex `β ∈ F₀↑`, whose operative content is
super-additivity (a convex curve null at the origin is
super-additive) together with attainment of the window minimum
(continuity); the bound-level statement keeps the output as the
plain function `A ∗ β`, its curve regularity being a separate
question. -/
example {beta betaStrict : ℝ≥0 → ℝ≥0} (h : beta ≤ betaStrict) :
    adaptiveServiceRel beta betaStrict
      ≤ minimalServiceRel (liftEReal beta) :=
  adaptiveServiceRel_le_minimalServiceRel h
example {A beta : ℝ≥0 → ℝ≥0}
    (hmono : Monotone A) (hlc : IsLeftContinuous A)
    (hcont : Continuous beta) (hsup : IsSuperadditive beta) :
    IsAdaptiveServiceBound beta beta A (minConvProj A beta) :=
  isAdaptiveServiceBound_minConvProj hmono hlc hcont hsup

end DeepWiki
