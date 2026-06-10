import Book.ServiceCurveStrict
import Book.DeviationsBoundsServer
import Book.DeviationsRestricted

/-! # Strict service curves are minimal service curves
The inclusion of the strict into the min-plus service-curve theory: a strict
minimal service curve is in particular a minimal service curve (lifted into
`EReal` via `liftEReal`), so the deviation bounds for servers apply —
including the restricted-domain bounds, through the unconditional
super-additive closure on the `ℝ≥0∞` carrier. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Deviation

/-- **A strict service curve is a min-plus service curve.** At
`s = start A D t`, the start-of-backlog output bound gives
`A s + beta (t - s) ≤ D t`, and the split `s + (t - s) = t` bounds the
convolution: `(A ∗ beta) t ≤ A s + beta (t - s) ≤ D t`. -/
theorem IsStrictMinimalServiceCurve.isMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S) :
    IsMinimalServiceCurve (liftEReal beta) S := by
  intro A D hp t
  have hst : start A D t ≤ t := start_le A D t
  have hbound : A (start A D t) + beta (t - start A D t) ≤ D t :=
    strictServiceRel_output_bound beta A D ⟨hc A D hp, hβ A D hp⟩ t
  calc minConv (curveE A) (liftEReal beta) t
      ≤ curveE A (start A D t) + liftEReal beta (t - start A D t) :=
        minConv_le_add _ _ (add_tsub_cancel_of_le hst)
    _ ≤ curveE D t := by
        show ((A (start A D t) : ℝ) : EReal)
            + ((beta (t - start A D t) : ℝ) : EReal) ≤ ((D t : ℝ) : EReal)
        rw [← EReal.coe_add]
        exact_mod_cast hbound

/-- The largest-relation form: the largest strict-service relation is
contained in the largest relation offering `liftEReal beta` as a minimal
service curve. -/
theorem strictServiceRel_le_minimalServiceRel (beta : ℝ≥0 → ℝ≥0) :
    strictServiceRel beta ≤ minimalServiceRel (liftEReal beta) := by
  intro A D hp
  exact ⟨curveE_mono hp.1,
    (isStrictMinimalServiceCurve_strictServiceRel beta).isMinimalServiceCurve
      (fun _ _ hq => hq.1) A D hp⟩

namespace Deviation

/-- The `ℝ≥0∞` reading of the `EReal` lift is the `ℝ≥0∞` lift:
`toENN (liftEReal f) = liftENN f`. -/
theorem toENN_liftEReal (f : ℝ≥0 → ℝ≥0) :
    toENN (liftEReal f) = liftENN f := by
  funext s
  show (((f s : ℝ) : EReal)).toENNReal = ((f s : ℝ≥0) : ℝ≥0∞)
  rw [← EReal.coe_nnreal_eq_coe_real, EReal.toENNReal_coe]

/-- The strict backlog bound iterates through the `ℝ≥0∞` closure powers:
on a backlogged `(s, t]`, `D s + maxConvPow (liftENN beta) n (t - s) ≤ D t`,
splitting the period at each convolution split. -/
theorem add_maxConvPow_le_of_isBacklogged
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve beta S) {A D : Curve} (hp : S A D)
    (n : ℕ) {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged A D (Set.Ioc s t)) :
    (D s : ℝ≥0∞) + maxConvPow (liftENN beta) n (t - s) ≤ (D t : ℝ≥0∞) := by
  induction n generalizing s t with
  | zero =>
      show (D s : ℝ≥0∞) + ((beta (t - s) : ℝ≥0) : ℝ≥0∞)
        ≤ ((D t : ℝ≥0) : ℝ≥0∞)
      exact_mod_cast hβ A D hp s t hst hbl
  | succ n ih =>
      show (D s : ℝ≥0∞)
        + ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t - s},
            (maxConvPow (liftENN beta) n p.1.1
              + maxConvPow (liftENN beta) n p.1.2)
        ≤ (D t : ℝ≥0∞)
      rw [ENNReal.add_iSup]
      refine iSup_le ?_
      rintro ⟨⟨a, b⟩, (hab : a + b = t - s)⟩
      have hsum : s + a + b = t := by
        rw [add_assoc, hab, add_tsub_cancel_of_le hst]
      have hat : s + a ≤ t := by
        rw [← hsum]; exact le_self_add
      have h1 := ih (le_self_add : s ≤ s + a)
        (hbl.subset (Set.Ioc_subset_Ioc_right hat))
      rw [add_tsub_cancel_left] at h1
      have h2 := ih hat (hbl.subset (Set.Ioc_subset_Ioc_left le_self_add))
      rw [show t - (s + a) = b by rw [← hsum, add_tsub_cancel_left]] at h2
      calc (D s : ℝ≥0∞)
          + (maxConvPow (liftENN beta) n a + maxConvPow (liftENN beta) n b)
          = ((D s : ℝ≥0∞) + maxConvPow (liftENN beta) n a)
              + maxConvPow (liftENN beta) n b := (add_assoc _ _ _).symm
        _ ≤ (D (s + a) : ℝ≥0∞) + maxConvPow (liftENN beta) n b :=
            add_le_add h1 le_rfl
        _ ≤ (D t : ℝ≥0∞) := h2

/-- Strict service yields the raw `ℝ≥0∞` convolution inequality for the
closure: `(A ∗ superadditiveClosureMaxNN (liftENN beta)) ≤ D`, by the
start-of-backlog split — no boundedness of `beta` needed. -/
theorem minConv_superadditiveClosureMaxNN_le_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    {A D : Curve} (hp : S A D) (t : ℝ≥0) :
    minConv (liftENN ⇑A) (superadditiveClosureMaxNN (liftENN beta)) t
      ≤ (D t : ℝ≥0∞) := by
  have hcAD : ∀ x, D x ≤ A x := hc A D hp
  have hst : start A D t ≤ t := start_le A D t
  have hcl : (D (start A D t) : ℝ≥0∞)
      + superadditiveClosureMaxNN (liftENN beta) (t - start A D t)
      ≤ (D t : ℝ≥0∞) := by
    show (D (start A D t) : ℝ≥0∞)
      + ⨆ n : ℕ, maxConvPow (liftENN beta) n (t - start A D t)
      ≤ (D t : ℝ≥0∞)
    rw [ENNReal.add_iSup]
    exact iSup_le fun n =>
      add_maxConvPow_le_of_isBacklogged hβ hp n hst
        (isBacklogged_Ioc_start A D hcAD t)
  calc minConv (liftENN ⇑A) (superadditiveClosureMaxNN (liftENN beta)) t
      ≤ liftENN ⇑A (start A D t)
          + superadditiveClosureMaxNN (liftENN beta) (t - start A D t) :=
        minConv_le_add _ _ (add_tsub_cancel_of_le hst)
    _ ≤ (D t : ℝ≥0∞) := by
        rw [show liftENN ⇑A (start A D t) = ((D (start A D t) : ℝ≥0) : ℝ≥0∞) by
          show ((A (start A D t) : ℝ≥0) : ℝ≥0∞) = _
          rw [A_start_eq_D_start A D hcAD t]]
        exact hcl

/-- **Backlog bound for strict service** (pointwise): a causal pair with
strict service `beta`, the arrival having maximal arrival curve `α`, has
backlog at each `t` bounded by the vertical deviation
`vDev α (liftENN beta)`. -/
theorem coe_backlogAt_le_vDev_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    (hp : S A D) (harr : IsMaximalArrivalBound (liftENN ⇑A) α) (t : ℝ≥0) :
    (backlogAt ⇑A ⇑D t : ℝ≥0∞) ≤ vDev α (liftENN beta) := by
  have h := coe_backlogAt_le_vDev_of_isMinimalServiceCurve
    (hβ.isMinimalServiceCurve hc) hp (isNonneg_liftEReal beta) harr t
  rwa [toENN_liftEReal] at h

/-- **Backlog bound for strict service**:
`b(A, D) ≤ vDev α (liftENN beta)`. -/
theorem backlog_le_vDev_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    (hp : S A D) (harr : IsMaximalArrivalBound (liftENN ⇑A) α) :
    backlog ⇑A ⇑D ≤ vDev α (liftENN beta) := by
  have h := backlog_le_vDev_of_isMinimalServiceCurve
    (hβ.isMinimalServiceCurve hc) hp (isNonneg_liftEReal beta) harr
  rwa [toENN_liftEReal] at h

/-- **Delay bound for strict service.** With `beta` additionally monotone,
the delay is at most the horizontal deviation `hDev α (liftENN beta)`. -/
theorem delay_le_hDev_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    (hp : S A D) (hmono : Monotone beta)
    (harr : IsMaximalArrivalBound (liftENN ⇑A) α) :
    delay ⇑A ⇑D ≤ (hDev α (liftENN beta) : ℝ≥0∞) := by
  have h := delay_le_hDev_of_isMinimalServiceCurve
    (hβ.isMinimalServiceCurve hc) hp (isNonneg_liftEReal beta)
    (monotone_liftEReal hmono) harr
  rwa [toENN_liftEReal] at h

/-- **Backlog from a restricted domain, strict service.** A causal pair
with strict service `beta`, the arrival allowing `α`, has backlog bounded
by the vertical deviations against `beta` on `[0, τ]`, for any positive
crossing point `α τ ≤ liftENN beta τ`: the unconditional `ℝ≥0∞`
super-additive closure of `beta` is served, super-additive, and dominates
`beta`. -/
theorem backlog_le_biSup_vDevAt_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    (hp : S A D) (harr : IsMaximalArrivalBound (liftENN ⇑A) α)
    {τ : ℝ≥0} (hτ : 0 < τ) (hcross : α τ ≤ liftENN beta τ) :
    backlog ⇑A ⇑D ≤ ⨆ t ≤ τ, vDevAt α (liftENN beta) t := by
  have hleβ := le_superadditiveClosureMaxNN (liftENN beta)
  have hleα := subadditiveClosureE_le α
  have hmain :=
    (backlog_le_vDev harr.subadditiveClosureE
        (minConv_superadditiveClosureMaxNN_le_of_isStrictMinimalServiceCurve
          hβ hc hp)).trans_eq
      (vDev_eq_biSup_of_crossing (subadditiveClosureE_subadditive α)
        (isSuperadditive_superadditiveClosureMaxNN (liftENN beta)) hτ
        (((hleα τ).trans hcross).trans (hleβ τ)))
  refine hmain.trans (iSup₂_mono fun t _ => ?_)
  exact vDevAt_mono (fun t' => hleα t') hleβ t

/-- **Delay from a restricted domain, strict service.** Under the same
hypotheses, with `beta` additionally monotone, the delay is bounded by the
horizontal deviations against `beta` on `[0, τ]`. -/
theorem delay_le_biSup_hDevAt_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    (hp : S A D) (hmono : Monotone beta)
    (harr : IsMaximalArrivalBound (liftENN ⇑A) α)
    {τ : ℝ≥0} (hτ : 0 < τ) (hcross : α τ ≤ liftENN beta τ) :
    delay ⇑A ⇑D ≤ ⨆ t ≤ τ, (hDevAt α (liftENN beta) t : ℝ≥0∞) := by
  have hleβ := le_superadditiveClosureMaxNN (liftENN beta)
  have hleα := subadditiveClosureE_le α
  have hmain :=
    (delay_le_hDev A.mono
        (monotone_superadditiveClosureMaxNN (monotone_liftENN hmono))
        harr.subadditiveClosureE
        (minConv_superadditiveClosureMaxNN_le_of_isStrictMinimalServiceCurve
          hβ hc hp)).trans_eq
      (hDev_eq_biSup_of_crossing (subadditiveClosureE_subadditive α)
        (isSuperadditive_superadditiveClosureMaxNN (liftENN beta)) hτ
        (((hleα τ).trans hcross).trans (hleβ τ)))
  refine hmain.trans (iSup₂_mono fun t _ => ?_)
  exact hDevAt_mono (fun t' => hleα t') hleβ t

/-- **Backlog from the first crossing, strict service.** Without
attainment: a causal pair with strict service `beta`, the arrival having
maximal arrival curve `α`, has backlog bounded by the vertical deviations
against `beta` on `[0, ℓmax]`,
`ℓmax = sInf (crossingSet α (liftENN beta))` — the super-additive closure
of `beta` dominates `beta`, so `α` crosses it no later. -/
theorem backlog_le_biSup_vDevAt_sInf_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    (hp : S A D) (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hne : (crossingSet α (liftENN beta)).Nonempty) :
    backlog ⇑A ⇑D
      ≤ ⨆ t ≤ sInf (crossingSet α (liftENN beta)),
          vDevAt α (liftENN beta) t := by
  have hleβ := le_superadditiveClosureMaxNN (liftENN beta)
  have hleα := subadditiveClosureE_le α
  have hclo := harr.subadditiveClosureE
  have hsubset : crossingSet α (liftENN beta)
      ⊆ crossingSet (subadditiveClosureE α)
          (superadditiveClosureMaxNN (liftENN beta)) :=
    (crossingSet_mono_right hleβ).trans (crossingSet_anti_left hleα)
  have hℓ : sInf (crossingSet (subadditiveClosureE α)
        (superadditiveClosureMaxNN (liftENN beta)))
      ≤ sInf (crossingSet α (liftENN beta)) :=
    csInf_le_csInf (OrderBot.bddBelow _) hne hsubset
  have hmain :=
    (backlog_le_vDev hclo.2
        (minConv_superadditiveClosureMaxNN_le_of_isStrictMinimalServiceCurve
          hβ hc hp)).trans_eq
      (vDev_eq_biSup_sInf_crossingSet (subadditiveClosureE_subadditive α)
        (isSuperadditive_superadditiveClosureMaxNN (liftENN beta))
        hclo.1 (hne.mono hsubset))
  exact hmain.trans
    (le_trans
      (iSup₂_mono fun t _ => vDevAt_mono (fun t' => hleα t') hleβ t)
      (biSup_mono fun _ ht => ht.trans hℓ))

/-- **Delay from the first crossing, strict service.** Without attainment:
under the same hypotheses, with `beta` additionally monotone, the delay is
bounded by the horizontal deviations against `beta` on `[0, ℓmax]`. -/
theorem delay_le_biSup_hDevAt_sInf_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    (hp : S A D) (hmono : Monotone beta)
    (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hne : (crossingSet α (liftENN beta)).Nonempty) :
    delay ⇑A ⇑D
      ≤ ⨆ t ≤ sInf (crossingSet α (liftENN beta)),
          (hDevAt α (liftENN beta) t : ℝ≥0∞) := by
  have hleβ := le_superadditiveClosureMaxNN (liftENN beta)
  have hleα := subadditiveClosureE_le α
  have hclo := harr.subadditiveClosureE
  have hsubset : crossingSet α (liftENN beta)
      ⊆ crossingSet (subadditiveClosureE α)
          (superadditiveClosureMaxNN (liftENN beta)) :=
    (crossingSet_mono_right hleβ).trans (crossingSet_anti_left hleα)
  have hℓ : sInf (crossingSet (subadditiveClosureE α)
        (superadditiveClosureMaxNN (liftENN beta)))
      ≤ sInf (crossingSet α (liftENN beta)) :=
    csInf_le_csInf (OrderBot.bddBelow _) hne hsubset
  have hmain :=
    (delay_le_hDev A.mono
        (monotone_superadditiveClosureMaxNN (monotone_liftENN hmono))
        hclo.2
        (minConv_superadditiveClosureMaxNN_le_of_isStrictMinimalServiceCurve
          hβ hc hp)).trans_eq
      (hDev_eq_biSup_sInf_crossingSet (subadditiveClosureE_subadditive α)
        (isSuperadditive_superadditiveClosureMaxNN (liftENN beta))
        hclo.1 (hne.mono hsubset))
  exact hmain.trans
    (le_trans
      (iSup₂_mono fun t _ => hDevAt_mono (fun t' => hleα t') hleβ t)
      (biSup_mono fun _ ht => ht.trans hℓ))

end Deviation

/-! ## Book restatement (strict service curves are service curves)
A server offering a strict service curve `beta` offers `beta` as a plain
min-plus service curve. -/
example {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0}
    (hSrv : IsServer S) (hβ : IsStrictMinimalServiceCurve beta S) :
    IsMinimalServiceCurve (liftEReal beta) S :=
  hβ.isMinimalServiceCurve hSrv.1

/-! ## Book restatement (restricted deviation domain, strict service)
With `ℓmax = inf {t > 0 | α t ≤ beta t}` — the curves do cross, but the
infimum need not be attained — backlog and delay of a pair served with
strict service `beta` (monotone) are bounded by the deviations against
`beta` computed on `[0, ℓmax]`. -/
example {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve}
    (hSrv : IsServer S) (hβ : IsStrictMinimalServiceCurve beta S)
    (hp : S A D) (hmono : Monotone beta)
    (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hne : (crossingSet α (liftENN beta)).Nonempty) :
    backlog ⇑A ⇑D
        ≤ (⨆ t ≤ sInf (crossingSet α (liftENN beta)),
            vDevAt α (liftENN beta) t) ∧
      delay ⇑A ⇑D
        ≤ ⨆ t ≤ sInf (crossingSet α (liftENN beta)),
            (hDevAt α (liftENN beta) t : ℝ≥0∞) :=
  ⟨backlog_le_biSup_vDevAt_sInf_of_isStrictMinimalServiceCurve hβ hSrv.1 hp
      harr hne,
    delay_le_biSup_hDevAt_sInf_of_isStrictMinimalServiceCurve hβ hSrv.1 hp
      hmono harr hne⟩

/-! ## Bridging arrival-curve readings
The maximal length of a backlogged period under the `ℝ≥0∞` reading of the
arrival-curve hypothesis: `liftENN` reflects it onto `ℝ≥0`, where the
strict-service crossing bound applies. -/
example {S : Curve → Curve → Prop} {beta alpha : ℝ≥0 → ℝ≥0}
    (hSrv : IsServer S) (hβ : IsStrictMinimalServiceCurve beta S)
    {A D : Curve} (hp : S A D)
    (harr : IsMaximalArrivalBound (liftENN ⇑A) (liftENN alpha))
    {t d : ℝ≥0} (hbl : IsBacklogged A D (Set.Ioc t (t + d))) :
    (d : ℝ≥0∞) ≤ firstCrossing alpha beta :=
  length_le_firstCrossing_of_isBacklogged hSrv.1 hβ hp
    (isMaximalArrivalBound_liftENN_iff.mp harr) hbl

end DeepWiki
