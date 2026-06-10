import Book.ServiceCurveStrict
import Book.DeviationsBoundsServer
import Book.DeviationsRestricted

/-! # Strict service curves are minimal service curves
The inclusion of the strict into the min-plus service-curve theory: a strict
minimal service curve is in particular a minimal service curve (lifted into
`EReal` via `liftEReal`), so the deviation bounds for servers apply —
including the restricted-domain bounds, through the super-additive closure
under an affine rate bound. -/

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

/-- **Backlog bound for strict service** (pointwise): a causal pair with
strict service `beta`, the arrival having maximal arrival curve `α`, has
backlog at each `t` bounded by the vertical deviation
`vDev α (liftENN beta)`. -/
theorem coe_backlogAt_le_vDev_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    (hp : S A D) (harr : IsMaximalArrivalCurve (liftENN ⇑A) α) (t : ℝ≥0) :
    (backlogAt ⇑A ⇑D t : ℝ≥0∞) ≤ vDev α (liftENN beta) := by
  have h := coe_backlogAt_le_vDev_of_isMinimalServiceCurve
    (hβ.isMinimalServiceCurve hc) hp (isNonneg_liftEReal beta) harr t
  rwa [toENN_liftEReal] at h

/-- **Backlog bound for strict service**:
`b(A, D) ≤ vDev α (liftENN beta)`. -/
theorem backlog_le_vDev_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    (hp : S A D) (harr : IsMaximalArrivalCurve (liftENN ⇑A) α) :
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
    (harr : IsMaximalArrivalCurve (liftENN ⇑A) α) :
    delay ⇑A ⇑D ≤ (hDev α (liftENN beta) : ℝ≥0∞) := by
  have h := delay_le_hDev_of_isMinimalServiceCurve
    (hβ.isMinimalServiceCurve hc) hp (isNonneg_liftEReal beta)
    (monotone_liftEReal hmono) harr
  rwa [toENN_liftEReal] at h

/-- **Backlog from a restricted domain, strict service.** A causal pair with
strict service `beta` under an affine rate bound, the arrival allowing `α`,
has backlog bounded by the vertical deviations against `beta` on `[0, τ]`,
for any positive crossing point `α τ ≤ liftENN beta τ`: the super-additive
closure of `beta` is still offered, is super-additive, and dominates
`beta`. -/
theorem backlog_le_biSup_vDevAt_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    (hp : S A D) (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hr : ∃ r : ℝ≥0, ∀ s, beta s ≤ r * s)
    {τ : ℝ≥0} (hτ : 0 < τ) (hcross : α τ ≤ liftENN beta τ) :
    backlog ⇑A ⇑D ≤ ⨆ t ≤ τ, vDevAt α (liftENN beta) t := by
  have hcross' : α τ ≤ toENN (liftEReal (superadditiveClosureMax beta)) τ := by
    rw [toENN_liftEReal]
    exact hcross.trans (ENNReal.coe_le_coe.mpr
      (le_superadditiveClosureMax_of_affine_bound hr τ))
  have hmain := backlog_le_biSup_vDevAt_of_isMinimalServiceCurve
    ((isStrictMinimalServiceCurve_superadditiveClosureMax beta
        hβ).isMinimalServiceCurve hc)
    hp (isNonneg_liftEReal _) harr
    ((isSuperadditive_superadditiveClosureMax_of_affine_bound hr).liftEReal)
    hτ hcross'
  rw [toENN_liftEReal] at hmain
  refine hmain.trans (iSup₂_mono fun t _ => ?_)
  exact vDevAt_mono le_rfl
    (fun t' => ENNReal.coe_le_coe.mpr
      (le_superadditiveClosureMax_of_affine_bound hr t')) t

/-- **Delay from a restricted domain, strict service.** Under the same
hypotheses, with `beta` additionally monotone, the delay is bounded by the
horizontal deviations against `beta` on `[0, τ]`. -/
theorem delay_le_biSup_hDevAt_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S)
    (hp : S A D) (hmono : Monotone beta)
    (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hr : ∃ r : ℝ≥0, ∀ s, beta s ≤ r * s)
    {τ : ℝ≥0} (hτ : 0 < τ) (hcross : α τ ≤ liftENN beta τ) :
    delay ⇑A ⇑D ≤ ⨆ t ≤ τ, (hDevAt α (liftENN beta) t : ℝ≥0∞) := by
  have hcross' : α τ ≤ toENN (liftEReal (superadditiveClosureMax beta)) τ := by
    rw [toENN_liftEReal]
    exact hcross.trans (ENNReal.coe_le_coe.mpr
      (le_superadditiveClosureMax_of_affine_bound hr τ))
  have hmain := delay_le_biSup_hDevAt_of_isMinimalServiceCurve
    ((isStrictMinimalServiceCurve_superadditiveClosureMax beta
        hβ).isMinimalServiceCurve hc)
    hp (isNonneg_liftEReal _)
    (monotone_liftEReal
      (monotone_superadditiveClosureMax_of_affine_bound hmono hr))
    harr
    ((isSuperadditive_superadditiveClosureMax_of_affine_bound hr).liftEReal)
    hτ hcross'
  rw [toENN_liftEReal] at hmain
  refine hmain.trans (iSup₂_mono fun t _ => ?_)
  exact hDevAt_mono le_rfl
    (fun t' => ENNReal.coe_le_coe.mpr
      (le_superadditiveClosureMax_of_affine_bound hr t')) t

end Deviation

/-! ## Book restatement (strict service curves are service curves)
A server offering a strict service curve `beta` offers `beta` as a plain
min-plus service curve. -/
example {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0}
    (hSrv : IsServer S) (hβ : IsStrictMinimalServiceCurve beta S) :
    IsMinimalServiceCurve (liftEReal beta) S :=
  hβ.isMinimalServiceCurve hSrv.1

/-! ## Book restatement (restricted deviation domain, strict service)
With `ℓmax = inf {t > 0 | α t ≤ beta t}` itself a crossing point (the
infimum attained), backlog and delay of a pair served with strict service
`beta` (monotone, affinely rate-bounded) are bounded by the deviations
against `beta` computed on `[0, ℓmax]`. -/
example {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve}
    (hSrv : IsServer S) (hβ : IsStrictMinimalServiceCurve beta S)
    (hp : S A D) (hmono : Monotone beta)
    (harr : IsMaximalArrivalCurve (liftENN ⇑A) α)
    (hr : ∃ r : ℝ≥0, ∀ s, beta s ≤ r * s)
    {ℓmax : ℝ≥0}
    (_hℓ : ℓmax = sInf (crossingSet α (liftENN beta)))
    (hmem : ℓmax ∈ crossingSet α (liftENN beta)) :
    backlog ⇑A ⇑D ≤ (⨆ t ≤ ℓmax, vDevAt α (liftENN beta) t) ∧
      delay ⇑A ⇑D ≤ ⨆ t ≤ ℓmax, (hDevAt α (liftENN beta) t : ℝ≥0∞) :=
  ⟨backlog_le_biSup_vDevAt_of_isStrictMinimalServiceCurve hβ hSrv.1 hp harr
      hr hmem.1 hmem.2,
    delay_le_biSup_hDevAt_of_isStrictMinimalServiceCurve hβ hSrv.1 hp hmono
      harr hr hmem.1 hmem.2⟩

/-! ## Bridging arrival-curve readings
The maximal length of a backlogged period under the `ℝ≥0∞` reading of the
arrival-curve hypothesis: `liftENN` reflects it onto `ℝ≥0`, where the
strict-service crossing bound applies. -/
example {S : Curve → Curve → Prop} {beta alpha : ℝ≥0 → ℝ≥0}
    (hSrv : IsServer S) (hβ : IsStrictMinimalServiceCurve beta S)
    {A D : Curve} (hp : S A D)
    (harr : IsMaximalArrivalCurve (liftENN ⇑A) (liftENN alpha))
    {t d : ℝ≥0} (hbl : IsBacklogged A D (Set.Ioc t (t + d))) :
    (d : ℝ≥0∞) ≤ firstCrossing alpha beta :=
  length_le_firstCrossing_of_isBacklogged hSrv.1 hβ hp
    (isMaximalArrivalCurve_liftENN_iff.mp harr) hbl

end DeepWiki
