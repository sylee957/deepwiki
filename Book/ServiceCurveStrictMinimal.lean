import Book.ServiceCurveStrict
import Book.DeviationsBoundsServer

/-! # Strict service curves are minimal service curves
The inclusion of the strict into the min-plus service-curve theory: a strict
minimal service curve is in particular a minimal service curve (lifted into
`EReal` via `liftEReal`), so the deviation bounds for servers apply. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

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

end Deviation

/-! ## Book restatement (strict service curves are service curves)
A server offering a strict service curve `beta` offers `beta` as a plain
min-plus service curve. -/
example {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0}
    (hSrv : IsServer S) (hβ : IsStrictMinimalServiceCurve beta S) :
    IsMinimalServiceCurve (liftEReal beta) S :=
  hβ.isMinimalServiceCurve hSrv.1

end DeepWiki
