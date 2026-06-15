import DeepWiki.NetworkCalculus.DeviationsBoundsServer
import DeepWiki.NetworkCalculus.RealCurvesDeviations
import DeepWiki.NetworkCalculus.ServiceCurveStrictMinimal
import DeepWiki.NetworkCalculus.WorstCaseLPInstance

/-! # Server delay / backlog bounds for the canonical curves
The standard network-calculus performance bounds at the server-relation level: a pair served by a
relation `S` offering the strict rate-latency service `β_{R,T}`, whose input is token-bucket
`γ_{r,b}`-constrained, has delay at most `T + b/R` and backlog at most `r·T + b`. These specialize
the generic server deviation bounds (`delay_le_hDev_of_isMinimalServiceCurve`,
`backlog_le_vDev_of_isMinimalServiceCurve`) to the rate-latency / token-bucket closed forms
(`hDevENN_tokenBucketNN_rateLatencyNN_le`, `vDev_tokenBucketNN_rateLatencyNN`), discharging the
strict→minimal and `ℝ≥0`/`EReal`/`ℝ≥0∞` reading bridges once. They are the per-server building
block for the per-flow delay/backlog bounds in a stable network. -/

namespace DeepWiki

open scoped NNReal ENNReal
open Deviation

/-- **Delay bound** (`β_{R,T}` strict service, `γ_{r,b}` arrival): a pair served by `S` with strict
rate-latency service `β_{R,T}` whose input is token-bucket `γ_{r,b}`-constrained has virtual delay
at most `T + b/R` (`0 < R`, `r ≤ R`). -/
theorem delay_le_of_strictRateLatency_tokenBucket
    {S : Curve → Curve → Prop} {R T r b : ℝ≥0} {A D : Curve}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve (rateLatency R T) S)
    (hp : S A D) (harr : IsMaximalArrivalBound (⇑A) (tokenBucketArrival r b))
    (hR : 0 < R) (hr : r ≤ R) :
    Deviation.delay (⇑A) (⇑D) ≤ ((T + b / R : ℝ≥0) : ℝ≥0∞) := by
  have harrlift : IsMaximalArrivalBound (liftENN ⇑A) (tokenBucketNN r b) := by
    rw [← liftENN_tokenBucketArrival]
    exact isMaximalArrivalBound_liftENN_iff.mpr harr
  have hbridge : toENN (liftEReal (rateLatency R T)) = rateLatencyNN R T := by
    rw [toENN_liftEReal]; funext t; exact (rateLatencyNN_coe R T t).symm
  have hdelay := delay_le_hDev_of_isMinimalServiceCurve (hβ.isMinimalServiceCurve hc) hp
    (isNonneg_liftEReal _) (monotone_liftEReal (rateLatency_mono R T)) harrlift
  rw [hbridge] at hdelay
  refine le_trans hdelay ?_
  show hDevENN (tokenBucketNN r b) (rateLatencyNN R T) ≤ _
  exact hDevENN_tokenBucketNN_rateLatencyNN_le r b R T hR hr

/-- **Backlog bound** (`β_{R,T}` strict service, `γ_{r,b}` arrival): a pair served by `S` with
strict rate-latency service `β_{R,T}` whose input is token-bucket `γ_{r,b}`-constrained has backlog
at most `r·T + b` (`r ≤ R`, `0 < T`). -/
theorem backlog_le_of_strictRateLatency_tokenBucket
    {S : Curve → Curve → Prop} {R T r b : ℝ≥0} {A D : Curve}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve (rateLatency R T) S)
    (hp : S A D) (harr : IsMaximalArrivalBound (⇑A) (tokenBucketArrival r b))
    (hr : r ≤ R) (hT : 0 < T) :
    Deviation.backlog (⇑A) (⇑D) ≤ ((r * T + b : ℝ≥0) : ℝ≥0∞) := by
  have harrlift : IsMaximalArrivalBound (liftENN ⇑A) (tokenBucketNN r b) := by
    rw [← liftENN_tokenBucketArrival]
    exact isMaximalArrivalBound_liftENN_iff.mpr harr
  have hbridge : toENN (liftEReal (rateLatency R T)) = rateLatencyNN R T := by
    rw [toENN_liftEReal]; funext t; exact (rateLatencyNN_coe R T t).symm
  have hbk := Deviation.backlog_le_vDev_of_isMinimalServiceCurve (hβ.isMinimalServiceCurve hc) hp
    (isNonneg_liftEReal _) harrlift
  rw [hbridge] at hbk
  refine le_trans hbk ?_
  rw [vDev_tokenBucketNN_rateLatencyNN r b R T hr hT]

end DeepWiki
