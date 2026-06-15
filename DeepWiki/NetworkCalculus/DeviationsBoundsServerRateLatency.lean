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
at most `r·T + b` (`r ≤ R`; valid for every `T`, including `T = 0`). -/
theorem backlog_le_of_strictRateLatency_tokenBucket
    {S : Curve → Curve → Prop} {R T r b : ℝ≥0} {A D : Curve}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve (rateLatency R T) S)
    (hp : S A D) (harr : IsMaximalArrivalBound (⇑A) (tokenBucketArrival r b))
    (hr : r ≤ R) :
    Deviation.backlog (⇑A) (⇑D) ≤ ((r * T + b : ℝ≥0) : ℝ≥0∞) := by
  have harrlift : IsMaximalArrivalBound (liftENN ⇑A) (tokenBucketNN r b) := by
    rw [← liftENN_tokenBucketArrival]
    exact isMaximalArrivalBound_liftENN_iff.mpr harr
  have hbridge : toENN (liftEReal (rateLatency R T)) = rateLatencyNN R T := by
    rw [toENN_liftEReal]; funext t; exact (rateLatencyNN_coe R T t).symm
  have hbk := Deviation.backlog_le_vDev_of_isMinimalServiceCurve (hβ.isMinimalServiceCurve hc) hp
    (isNonneg_liftEReal _) harrlift
  rw [hbridge] at hbk
  exact le_trans hbk (vDev_tokenBucketNN_rateLatencyNN_le r b R T hr)

/-- An affine increment bound `A(t+d) ≤ A(t) + (r·d + b)` is a token-bucket arrival curve: the two
agree for `d > 0`, and the `d = 0` increment `A(t) ≤ A(t)` is vacuous. Lets the affine bounds
produced by the network arrival propagation feed the `tokenBucketArrival` server bounds. -/
theorem isMaximalArrivalBound_tokenBucketArrival_of_affine {A : Curve} {r b : ℝ≥0}
    (h : IsMaximalArrivalBound (⇑A) (fun s => r * s + b)) :
    IsMaximalArrivalBound (⇑A) (tokenBucketArrival r b) := by
  rw [isMaximalArrivalBound_iff_increment] at h ⊢
  intro t d
  rcases eq_or_ne d 0 with hd | hd
  · subst hd
    have h0 : tokenBucketArrival r b 0 = 0 := by
      simp [tokenBucketArrival, tokenBucketNN_apply, delayNN, delay_apply]
    rw [h0]; simp
  · have hval : tokenBucketArrival r b d = r * d + b := by
      simp only [tokenBucketArrival, tokenBucketNN_apply_pos r b d hd]
      rw [← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.toNNReal_coe]
    rw [hval]; exact h t d

/-- **Delay bound, affine arrival**: the delay bound `T + b/R` for an input bounded by the affine
increment `r·d + b` (the form the network arrival propagation produces). -/
theorem delay_le_of_strictRateLatency_affine
    {S : Curve → Curve → Prop} {R T r b : ℝ≥0} {A D : Curve}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve (rateLatency R T) S)
    (hp : S A D) (harr : IsMaximalArrivalBound (⇑A) (fun s => r * s + b))
    (hR : 0 < R) (hr : r ≤ R) :
    Deviation.delay (⇑A) (⇑D) ≤ ((T + b / R : ℝ≥0) : ℝ≥0∞) :=
  delay_le_of_strictRateLatency_tokenBucket hc hβ hp
    (isMaximalArrivalBound_tokenBucketArrival_of_affine harr) hR hr

/-- **Backlog bound, affine arrival**: the backlog bound `r·T + b` for an input bounded by the
affine increment `r·d + b`. -/
theorem backlog_le_of_strictRateLatency_affine
    {S : Curve → Curve → Prop} {R T r b : ℝ≥0} {A D : Curve}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve (rateLatency R T) S)
    (hp : S A D) (harr : IsMaximalArrivalBound (⇑A) (fun s => r * s + b))
    (hr : r ≤ R) :
    Deviation.backlog (⇑A) (⇑D) ≤ ((r * T + b : ℝ≥0) : ℝ≥0∞) :=
  backlog_le_of_strictRateLatency_tokenBucket hc hβ hp
    (isMaximalArrivalBound_tokenBucketArrival_of_affine harr) hr

/-! ## Min-service-curve forms
The end-to-end (concatenated) service curve of a tandem is a *minimal* service curve, not a strict
one. These take `IsMinimalServiceCurve (liftEReal β_{R,T}) S` directly — the form the chain
composition (`isMinimalServiceCurve_pmooResidualChain_of_strict_chain`) produces. -/

/-- **Delay bound from a min-plus rate-latency service** (`γ_{r,b}` arrival): delay `≤ T + b/R`. -/
theorem delay_le_of_minRateLatency_tokenBucket
    {S : Curve → Curve → Prop} {R T r b : ℝ≥0} {A D : Curve}
    (hβ : IsMinimalServiceCurve (liftEReal (rateLatency R T)) S)
    (hp : S A D) (harr : IsMaximalArrivalBound (⇑A) (tokenBucketArrival r b))
    (hR : 0 < R) (hr : r ≤ R) :
    Deviation.delay (⇑A) (⇑D) ≤ ((T + b / R : ℝ≥0) : ℝ≥0∞) := by
  have harrlift : IsMaximalArrivalBound (liftENN ⇑A) (tokenBucketNN r b) := by
    rw [← liftENN_tokenBucketArrival]
    exact isMaximalArrivalBound_liftENN_iff.mpr harr
  have hbridge : toENN (liftEReal (rateLatency R T)) = rateLatencyNN R T := by
    rw [toENN_liftEReal]; funext t; exact (rateLatencyNN_coe R T t).symm
  have hdelay := delay_le_hDev_of_isMinimalServiceCurve hβ hp
    (isNonneg_liftEReal _) (monotone_liftEReal (rateLatency_mono R T)) harrlift
  rw [hbridge] at hdelay
  refine le_trans hdelay ?_
  show hDevENN (tokenBucketNN r b) (rateLatencyNN R T) ≤ _
  exact hDevENN_tokenBucketNN_rateLatencyNN_le r b R T hR hr

/-- **Backlog bound from a min-plus rate-latency service** (`γ_{r,b}` arrival): backlog `≤ r·T + b`. -/
theorem backlog_le_of_minRateLatency_tokenBucket
    {S : Curve → Curve → Prop} {R T r b : ℝ≥0} {A D : Curve}
    (hβ : IsMinimalServiceCurve (liftEReal (rateLatency R T)) S)
    (hp : S A D) (harr : IsMaximalArrivalBound (⇑A) (tokenBucketArrival r b))
    (hr : r ≤ R) :
    Deviation.backlog (⇑A) (⇑D) ≤ ((r * T + b : ℝ≥0) : ℝ≥0∞) := by
  have harrlift : IsMaximalArrivalBound (liftENN ⇑A) (tokenBucketNN r b) := by
    rw [← liftENN_tokenBucketArrival]
    exact isMaximalArrivalBound_liftENN_iff.mpr harr
  have hbridge : toENN (liftEReal (rateLatency R T)) = rateLatencyNN R T := by
    rw [toENN_liftEReal]; funext t; exact (rateLatencyNN_coe R T t).symm
  have hbk := Deviation.backlog_le_vDev_of_isMinimalServiceCurve hβ hp
    (isNonneg_liftEReal _) harrlift
  rw [hbridge] at hbk
  exact le_trans hbk (vDev_tokenBucketNN_rateLatencyNN_le r b R T hr)

/-- Affine-arrival form of `delay_le_of_minRateLatency_tokenBucket`. -/
theorem delay_le_of_minRateLatency_affine
    {S : Curve → Curve → Prop} {R T r b : ℝ≥0} {A D : Curve}
    (hβ : IsMinimalServiceCurve (liftEReal (rateLatency R T)) S)
    (hp : S A D) (harr : IsMaximalArrivalBound (⇑A) (fun s => r * s + b))
    (hR : 0 < R) (hr : r ≤ R) :
    Deviation.delay (⇑A) (⇑D) ≤ ((T + b / R : ℝ≥0) : ℝ≥0∞) :=
  delay_le_of_minRateLatency_tokenBucket hβ hp
    (isMaximalArrivalBound_tokenBucketArrival_of_affine harr) hR hr

/-- Affine-arrival form of `backlog_le_of_minRateLatency_tokenBucket`. -/
theorem backlog_le_of_minRateLatency_affine
    {S : Curve → Curve → Prop} {R T r b : ℝ≥0} {A D : Curve}
    (hβ : IsMinimalServiceCurve (liftEReal (rateLatency R T)) S)
    (hp : S A D) (harr : IsMaximalArrivalBound (⇑A) (fun s => r * s + b))
    (hr : r ≤ R) :
    Deviation.backlog (⇑A) (⇑D) ≤ ((r * T + b : ℝ≥0) : ℝ≥0∞) :=
  backlog_le_of_minRateLatency_tokenBucket hβ hp
    (isMaximalArrivalBound_tokenBucketArrival_of_affine harr) hr

end DeepWiki
