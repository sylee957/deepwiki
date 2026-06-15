import DeepWiki.NetworkCalculus.ArrivalCurvesOutput
import DeepWiki.NetworkCalculus.RealCurvesDeconv

/-! # Output burstiness of the canonical flow/server pair
The standard network-calculus fact: a token-bucket flow through a rate-latency
server leaves with its burst grown by the service latency times the rate. The
output arrival bound is the deconvolution `γ_{r,b} ⊘ β_{R,T} = affine r (b + r·T)`
(`minDeconv_tokenBucketNN_rateLatencyNN`) fed through the strict-service output
theorem. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Output of a token-bucket flow through a rate-latency server**: for `γ_{r,b}`
(`r ≤ R`, `T > 0`) crossing a strict rate-latency server `β_{R,T}` (here the
`ℝ≥0`-valued service `t ↦ R·(t−T)`), the output is bounded by the affine curve
`r·t + (b + r·T)` — the burst grows from `b` to `b + r·T`. -/
theorem isMaximalArrivalBound_output_tokenBucket_rateLatency
    {S : Curve → Curve → Prop} (hc : IsCausal S) {R T : ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve (fun t => R * (t - T)) S)
    {A D : Curve} (hp : S A D) {r b : ℝ≥0} (hr : r ≤ R) (hT : 0 < T)
    (harr : IsMaximalArrivalBound (Deviation.liftENN ⇑A) (tokenBucketNN r b)) :
    IsMaximalArrivalBound (Deviation.liftENN ⇑D) (affine r (b + r * T)) := by
  have hlift : Deviation.liftENN (fun t : ℝ≥0 => R * (t - T)) = rateLatencyNN R T := by
    funext t; exact (rateLatencyNN_coe R T t).symm
  have h := isMaximalArrivalBound_output_of_isStrictMinimalServiceCurve hc hβ hp harr
  rw [hlift, minDeconv_tokenBucketNN_rateLatencyNN r b R T hr hT] at h
  exact h

end DeepWiki
