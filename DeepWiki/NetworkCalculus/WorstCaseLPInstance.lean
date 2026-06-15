import DeepWiki.NetworkCalculus.WorstCaseLPBacklog
import DeepWiki.NetworkCalculus.RealCurvesDeviations

/-! # Concrete worst-case delay and backlog: token-bucket through rate-latency
The canonical network-calculus instance. The worst-case delay (resp. backlog) of a
token-bucket flow `γ_{r,b}` (`r ≤ R`) crossing a rate-latency server `β_{R,T}` over
*all* feasible trajectories is exactly the textbook bound `T + b/R` (resp.
`r·T + b`) — not merely an upper bound: the worst-case-equals-optimum theorems make
it the optimum, and the deviation closed forms evaluate it. The flow's arrival
process is the `ℝ≥0` reading `tokenBucketArrival` of the token-bucket curve. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The `ℝ≥0` cumulative reading of the token-bucket curve `γ_{r,b}` (finite, so
its `ℝ≥0∞` lift is `tokenBucketNN`). -/
noncomputable def tokenBucketArrival (r b : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => (tokenBucketNN r b t).toNNReal

/-- `tokenBucketNN r b t` is finite. -/
theorem tokenBucketNN_ne_top (r b t : ℝ≥0) : tokenBucketNN r b t ≠ ⊤ := by
  have hle : tokenBucketNN r b t ≤ ((r * t + b : ℝ≥0) : ℝ≥0∞) := by
    rw [tokenBucketNN_apply]; push_cast; exact inf_le_left
  exact ne_top_of_le_ne_top (ENNReal.coe_ne_top) hle

/-- The `ℝ≥0∞` lift of `tokenBucketArrival` is the token-bucket curve `tokenBucketNN`. -/
@[simp] theorem liftENN_tokenBucketArrival (r b : ℝ≥0) :
    Deviation.liftENN (tokenBucketArrival r b) = tokenBucketNN r b := by
  funext t; exact ENNReal.coe_toNNReal (tokenBucketNN_ne_top r b t)

/-- `tokenBucketArrival r b` is monotone. -/
theorem tokenBucketArrival_mono (r b : ℝ≥0) : Monotone (tokenBucketArrival r b) :=
  fun _ t hst => ENNReal.toNNReal_mono (tokenBucketNN_ne_top r b t) (tokenBucketNN_mono r b hst)

/-- `tokenBucketArrival r b` is null at the origin. -/
theorem tokenBucketArrival_nullAtOrigin (r b : ℝ≥0) :
    IsNullAtOrigin (tokenBucketArrival r b) := by
  show (tokenBucketNN r b 0).toNNReal = 0
  rw [tokenBucketNN_zero_eq]; rfl

/-- `tokenBucketArrival r b` is sub-additive. -/
theorem tokenBucketArrival_subadditive (r b : ℝ≥0) :
    IsSubadditive (tokenBucketArrival r b) := fun u s => by
  show (tokenBucketNN r b (u + s)).toNNReal
    ≤ (tokenBucketNN r b u).toNNReal + (tokenBucketNN r b s).toNNReal
  rw [← ENNReal.toNNReal_add (tokenBucketNN_ne_top r b u) (tokenBucketNN_ne_top r b s)]
  exact ENNReal.toNNReal_mono
    (ENNReal.add_ne_top.mpr ⟨tokenBucketNN_ne_top r b u, tokenBucketNN_ne_top r b s⟩)
    (tokenBucketNN_subadditive r b u s)

/-- **Worst-case delay = `T + b/R`** for a token-bucket flow through a rate-latency
server (`R > 0`, `b > 0`, `r ≤ R`): the supremum of the realized delay over every
feasible trajectory equals the textbook bound exactly. -/
theorem worstCaseServerDelay_tokenBucketNN_rateLatencyNN (r b R T : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hrR : r ≤ R) :
    worstCaseServerDelay (tokenBucketArrival r b) (rateLatencyNN R T)
      = ((T + b / R : ℝ≥0) : ℝ≥0∞) := by
  rw [worstCaseServerDelay_eq_hDev (tokenBucketArrival_mono r b)
      (tokenBucketArrival_nullAtOrigin r b) (tokenBucketArrival_subadditive r b)
      (rateLatencyNN_mono R T) (rateLatencyNN_zero_eq R T), liftENN_tokenBucketArrival]
  exact hDevENN_tokenBucketNN_rateLatencyNN r b R T hR hb hrR

/-- **Worst-case backlog = `r·T + b`** for a token-bucket flow through a rate-latency
server (`r ≤ R`, `T > 0`): the supremum of the realized backlog over every feasible
trajectory equals the textbook bound exactly. -/
theorem worstCaseServerBacklog_tokenBucketNN_rateLatencyNN (r b R T : ℝ≥0)
    (hrR : r ≤ R) (hT : 0 < T) :
    worstCaseServerBacklog (tokenBucketArrival r b) (rateLatencyNN R T)
      = ((r * T + b : ℝ≥0) : ℝ≥0∞) := by
  rw [worstCaseServerBacklog_eq_vDev (tokenBucketArrival_mono r b)
      (tokenBucketArrival_nullAtOrigin r b) (tokenBucketArrival_subadditive r b)
      (rateLatencyNN_zero_eq R T), liftENN_tokenBucketArrival]
  exact vDev_tokenBucketNN_rateLatencyNN r b R T hrR hT

end DeepWiki
