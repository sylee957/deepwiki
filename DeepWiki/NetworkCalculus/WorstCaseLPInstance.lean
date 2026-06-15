import DeepWiki.NetworkCalculus.WorstCaseLP
import DeepWiki.NetworkCalculus.RealCurvesDeviations

/-! # Concrete worst-case delay: token-bucket flow through a rate-latency server
The canonical network-calculus instance. The worst-case delay of a token-bucket
flow `γ_{r,b}` (`r ≤ R`) crossing a rate-latency server `β_{R,T}` over *all*
feasible trajectories is exactly the textbook bound `T + b/R` — not merely an
upper bound: `worstCaseServerDelay_eq_hDev` makes it the optimum, and the
horizontal-deviation closed form `hDevENN_tokenBucketNN_rateLatencyNN` evaluates
it. The flow's arrival process is the `ℝ≥0` reading of the token-bucket curve. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Worst-case delay = `T + b/R`** for a token-bucket flow through a rate-latency
server (`R > 0`, `b > 0`, `r ≤ R`): the supremum of the realized delay over every
feasible trajectory equals the textbook bound exactly. -/
theorem worstCaseServerDelay_tokenBucketNN_rateLatencyNN (r b R T : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hrR : r ≤ R) :
    worstCaseServerDelay (fun t => (tokenBucketNN r b t).toNNReal) (rateLatencyNN R T)
      = ((T + b / R : ℝ≥0) : ℝ≥0∞) := by
  have hfin : ∀ t, tokenBucketNN r b t ≠ ⊤ := fun t => by
    have hle : tokenBucketNN r b t ≤ ((r * t + b : ℝ≥0) : ℝ≥0∞) := by
      rw [tokenBucketNN_apply]; push_cast; exact inf_le_left
    exact ne_top_of_le_ne_top (ENNReal.coe_ne_top) hle
  have hlift : Deviation.liftENN (fun t => (tokenBucketNN r b t).toNNReal) = tokenBucketNN r b := by
    funext t; exact ENNReal.coe_toNNReal (hfin t)
  have hmono : Monotone (fun t => (tokenBucketNN r b t).toNNReal) := fun s t hst =>
    ENNReal.toNNReal_mono (hfin t) (tokenBucketNN_mono r b hst)
  have h0 : IsNullAtOrigin (fun t => (tokenBucketNN r b t).toNNReal) := by
    show (tokenBucketNN r b 0).toNNReal = 0
    rw [tokenBucketNN_zero_eq]; rfl
  have hsub : IsSubadditive (fun t => (tokenBucketNN r b t).toNNReal) := fun u s => by
    show (tokenBucketNN r b (u + s)).toNNReal
      ≤ (tokenBucketNN r b u).toNNReal + (tokenBucketNN r b s).toNNReal
    rw [← ENNReal.toNNReal_add (hfin u) (hfin s)]
    exact ENNReal.toNNReal_mono (ENNReal.add_ne_top.mpr ⟨hfin u, hfin s⟩)
      (tokenBucketNN_subadditive r b u s)
  rw [worstCaseServerDelay_eq_hDev hmono h0 hsub (rateLatencyNN_mono R T)
    (rateLatencyNN_zero_eq R T), hlift]
  exact hDevENN_tokenBucketNN_rateLatencyNN r b R T hR hb hrR

end DeepWiki
