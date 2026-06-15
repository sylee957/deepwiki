import DeepWiki.NetworkCalculus.RealCurves
import DeepWiki.NetworkCalculus.StabilityRates

/-! # Long-term rates of the canonical curves
Closed forms for the long-term rates: the rate curve `λ_R = R·t` has both
long-term arrival and service rate `R` (it is `R` exactly, once divided by `t`).
These verify the rate machinery against the curve catalog. (The rate-latency and
token-bucket closed forms — `R(β_{R,T}) = R`, `r(γ_{r,b}) = r` — additionally
need the `T/t → 0` / `b/t → 0` limits and are left to a follow-up.) -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Filter

/-- After dividing by `t`, the rate curve `λ_R` is the constant `R` for every
positive time: `↑(R·t)/↑t = ↑R`. -/
theorem rate_div_eventually_eq (R : ℝ≥0) :
    (fun t : ℝ≥0 => ((rate R t : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞)) =ᶠ[atTop]
      (fun _ => (R : ℝ≥0∞)) := by
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [rate_apply, ENNReal.coe_mul, mul_div_assoc,
    ENNReal.div_self (by exact_mod_cast ht.ne') ENNReal.coe_ne_top, mul_one]

/-- The rate curve `λ_R` has long-term service rate `R`. -/
theorem longTermServiceRate_rate (R : ℝ≥0) : longTermServiceRate (rate R) = (R : ℝ≥0∞) := by
  rw [longTermServiceRate, Filter.liminf_congr (rate_div_eventually_eq R), Filter.liminf_const]

/-- The rate curve `λ_R` has long-term arrival rate `R`. -/
theorem longTermArrivalRate_rate (R : ℝ≥0) : longTermArrivalRate (rate R) = (R : ℝ≥0∞) := by
  rw [longTermArrivalRate, Filter.limsup_congr (rate_div_eventually_eq R), Filter.limsup_const]

end DeepWiki
