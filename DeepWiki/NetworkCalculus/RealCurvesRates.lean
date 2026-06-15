import DeepWiki.NetworkCalculus.RealCurves
import DeepWiki.NetworkCalculus.StabilityRates

/-! # Long-term rates of the canonical curves
Closed forms for the long-term rates: the rate curve `λ_R = R·t` has both
long-term arrival and service rate `R`; the affine (token-bucket) arrival curve
`r·t + b` has arrival rate `r` (the burst `b` washes out); the rate-latency
service curve `β_{R,T} = R·(t − T)` has service rate `R` (the latency `T` washes
out). The washing-out rests on `↑c / ↑t → 0` and the constant-shift invariance
of the rate. These verify the rate machinery against the curve catalog. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal Topology
open Filter

/-- A constant over `t` vanishes at infinity: `↑c / ↑t → 0` as `t → ∞`. -/
theorem tendsto_coe_div_atTop_nhds_zero (c : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => (c : ℝ≥0∞) / (t : ℝ≥0∞)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun t : ℝ≥0 => ((t : ℝ≥0∞))⁻¹) atTop (𝓝 0) := by
    rw [← ENNReal.inv_top]
    exact tendsto_inv_iff.mpr (ENNReal.tendsto_coe_nhds_top.mpr tendsto_id)
  have h := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)) hinv (Or.inr (by simp))
  simpa only [div_eq_mul_inv, mul_zero] using h

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

/-- Adding a constant burst does not change the long-term arrival rate: the
burst washes out under division by `t`, `r(α + b) = r(α)`. -/
theorem longTermArrivalRate_add_const (α : ℝ≥0 → ℝ≥0) (b : ℝ≥0) :
    longTermArrivalRate (fun t => α t + b) = longTermArrivalRate α := by
  simp only [longTermArrivalRate]
  have hfun : (fun t : ℝ≥0 => ((α t + b : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞))
      = (fun t : ℝ≥0 => (α t : ℝ≥0∞) / (t : ℝ≥0∞))
        + fun t : ℝ≥0 => (b : ℝ≥0∞) / (t : ℝ≥0∞) := by
    funext t
    simp only [Pi.add_apply]
    rw [ENNReal.coe_add, ENNReal.add_div]
  rw [hfun, ENNReal.limsup_add_of_right_tendsto_zero (tendsto_coe_div_atTop_nhds_zero b)]

/-- The affine (token-bucket) arrival curve `t ↦ r·t + b` has long-term arrival
rate `r`: the burst `b` washes out. -/
theorem longTermArrivalRate_affine (r b : ℝ≥0) :
    longTermArrivalRate (fun t => r * t + b) = (r : ℝ≥0∞) := by
  rw [show (fun t : ℝ≥0 => r * t + b) = fun t => rate r t + b from rfl,
    longTermArrivalRate_add_const, longTermArrivalRate_rate]

/-- The rate-latency curve `β_{R,T} = R·(t − T)` has long-term service rate `R`:
the latency `T` washes out, `liminf R·(t−T)/t = R`. -/
theorem longTermServiceRate_rateLatency (R T : ℝ≥0) :
    longTermServiceRate (rateLatency R T) = (R : ℝ≥0∞) := by
  -- `(t − T)/t → 1`
  have hratio : Tendsto (fun t : ℝ≥0 => ((t - T : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ≥0 => (1 : ℝ≥0∞) - (T : ℝ≥0∞) / (t : ℝ≥0∞)) atTop (𝓝 1) := by
      have h := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞)))
        (tendsto_coe_div_atTop_nhds_zero T) (Or.inl ENNReal.one_ne_top)
      simpa using h
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    show (1 : ℝ≥0∞) - (T : ℝ≥0∞) / (t : ℝ≥0∞) = ((t - T : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞)
    rw [ENNReal.coe_sub, ENNReal.sub_div (fun _ _ => by exact_mod_cast ht.ne'),
      ENNReal.div_self (by exact_mod_cast ht.ne') ENNReal.coe_ne_top]
  -- `R·(t−T)/t = R · ((t−T)/t) → R · 1 = R`
  have hlim : Tendsto
      (fun t : ℝ≥0 => ((rateLatency R T t : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞)) atTop (𝓝 (R : ℝ≥0∞)) := by
    have h := ENNReal.Tendsto.const_mul (a := (R : ℝ≥0∞)) hratio (Or.inr ENNReal.coe_ne_top)
    rw [mul_one] at h
    refine h.congr' (Eventually.of_forall fun t => ?_)
    show (R : ℝ≥0∞) * (((t - T : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞))
        = ((rateLatency R T t : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞)
    rw [rateLatency, ENNReal.coe_mul, mul_div_assoc]
  rw [longTermServiceRate]
  exact hlim.liminf_eq

end DeepWiki
