import DeepWiki.NetworkCalculus.StabilityResidualRate
import DeepWiki.NetworkCalculus.RealCurvesRates

/-! # A worked stability instance on the canonical curves
The rate route end-to-end on token-bucket flows and a rate-latency server: two
flows `γ_{r₁,b₁}`, `γ_{r₂,b₂}` sharing a server `β_{R,T}` under blind
multiplexing, with `r₁ + r₂ < R`, leave each flow locally stable against its
residual — every hypothesis discharged from the single rate inequality via the
closed-form curve rates and the residual-rate bound. This verifies that the
abstract `isLocallyStableServer_residualCurve_of_rate_lt` says the right thing
on the concrete curves of §12.1. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Concrete residual local stability**: a token-bucket flow `γ_{r₁,b₁}` sharing
a rate-latency server `β_{R,T}` with token-bucket cross-traffic `γ_{r₂,b₂}` under
blind multiplexing is locally stable against its residual `β_{R,T} ⊖ γ_{r₂,b₂}`
whenever `r₁ + r₂ < R` — the closed-form rates (`r(γ)=r`, `R(β_{R,T})=R`) reduce
the residual-rate condition to the single inequality. -/
theorem isLocallyStableServer_tokenBucket_rateLatency
    (r₁ b₁ r₂ b₂ R T : ℝ≥0) (hlt : r₁ + r₂ < R) :
    IsLocallyStableServer (fun t => r₁ * t + b₁)
      (residualCurve (rateLatency R T) (fun t => r₂ * t + b₂)) := by
  refine isLocallyStableServer_residualCurve_of_rate_lt (rateLatency_mono R T) ?_ ?_
  · rw [longTermArrivalRate_affine]; exact ENNReal.coe_lt_top
  · rw [longTermArrivalRate_affine, longTermArrivalRate_affine,
      longTermServiceRate_rateLatency, ← ENNReal.coe_add]
    exact_mod_cast hlt

end DeepWiki
