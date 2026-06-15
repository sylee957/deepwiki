import DeepWiki.NetworkCalculus.StabilityRates
import DeepWiki.NetworkCalculus.ServersResidual

/-! # Residual service rate and rate-derived local stability
The rate-level closure of the SFA cross-traffic analysis: under blind
multiplexing the residual service rate survives subtracting the cross-traffic
rate, `R(β) ≤ r(α) + R(β ⊖ α)`, so a flow whose own rate plus its cross-traffic
rate stays below the aggregate service rate is *locally stable against its
residual* — discharging the `hstab` hypothesis of `isGloballyStable_residualPath`
from the pure rate condition `r(αi) + r(αcross) < R(β)`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Residual service rate lower bound**: for non-decreasing `β` the residual
`[β − α]⁺↑` keeps service rate at least `R(β) − r(α)`, i.e.
`R(β) ≤ r(α) + R(residualCurve β α)`. The non-decreasing closure only raises the
curve (`tsub_le_residualCurve`), and the truncated-difference rate split
(`longTermServiceRate_tsub_ge`) finishes. -/
theorem longTermServiceRate_residualCurve_ge {β α : ℝ≥0 → ℝ≥0} (hβ : Monotone β) :
    longTermServiceRate β
      ≤ longTermArrivalRate α + longTermServiceRate (residualCurve β α) := by
  refine le_trans (longTermServiceRate_tsub_ge β α) ?_
  gcongr
  exact longTermServiceRate_mono fun t =>
    tsub_le_residualCurve (closureBddAbove_tsub_of_monotone hβ) le_rfl

/-- **Residual local stability from the rate condition**: if the tagged flow's
rate plus its cross-traffic rate is below the aggregate service rate,
`r(αi) + r(αcross) < R(β)`, then the tagged flow is locally stable against its
blind-multiplexing residual `residualCurve β αcross`. This *derives* the SFA
`hstab` hypothesis from the rate sum (cancelling the finite cross-traffic rate
through the residual-rate lower bound), rather than assuming it. -/
theorem isLocallyStableServer_residualCurve_of_rate_lt {β αi αcross : ℝ≥0 → ℝ≥0}
    (hβ : Monotone β) (hcrossfin : longTermArrivalRate αcross < ⊤)
    (hrate : longTermArrivalRate αi + longTermArrivalRate αcross
              < longTermServiceRate β) :
    IsLocallyStableServer αi (residualCurve β αcross) := by
  have h1 : longTermArrivalRate αcross + longTermArrivalRate αi
      < longTermArrivalRate αcross + longTermServiceRate (residualCurve β αcross) := by
    rw [add_comm (longTermArrivalRate αcross) (longTermArrivalRate αi)]
    exact lt_of_lt_of_le hrate (longTermServiceRate_residualCurve_ge hβ)
  exact (ENNReal.add_lt_add_iff_left hcrossfin.ne).mp h1

end DeepWiki
