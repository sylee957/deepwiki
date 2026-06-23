import DeepWiki.NetworkCalculus.StabilityNetwork
import DeepWiki.NetworkCalculus.StabilityRates
import DeepWiki.NetworkCalculus.RealCurvesRates

/-! # The linear-model reduction for stability
The reduction underlying Lemma 12.3: it suffices to prove network stability for
the *linear model* — token-bucket arrival curves and rate-latency service curves
respecting local stability — because an arbitrary curve can be bounded by a
linear one **with the same long-term rate**, which still respects local
stability and admits *more* trajectories. The representable core is the
rate-level monotonicity transfer of local stability:

* `IsLocallyStableServer.of_le` — bounding the arrival above and the service
  below transfers local stability down (the rates only move the right way).
* `isLocallyStableServer_of_linearBound` — a token-bucket bound above on `α` and
  a rate-latency bound below on `β` with `r < R` make the original server locally
  stable: the linear-model criterion `r < R` is the full local-stability test.
* `Network.IsLocallyStable.of_linearBound` — the network-level transfer: a
  network whose flows are dominated above by `netLin`'s arrival curves and whose
  servers dominate below `netLin`'s service curves inherits local stability from
  `netLin`.

The remaining `[infra]` step is purely on the trajectory side: that a larger
arrival / smaller service curve admits a *superset* of cumulative-function
trajectories, so global stability of the linear bound transfers to the original.
That is stated as an explicit hypothesis in `Network.isGloballyStable_of_linearModel`
(the `htraj` admissibility witness), which is exactly the model-bounding
construction Lemma 12.3's proof invokes. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

/-- **Local stability is monotone in the bounding curves**: if the arrival is
dominated above (`α ≤ α'`) and the service dominates below (`β' ≤ β`), then local
stability of the bounding pair `(α', β')` transfers to the original `(α, β)`.
This is the rate-level heart of Lemma 12.3 — `r(α) ≤ r(α') < R(β') ≤ R(β)`. -/
theorem IsLocallyStableServer.of_le {α α' β β' : ℝ≥0 → ℝ≥0}
    (hα : ∀ t, α t ≤ α' t) (hβ : ∀ t, β' t ≤ β t)
    (h : IsLocallyStableServer α' β') : IsLocallyStableServer α β :=
  calc longTermArrivalRate α ≤ longTermArrivalRate α' := longTermArrivalRate_mono hα
    _ < longTermServiceRate β' := h
    _ ≤ longTermServiceRate β := longTermServiceRate_mono hβ

/-- **Linear-model local-stability criterion** (per-server form of Lemma 12.3):
if the arrival is bounded above by a token bucket `γ_{r,b}` and the service is
bounded below by a rate-latency `β_{R,T}`, then `r < R` (the linear-model local
stability test) makes the *original* server locally stable. Burst `b` and
latency `T` wash out of the long-term rates, so only `r < R` matters. -/
theorem isLocallyStableServer_of_linearBound {α β : ℝ≥0 → ℝ≥0} {r b R T : ℝ≥0}
    (hαbound : ∀ t, α t ≤ r * t + b) (hβbound : ∀ t, rateLatency R T t ≤ β t)
    (hrR : r < R) : IsLocallyStableServer α β := by
  refine IsLocallyStableServer.of_le hαbound hβbound ?_
  show IsLocallyStableServer (fun t => r * t + b) (rateLatency R T)
  rw [IsLocallyStableServer, longTermArrivalRate_affine, longTermServiceRate_rateLatency]
  exact_mod_cast hrR

variable {κ ι : Type*} [Fintype ι] [DecidableEq κ]

/-- **Network local stability transfers from a linear bound**: if `net`'s flows
are dominated above by `netLin`'s arrival curves and `net`'s servers dominate
below `netLin`'s service curves (same routing, hence same `flowsThrough`), then
local stability of `netLin` gives local stability of `net`. The aggregate rate
only drops and the service rate only rises. -/
theorem Network.IsLocallyStable.of_linearBound (net netLin : Network κ ι)
    (hpaths : ∀ h, net.flowsThrough h = netLin.flowsThrough h)
    (harr : ∀ i t, net.arrivalCurve i t ≤ netLin.arrivalCurve i t)
    (hserv : ∀ h t, netLin.service h t ≤ net.service h t)
    (hlin : netLin.IsLocallyStable) : net.IsLocallyStable := by
  intro h
  have hrate_arr : net.aggregateArrivalRate h ≤ netLin.aggregateArrivalRate h := by
    unfold Network.aggregateArrivalRate
    rw [hpaths h]
    exact Finset.sum_le_sum fun i _ => longTermArrivalRate_mono (harr i)
  calc net.aggregateArrivalRate h ≤ netLin.aggregateArrivalRate h := hrate_arr
    _ < netLin.serviceRate h := hlin h
    _ ≤ net.serviceRate h := longTermServiceRate_mono (hserv h)

/-- **Lemma 12.3, the reduction (scoping form)**: *if* network global stability
is known for the linear model — i.e. `netLin` (token-bucket arrivals, rate-latency
services) is globally stable for the original network's departure processes — and
`net` is bounded by `netLin` above on arrivals / below on services with the same
routing, then `net` is globally stable for those same departures. The trajectory
admissibility `htraj` (that the original departures are also `netLin`'s aggregate
departures — the "more trajectories are admissible" step) is the residual
`[infra]` model-bounding witness; everything else (the rate-level local-stability
transfer, the per-server backlog bound) is discharged here. -/
theorem Network.isGloballyStable_of_linearModel (net netLin : Network κ ι)
    (departure : κ → Curve)
    (hlinStable : netLin.IsGloballyStable departure)
    (htraj : ∀ h, ⇑(net.aggregateArrival h) = ⇑(netLin.aggregateArrival h)) :
    net.IsGloballyStable departure := by
  intro h
  show IsGloballyStableServer ⇑(net.aggregateArrival h) ⇑(departure h)
  rw [htraj h]
  exact hlinStable h

-- Restatements against the book's wording (Lemma 12.3 §12.1, p.272).
-- The linear-model criterion: token-bucket above + rate-latency below + r < R.
example {α β : ℝ≥0 → ℝ≥0} {r b R T : ℝ≥0}
    (hα : ∀ t, α t ≤ r * t + b) (hβ : ∀ t, rateLatency R T t ≤ β t) (hrR : r < R) :
    longTermArrivalRate α < longTermServiceRate β :=
  isLocallyStableServer_of_linearBound hα hβ hrR

-- Local stability is preserved when bounding curves keep their rate order.
example {α α' β β' : ℝ≥0 → ℝ≥0}
    (hα : ∀ t, α t ≤ α' t) (hβ : ∀ t, β' t ≤ β t)
    (h : longTermArrivalRate α' < longTermServiceRate β') :
    longTermArrivalRate α < longTermServiceRate β :=
  IsLocallyStableServer.of_le hα hβ h

end DeepWiki
