import DeepWiki.NetworkCalculus.StabilityGlobal
import DeepWiki.NetworkCalculus.StabilityRates
import DeepWiki.NetworkCalculus.ServersResidualGps

/-! # Per-flow stability under GPS
The GPS analogue of the static-priority stability: in a GPS server flow `i`
receives its weighted share `(φᵢ/∑ⱼ φⱼ)·β` of the aggregate service
(`isStrictMinimalServiceCurve_residualServer_of_isGps`) — independent of the
cross-traffic. So flow `i` is globally stable once locally stable against that
share, and (since scaling the curve scales the rate) once
`r(αᵢ) < (φᵢ/∑ⱼ φⱼ)·R(β)` — the book's GPS local-stability condition
(Theorem 12.4). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **GPS per-flow global stability**: in a GPS server with strict aggregate
service `β`, flow `i` — locally stable against its weighted share
`(φᵢ/∑ⱼ φⱼ)·β` — has a bounded backlogged period. -/
theorem isGloballyStableServer_gps {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {φ : ι → ℝ≥0} {β αi : ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S) (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hgps : IsGpsServerN φ S)
    {As Ds : ι → Curve} (hp : S As Ds)
    (harr : IsMaximalArrivalBound (⇑(As i)) αi)
    (hstab : IsLocallyStableServer αi (fun v => (φ i / ∑ j, φ j) * β v)) :
    IsGloballyStableServer (⇑(As i)) (⇑(Ds i)) :=
  isGloballyStableServer_of_isLocallyStableServer
    (isCausal_residualServer hcaus i)
    (isStrictMinimalServiceCurve_residualServer_of_isGps hcaus hβ hgps)
    (residualServer_apply hp i) harr hstab

/-- **GPS stability from the rate condition** (Theorem 12.4 form): in a GPS
server with strict aggregate service `β`, flow `i` is globally stable as soon as
its rate stays below its weighted share of the service rate,
`r(αᵢ) < (φᵢ/∑ⱼ φⱼ)·R(β)` — scaling the service curve scales the rate, so the
share's service rate is `(φᵢ/∑ⱼ φⱼ)·R(β)`. -/
theorem isGloballyStableServer_gps_of_rate_lt {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {φ : ι → ℝ≥0} {β αi : ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S) (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hgps : IsGpsServerN φ S)
    {As Ds : ι → Curve} (hp : S As Ds)
    (harr : IsMaximalArrivalBound (⇑(As i)) αi)
    (hrate : longTermArrivalRate αi
      < (φ i / ∑ j, φ j : ℝ≥0) * longTermServiceRate β) :
    IsGloballyStableServer (⇑(As i)) (⇑(Ds i)) := by
  refine isGloballyStableServer_gps hcaus hβ hgps hp harr ?_
  show longTermArrivalRate αi < longTermServiceRate (fun v => (φ i / ∑ j, φ j) * β v)
  rwa [longTermServiceRate_const_mul]

end DeepWiki
