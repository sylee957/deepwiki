import DeepWiki.NetworkCalculus.StabilityNetwork
import DeepWiki.NetworkCalculus.ServersMimo
import DeepWiki.NetworkCalculus.ArrivalCurvesOutputChain

/-! # Per-flow trajectory wiring for network stability
The MIMO multiplexing layer that *derives* the aggregate served pair (the `hp`
hypothesis of `Network.isGloballyStable_of_isLocallyStable`) from genuine
per-flow data, rather than assuming it. A server multiplexes a *vector* of
per-flow processes (`S : (ι → Curve) → (ι → Curve) → Prop`, `ServersMimo`); its
aggregate server carries the summed input to the summed output
(`aggregateServer_sum`) and is causal (`isCausal_aggregateServer`). So once a
server offers a strict service curve to its aggregate and the aggregate is
locally stable, it is globally stable — the served pair and causality are read
off the multiplexing, not posited.

(The remaining piece — *deriving* the per-hop aggregate arrival bound `harr` by
propagating each flow's ingress curve along its path, via the
`ArrivalCurvesOutputChain` engine summed over the flows at a server — is
topological for feed-forward networks and the fix-point for cyclic ones; it is
left as a hypothesis here, with the propagation engine already in place.) -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **MIMO aggregate global stability** (the multiplexing ⟹ aggregate bridge):
a per-flow-causal `n`-server `S` whose aggregate offers a strict service curve
`β`, carrying the per-flow pair `(As, Ds)`, with the aggregate input
`∑ᵢ Asᵢ` arrival-constrained by `αagg` and locally stable against `β`, has a
globally stable aggregate. The aggregate served pair (`aggregateServer_sum`) and
its causality (`isCausal_aggregateServer`) are *derived* from the per-flow
multiplexing; only the arrival bound and rate condition remain. -/
theorem isGloballyStableServer_aggregateServer {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β αagg : ℝ≥0 → ℝ≥0}
    (hc : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds)
    (harr : IsMaximalArrivalBound (⇑(∑ i, As i)) αagg)
    (hstab : IsLocallyStableServer αagg β) :
    IsGloballyStableServer ⇑(∑ i, As i) ⇑(∑ i, Ds i) :=
  isGloballyStableServer_of_isLocallyStableServer
    (isCausal_aggregateServer hc) hβ (aggregateServer_sum hp) harr hstab

/-- **Rate conservation**: a causal server's output never has a larger
long-term rate than its input (`D ≤ A`, so `r(D) ≤ r(A)`). The rate does not
grow through a server. -/
theorem longTermArrivalRate_departure_le {S : Curve → Curve → Prop}
    (hc : IsCausal S) {A D : Curve} (hp : S A D) :
    longTermArrivalRate ⇑D ≤ longTermArrivalRate ⇑A :=
  longTermArrivalRate_mono fun t => hc A D hp t

/-- **Local stability is inherited downstream**: since the rate does not grow
through a causal server, an input locally stable against `β` has an output
whose rate is still below `β`'s service rate — the feed-forward reason a
source-level rate condition suffices at every downstream server. -/
theorem longTermArrivalRate_departure_lt_serviceRate {S : Curve → Curve → Prop}
    {β : ℝ≥0 → ℝ≥0} (hc : IsCausal S) {A D : Curve} (hp : S A D)
    (hstab : IsLocallyStableServer (⇑A) β) :
    longTermArrivalRate ⇑D < longTermServiceRate β :=
  lt_of_le_of_lt (longTermArrivalRate_departure_le hc hp) hstab

variable {κ ι : Type*} [Fintype ι] [DecidableEq κ]

/-- **Network global stability from per-hop MIMO servers** (Definition 12.2 ⟹
Definition 12.3, multiplexing form). Each server `h` is a per-flow-causal MIMO
server `S h` whose aggregate offers the strict service curve `net.service h`,
carrying the actual per-flow input/output vectors `Ain h`/`Dout h`. Given the
per-hop aggregate input is constrained by `aggregateArrivalCurve h` and the
network is locally stable, every server's aggregate is globally stable. The
served pair and causality at each server are derived from the multiplexing
(`isGloballyStableServer_aggregateServer`); only the per-hop arrival bound
`harr` is assumed — that is what the arrival-curve propagation engine
(`isMaximalArrivalBound_concatComp_output` summed over `flowsThrough h`)
discharges from the routing in the feed-forward case. -/
theorem Network.isGloballyStable_mimo (net : Network κ ι)
    (S : κ → (ι → Curve) → (ι → Curve) → Prop)
    (Ain Dout : κ → ι → Curve)
    (hc : ∀ h, IsCausalN (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (net.service h) (aggregateServer (S h)))
    (hp : ∀ h, S h (Ain h) (Dout h))
    (harr : ∀ h, IsMaximalArrivalBound (⇑(∑ i, Ain h i)) (net.aggregateArrivalCurve h))
    (hstab : net.IsLocallyStable) :
    ∀ h, IsGloballyStableServer ⇑(∑ i, Ain h i) ⇑(∑ i, Dout h i) := fun h =>
  isGloballyStableServer_aggregateServer (hc h) (hβ h) (hp h) (harr h)
    (net.isLocallyStableServer_of_isLocallyStable hstab h)

/-! ## Book restatement (multiplexing ⟹ aggregate global stability)
A server multiplexing flows `As` to `Ds` (`n`-server `S`), offering a strict
service curve `β` to the aggregate, with the aggregate input
`α`-arrival-constrained and locally stable, has a bounded aggregate backlogged
period — its served pair and causality coming from the multiplexing model. -/
example {ι : Type*} [Fintype ι] {S : (ι → Curve) → (ι → Curve) → Prop}
    {β α : ℝ≥0 → ℝ≥0} (hc : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds)
    (harr : IsMaximalArrivalBound (⇑(∑ i, As i)) α)
    (hstab : IsLocallyStableServer α β) :
    IsGloballyStableServer ⇑(∑ i, As i) ⇑(∑ i, Ds i) :=
  isGloballyStableServer_aggregateServer hc hβ hp harr hstab

end DeepWiki
