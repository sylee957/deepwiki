import DeepWiki.NetworkCalculus.StabilityGlobal
import DeepWiki.NetworkCalculus.NetworkTopology
import DeepWiki.NetworkCalculus.ArrivalCurvesAggregate

/-! # Network model and network stability
The basics of the network model: a `Network` of flows routed over servers, the
flows `Fl(h)` crossing each server, the aggregate arrival at a server, and the
network-wide local/global stability predicates (Definitions 12.2 / 12.3). The
load-bearing result is **network local ⟹ network global**: the rate-sum
condition `∑_{i∈Fl(h)} rᵢ < R^(h)` bounds (limsup subadditivity) the aggregate
rate below the service rate, so the per-server `local ⟹ global` fires at every
server. (Cross-traffic propagation — deriving the per-server served pair and
aggregate arrival bound from the routing rather than assuming them — is the next
network-model layer and is left as hypotheses here.) -/

namespace DeepWiki

open scoped NNReal ENNReal
open Filter

/-- A **network**: flows `ι` routed over servers `κ` by `paths` (flow `i`
traverses the server list `paths i`), each flow with a source cumulative
process `arrival i` constrained by a maximal arrival curve `arrivalCurve i`,
each server offering a strict minimal service curve `service h`. -/
structure Network (κ ι : Type*) where
  /-- Routing: flow `i` traverses the server list `paths i`. -/
  paths : ι → List κ
  /-- Per-flow source cumulative arrival process at the network ingress. -/
  arrival : ι → Curve
  /-- Per-flow maximal arrival curve `αᵢ` constraining `arrival i`. -/
  arrivalCurve : ι → (ℝ≥0 → ℝ≥0)
  /-- Per-server strict minimal service curve `β^(h)`. -/
  service : κ → (ℝ≥0 → ℝ≥0)

variable {κ ι : Type*} [Fintype ι] [DecidableEq κ]

/-- The flows crossing server `h`: `Fl(h) = { i | h ∈ paths i }` (Definition
12.2). -/
def Network.flowsThrough (net : Network κ ι) (h : κ) : Finset ι :=
  Finset.univ.filter (fun i => h ∈ net.paths i)

/-- Membership in `Fl(h)` is path-crossing. -/
@[simp] theorem Network.mem_flowsThrough {net : Network κ ι} {h : κ} {i : ι} :
    i ∈ net.flowsThrough h ↔ h ∈ net.paths i := by
  simp [Network.flowsThrough]

/-- The aggregate source process at server `h`: the pointwise sum of the
arrivals of the flows crossing `h`, `∑_{i∈Fl(h)} Aᵢ`. -/
noncomputable def Network.aggregateArrival (net : Network κ ι) (h : κ) : Curve :=
  ∑ i ∈ net.flowsThrough h, net.arrival i

/-- The aggregate maximal arrival curve at server `h`: `∑_{i∈Fl(h)} αᵢ`. -/
def Network.aggregateArrivalCurve (net : Network κ ι) (h : κ) : ℝ≥0 → ℝ≥0 :=
  fun t => ∑ i ∈ net.flowsThrough h, net.arrivalCurve i t

/-- The aggregate long-term arrival rate at `h`: `∑_{i∈Fl(h)} rᵢ`. -/
noncomputable def Network.aggregateArrivalRate (net : Network κ ι) (h : κ) : ℝ≥0∞ :=
  ∑ i ∈ net.flowsThrough h, longTermArrivalRate (net.arrivalCurve i)

/-- The long-term service rate at `h`: `R^(h) = liminf_{t→∞} β^(h)(t)/t`. -/
noncomputable def Network.serviceRate (net : Network κ ι) (h : κ) : ℝ≥0∞ :=
  longTermServiceRate (net.service h)

/-- The aggregate process at `h` is `α`-arrival-constrained by the aggregate
arrival curve, given each crossing flow is constrained by its own curve
(`isMaximalArrivalBound_sum`). -/
theorem Network.isMaximalArrivalBound_aggregate (net : Network κ ι) (h : κ)
    (hper : ∀ i ∈ net.flowsThrough h,
      IsMaximalArrivalBound (⇑(net.arrival i)) (net.arrivalCurve i)) :
    IsMaximalArrivalBound (⇑(net.aggregateArrival h)) (net.aggregateArrivalCurve h) := by
  rw [Network.aggregateArrival, Curve.coe_sum]
  exact isMaximalArrivalBound_sum (net.flowsThrough h) hper

/-- The aggregate rate is below the per-flow rate sum (limsup subadditivity):
`r(∑_{i∈Fl(h)} αᵢ) ≤ ∑_{i∈Fl(h)} rᵢ`. -/
theorem Network.longTermArrivalRate_aggregate_le (net : Network κ ι) (h : κ) :
    longTermArrivalRate (net.aggregateArrivalCurve h) ≤ net.aggregateArrivalRate h :=
  longTermArrivalRate_sum_le (net.flowsThrough h) net.arrivalCurve

/-- **Definition 12.2** (network local stability): at every server `h` the
aggregate long-term arrival rate of the flows crossing `h` is strictly below
the server's long-term service rate, `∑_{i∈Fl(h)} rᵢ < R^(h)`. -/
def Network.IsLocallyStable (net : Network κ ι) : Prop :=
  ∀ h : κ, net.aggregateArrivalRate h < net.serviceRate h

/-- **Definition 12.3** (network global stability): for every server `h`, given
its aggregate departure `departure h`, the aggregate backlogged period is
bounded (`IsGloballyStableServer`). -/
def Network.IsGloballyStable (net : Network κ ι) (departure : κ → Curve) : Prop :=
  ∀ h : κ, IsGloballyStableServer ⇑(net.aggregateArrival h) ⇑(departure h)

/-- Network local stability bounds each server's *aggregate* rate below its
service rate: `r(∑ αᵢ) ≤ ∑ rᵢ < R^(h)` (subadditivity + the rate-sum bound). -/
theorem Network.aggregateRate_lt_serviceRate (net : Network κ ι)
    (hstab : net.IsLocallyStable) (h : κ) :
    longTermArrivalRate (net.aggregateArrivalCurve h) < net.serviceRate h :=
  lt_of_le_of_lt (net.longTermArrivalRate_aggregate_le h) (hstab h)

/-- Network local stability gives each server's aggregate the per-server local
stability `IsLocallyStableServer (∑ αᵢ) β^(h)`. -/
theorem Network.isLocallyStableServer_of_isLocallyStable (net : Network κ ι)
    (hstab : net.IsLocallyStable) (h : κ) :
    IsLocallyStableServer (net.aggregateArrivalCurve h) (net.service h) :=
  net.aggregateRate_lt_serviceRate hstab h

/-- **Network local stability ⟹ network global stability** (Definition 12.2 ⟹
Definition 12.3). With, at every server `h`, a causal relation `S h` offering
strict minimal service `service h`, carrying the aggregate served pair
`(aggregateArrival h, departure h)` whose aggregate arrival is constrained by
the aggregate arrival curve, network local stability bounds every backlogged
period. Per server the rate-sum bound gives `IsLocallyStableServer` of the
aggregate, then the per-server `local ⟹ global` fires. -/
theorem Network.isGloballyStable_of_isLocallyStable (net : Network κ ι)
    (S : κ → (Curve → Curve → Prop)) (departure : κ → Curve)
    (hc : ∀ h, IsCausal (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (net.service h) (S h))
    (hp : ∀ h, S h (net.aggregateArrival h) (departure h))
    (harr : ∀ h, IsMaximalArrivalBound (⇑(net.aggregateArrival h))
      (net.aggregateArrivalCurve h))
    (hstab : net.IsLocallyStable) :
    net.IsGloballyStable departure := fun h =>
  isGloballyStableServer_of_isLocallyStableServer (hc h) (hβ h) (hp h) (harr h)
    (net.isLocallyStableServer_of_isLocallyStable hstab h)

/-! ## Network topology classes (Definition 10.1)
The modular-analysis topology classes of `NetworkTopology`, read off a
network's routing `paths`. -/

/-- A network is **feed-forward** when its routing admits an acyclic server
ranking — every flow path strictly increases in rank (`IsFeedForward`). -/
def Network.IsFeedForward (net : Network κ ι) (rank : κ → ℕ) : Prop :=
  _root_.DeepWiki.IsFeedForward rank net.paths

/-- A network is a **nested tandem** when its flow paths are totally ordered by
contiguous-subpath inclusion (the (Nest) condition, `IsNestedTandem`). -/
def Network.IsNestedTandem (net : Network κ ι) : Prop :=
  _root_.DeepWiki.IsNestedTandem net.paths

/-- A network is a **tandem** along `line` when every flow path is a contiguous
subpath of `line` (`IsTandemNetwork`). -/
def Network.IsTandem (net : Network κ ι) (line : List κ) : Prop :=
  _root_.DeepWiki.IsTandemNetwork line net.paths

omit [Fintype ι] [DecidableEq κ] in
/-- A single-flow network is trivially a nested tandem. -/
theorem Network.isNestedTandem_of_subsingleton [Subsingleton ι]
    (net : Network κ ι) : net.IsNestedTandem :=
  _root_.DeepWiki.isNestedTandem_of_subsingleton net.paths

end DeepWiki
