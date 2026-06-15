import DeepWiki.NetworkCalculus.Stability
import DeepWiki.NetworkCalculus.StabilityGlobal
import DeepWiki.NetworkCalculus.StabilityFixPoint
import DeepWiki.NetworkCalculus.StabilityNetwork
import DeepWiki.NetworkCalculus.StabilityNetworkTrajectory
import DeepWiki.NetworkCalculus.StabilityResidualRate
import DeepWiki.NetworkCalculus.ArrivalCurvesOutputChain
import DeepWiki.NetworkCalculus.RealCurvesRates
import DeepWiki.NetworkCalculus.StabilityNetworkInstance
import DeepWiki.NetworkCalculus.StabilityNetworkPriority
import DeepWiki.NetworkCalculus.StabilityNetworkGps
import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstant
import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstantTandem
import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstantGeneral
import DeepWiki.NetworkCalculus.StabilityNetworkPriorityConstantTandem
import DeepWiki.NetworkCalculus.StabilityNetworkPriorityConstantGeneral
import DeepWiki.NetworkCalculus.StabilityNetworkPriorityConstantEndToEnd
import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstantEndToEnd
import DeepWiki.NetworkCalculus.StabilityNetworkScheduler
import Sources.Dnc.Source

/-! # DNC catalog — Chapter 12: Stability in Networks with Cyclic Dependencies
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-- **Definition 12.1** (§12.1.1, p.270): long-term rates — the arrival rate
`limsup_{t→∞} α(t)/t` (`longTermArrivalRate`) and the service rate
`liminf_{t→∞} β(t)/t` (`longTermServiceRate`). -/
noncomputable def def_12_1_arrivalRate := @longTermArrivalRate

/-- **Definition 12.1** (§12.1.1, p.270): the long-term service rate
`liminf_{t→∞} β(t)/t`. -/
noncomputable def def_12_1_serviceRate := @longTermServiceRate

/-- **Definition 12.2** (§12.1.1, p.271): local stability (per-server form) —
a server is locally stable when the aggregate long-term arrival rate is
strictly below its long-term service rate, `∑ rᵢ < R`. The library's
`IsLocallyStableServer`. (The whole-network form quantifying over every server
is `def_12_2_network` below.) -/
abbrev def_12_2 := @IsLocallyStableServer

/-- **Lemma 12.1** (§12.1.1, p.271): if a server is locally stable then
`ℓmax(α, β) < ∞`, i.e. its first crossing — equivalently (Theorem 5.5) the
maximal length of its backlogged period — is finite. The library's
`firstCrossing_lt_top_of_isLocallyStableServer`. -/
theorem lemma_12_1 {α β : ℝ≥0 → ℝ≥0} (h : IsLocallyStableServer α β) :
    firstCrossing α β < ⊤ :=
  firstCrossing_lt_top_of_isLocallyStableServer h

/-- **Definition 12.3** (§12.1.2, p.271): global stability (per-server form) —
a server is globally stable when its maximal backlogged-period length is
bounded, `maxBackloggedLength A D < ⊤`. The library's `IsGloballyStableServer`.
(The whole-network form is `def_12_3_network` below.) -/
abbrev def_12_3 := @IsGloballyStableServer

/-- **Definition 12.2** (network form, §12.1.1 p.271): a network is locally
stable when at every server `h` the aggregate arrival rate of the crossing
flows is below the service rate, `∀ h, ∑_{i∈Fl(h)} rᵢ < R^(h)`. The library's
`Network.IsLocallyStable`. -/
abbrev def_12_2_network := @Network.IsLocallyStable

/-- **Definition 12.3** (network form, §12.1.2 p.271): a network is globally
stable when every server's aggregate backlogged period is bounded. The
library's `Network.IsGloballyStable`. -/
abbrev def_12_3_network := @Network.IsGloballyStable

/-- **Network local ⟹ global** (Definition 12.2 ⟹ Definition 12.3): under a
causal strict-service relation and an aggregate arrival bound at each server,
network local stability bounds every server's backlogged period. The library's
`Network.isGloballyStable_of_isLocallyStable` — the rate-sum condition bounds
(limsup subadditivity) each aggregate rate below the service rate, then the
per-server `local ⟹ global` fires at every server. (Deriving the per-server
served pair and aggregate arrival bound by cross-traffic propagation, rather
than assuming them, is the remaining network-model step.) -/
alias thm_12_localGlobal := Network.isGloballyStable_of_isLocallyStable

/-! **Lemma 12.2** (§12.1.2, p.271): If a network is globally stable then it is locally stable. (Converse direction — not formalized in the library.) -/

/-! **Lemma 12.3** (§12.1.2, p.272): If for a network with token-bucket arrival and rate-latency service curves respecting the local stability conditions the network is globally stable, then local stability for any arrival and service curve is also a sufficient condition for global stability. Not formalized in the library. -/

/-- **Lemma 12.4** (§12.1.2, p.272), per-server form: if a server's arrival is
maximal-arrival-curve constrained and `ℓmax(α, β) = firstCrossing α β < ∞`,
then the server is globally stable (its backlogged period is bounded by the
first crossing, Theorem 5.5). The library's
`isGloballyStableServer_of_firstCrossing_lt_top`. Chaining it with Lemma 12.1
gives the local ⟹ global per-server implication
(`isGloballyStableServer_of_isLocallyStableServer`). (The network statement
quantifies over all servers; not formalized.) -/
theorem lemma_12_4 {S : Curve → Curve → Prop} {β α : ℝ≥0 → ℝ≥0}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve β S)
    {A D : Curve} (hp : S A D) (harr : IsMaximalArrivalBound (⇑A) α)
    (hfin : firstCrossing α β < ⊤) :
    IsGloballyStableServer ⇑A ⇑D :=
  isGloballyStableServer_of_firstCrossing_lt_top hc hβ hp harr hfin

/-! **Example 12.1** (§12.2.1, p.273): The example network of Figure 12.1 (top) is transformed by removing arc h'={(4,2),(2,1)} into an acyclic feed-forward network N^FF; flows splitting into sub-flows (i,k). The concrete Figure-12.1 transformation is not formalized; its engine — feed-forward propagation of arrival curves along a server path — is `arrivalProp_chain` below. -/

/-- **Feed-forward arrival-curve propagation** (the §12.2 engine): a flow
crossing a chain of causal strict-service servers carries its ingress maximal
arrival curve to the chain's output, deconvolved by each server in turn
(`αu ⊘ β₁ ⊘ ⋯ ⊘ βₙ`). The library's `isMaximalArrivalBound_concatComp_output`.
This is how an ingress constraint becomes a constraint at every downstream
server in a feed-forward network. -/
alias arrivalProp_chain := isMaximalArrivalBound_concatComp_output

/-- **Two-server tandem propagation** (the atomic step of `arrivalProp_chain`):
output of the first strict-service server is input of the second, so the
ingress curve `αu` emerges as `(αu ⊘ β₁) ⊘ β₂`. The library's
`isMaximalArrivalBound_tandem_output`. -/
alias arrivalProp_tandem := isMaximalArrivalBound_tandem_output

/-- **Multiplexing ⟹ aggregate global stability** (the per-flow trajectory
wiring): a server multiplexing a vector of flows, offering a strict service
curve to its aggregate, with a locally stable arrival-constrained aggregate, is
globally stable — its served pair and causality *derived* from the MIMO
multiplexing model (`aggregateServer`/`isCausal_aggregateServer`), not assumed.
The library's `isGloballyStableServer_aggregateServer`; the network-wide form is
`Network.isGloballyStable_mimo`. (Deriving the per-hop arrival bound itself by
arrival-curve propagation along each flow's path — `arrivalProp_chain` summed
over a server's flows — is the remaining topological/fix-point step.) -/
alias thm_12_mimoStable := isGloballyStableServer_aggregateServer

/-- **Two-server feed-forward global stability** (single flow, downstream bound
*derived*): a flow crossing two causal strict-service servers in series is
globally stable at *both*, with the second server's arrival bound obtained from
the first's output by propagation (`α ⊘ β₁`, read back through the `liftENN`
carrier bridge) rather than assumed. The library's `isGloballyStable_tandem`.
This is the harr-discharge for the tandem case — the engine behind the §12.2
feed-forward transformation (Example 12.1) at two hops. -/
alias thm_12_tandemStable := isGloballyStable_tandem

/-- **Single-flow feed-forward path global stability** (every hop's bound
derived): a flow crossing any number of causal strict-service servers in series
is globally stable at *every* server on its path, with each hop's arrival bound
obtained by propagating the ingress curve along the prefix (the induction
invariant), not assumed. The library's `isGloballyStable_path` — the n-hop
generalization of `thm_12_tandemStable` and the per-flow feed-forward engine of
§12.2. -/
alias thm_12_pathStable := isGloballyStable_path

/-- **Per-flow global stability under blind (arbitrary) multiplexing**: in an
`n`-server with strict aggregate service `βf`, a flow whose cross-traffic
departures are `αcross`-constrained sees the residual service curve
`βf ⊖ αcross` (`residualCurve`); if locally stable against it, the flow is
globally stable. The library's `isGloballyStableServer_residual` — the
residual-service stability the SFA cross-traffic analysis composes along a path.
(Deriving `αcross` by propagating the other flows' curves is the topological /
fix-point step.) -/
alias thm_12_residualStable := isGloballyStableServer_residual

/-- **Separated-flow per-flow path stability** (multi-flow, multi-server, with
cross-traffic): a flow crossing a chain of `n`-servers, each with strict
aggregate service and `αcross`-constrained cross-traffic at that hop, sees the
residual service curve at every hop and is globally stable at *all* of them —
the SFA combination of `thm_12_pathStable` (multi-hop propagation) with
`thm_12_residualStable` (blind-multiplexing residual). The library's
`isGloballyStable_residualPath`; only the cross-traffic bounds `αcross k`
(computed by the SFA topological pass over the other flows) are parameters. -/
alias thm_12_sfaPathStable := isGloballyStable_residualPath

/-- **Residual local stability from the rate sum** (the §12.2 SFA `hstab`,
*derived* not assumed): under blind multiplexing the residual service rate
survives subtracting the cross-traffic rate (`R(β) ≤ r(α) + R(β⊖α)`,
`longTermServiceRate_residualCurve_ge`), so a flow with
`r(αi) + r(αcross) < R(β)` is locally stable against its residual. The library's
`isLocallyStableServer_residualCurve_of_rate_lt` — this turns `αcross` from a
free curve parameter into a quantity whose *rate* alone drives stability (its
rate bounded, in turn, by the cross-flows' source rates via causal-output
conservation). -/
alias prop_12_residualLocalStable := isLocallyStableServer_residualCurve_of_rate_lt

/-- **Long-term rates of the canonical curves** (§12.1.1 worked rates): the rate
curve `λ_R = R·t` has both arrival and service rate `R`; the rate-latency
service curve `β_{R,T} = R·(t − T)` has service rate `R` (latency washes out);
the affine token-bucket arrival curve `γ_{r,b} = r·t + b` has arrival rate `r`
(burst washes out). The library's `longTermServiceRate_rate`,
`longTermServiceRate_rateLatency`, `longTermArrivalRate_affine`. -/
theorem prop_12_canonicalRates (R T r b : ℝ≥0) :
    longTermServiceRate (rate R) = (R : ℝ≥0∞)
      ∧ longTermServiceRate (rateLatency R T) = (R : ℝ≥0∞)
      ∧ longTermArrivalRate (fun t => r * t + b) = (r : ℝ≥0∞) :=
  ⟨longTermServiceRate_rate R, longTermServiceRate_rateLatency R T, longTermArrivalRate_affine r b⟩

/-- **Worked instance** (§12.1 on the canonical curves): two token-bucket flows
`γ_{r₁,b₁}`, `γ_{r₂,b₂}` sharing a rate-latency server `β_{R,T}` under blind
multiplexing — with `r₁ + r₂ < R`, a flow is locally stable against its residual.
The single rate inequality discharges every hypothesis (closed-form rates +
residual-rate bound). The library's `isLocallyStableServer_tokenBucket_rateLatency`. -/
alias example_12_tokenBucketRateLatency := isLocallyStableServer_tokenBucket_rateLatency

/-- **Theorem 12.1** (§12.2.3, p.275), fix-point sufficient condition — the
Knaster–Tarski kernel: for a monotone propagation operator `F`, the candidate
assignment `α̂ = sSup {α | α ≤ F α}` (`canonicalArrivalAssignment`) is a fixed
point of `F` and the greatest consistent (post-fixed) assignment. The library's
`map_canonicalArrivalAssignment` + `isGreatest_canonicalArrivalAssignment`.
(That a *finite* `α̂` then makes the network globally stable and gives each flow
`(i,k)` an arrival curve at its first server is the network-model
instantiation, which builds on this kernel and is not formalized.) -/
theorem thm_12_1 {V : Type*} [CompleteLattice V] (F : V →o V) :
    F (canonicalArrivalAssignment F) = canonicalArrivalAssignment F ∧
      IsGreatest {α | α ≤ F α} (canonicalArrivalAssignment F) :=
  ⟨map_canonicalArrivalAssignment F, isGreatest_canonicalArrivalAssignment F⟩

/-- **Theorem 12.2** (§12.3.1, p.276), per-flow sufficient direction: under a
preemptive static-priority policy with (monotone, left-continuous) strict
aggregate service `β`, flow `i` is globally stable as soon as its rate plus the
higher-priority rates stays below the service rate, `r(αᵢ) + ∑_{j<i} r(αⱼ) < R(β)`
— the local-stability condition for `i`. Flow `i` sees the residual
`β ⊖ ∑_{j<i} αⱼ` and the residual-rate bound discharges its local stability. The
library's `isGloballyStableServer_staticPriority_of_rate_lt`. (The network-wide
"stable ⟺ locally stable" with the full priority order quantifies this over all
flows; that quantification is not formalized.) -/
alias thm_12_2 := isGloballyStableServer_staticPriority_of_rate_lt

/-! **Example 12.2** (§12.3.2, p.278): For the Figure 12.1 network under FDF: in server 3 flow 1 has highest priority, then flow 2; flows 2 and 3 share the same priority; in server 2 flows 4 and 3 are highest and flow 1 lowest. Not formalized in the library. -/

/-- **Theorem 12.3** (§12.3.2, p.278), shared-path tandem: under a preemptive static-priority
policy a locally stable shared-path tandem is globally stable at every hop. All flows
(priority-ordered) traverse the same line of SP rate-latency servers, each a token bucket at
ingress, with total local stability `∑ⱼ rⱼ < R^(h)`. The library's
`SpTandem.isGloballyStable_sharedPath_tandem` — the static-priority analogue of `thm_12_5_tandem`,
proved by inducting on the priority order (the strictly-higher-priority flows are bounded first,
feeding flow `i`'s SP residual `β_{R − ∑_{j<i} rⱼ, ·}`), then aggregating. A corollary-in-spirit of
the general `thm_12_3` below (the variable-per-server-population network). -/
alias thm_12_3_tandem := SpTandem.isGloballyStable_sharedPath_tandem

/-- **Theorem 12.3** (§12.3.2, p.278), the general theorem: under a preemptive static-priority
policy a locally stable network is globally stable at every server — arbitrary per-flow routing
`net.paths i : List κ`, variable per-server populations `net.flowsThrough h`, flows priority-ordered
by `<`, each server a strict rate-latency aggregate, each flow a token bucket at ingress, local
stability `∑_{Fl h} rⱼ < R^(h)`. The library's `SpNetwork.Traj.isGloballyStable` — the
static-priority analogue of the GPS general `thm_12_5`, proved by well-founded induction on the
priority order (the strictly-higher-priority crossing flows `{j<i} ∩ Fl(h)` bounded first, feeding
flow `i`'s per-hop SP residual along its list path), then aggregating via
`Network.isGloballyStable_of_perFlow_bounds`. FDF is this at the topology-derived
(remaining-distance) priority order. -/
alias thm_12_3 := SpNetwork.Traj.isGloballyStable

/-- **Theorem 12.3, per-flow form** (library strengthening): in a locally stable static-priority
network *each individual flow* `i` has a bounded backlogged period at every server it crosses — not
merely the per-server aggregate. Flow `i` sees the SP residual `β_{R^(h) − ∑_{j<i, j∈Fl h} rⱼ, ·}`
and is locally stable against it (`∑_{j≤i, j∈Fl h} rⱼ ≤ ∑_{Fl h} rⱼ < R^(h)`). The library's
`SpNetwork.Traj.isFlowGloballyStable`. -/
alias thm_12_3_perFlow := SpNetwork.Traj.isFlowGloballyStable

/-- **Lemma 12.5** (§12.3.3, p.279): GPS with fixed parameters — under aggregate
local stability `∑_{j∈Fl(h)} rⱼ < R^(h)` at every server, there is a flow `i` (the
one minimizing `rⱼ/φⱼ`) below its GPS share at every server it crosses,
`rᵢ < φᵢ·R^(h)/(∑_{j∈Fl(h)} φⱼ)`. This is the flow peeled off in the induction for
Theorem 12.5 (local ⟹ global stability under GPS). The combinatorial core, abstract
over flows/servers; the library's `exists_flow_below_gps_share`. (The full Theorem
12.5 network induction is formalized — `thm_12_5` below.) -/
theorem lemma_12_5 {ι σ : Type*} [Fintype ι] [Nonempty ι]
    (r φ : ι → ℝ) (hφ : ∀ j, 0 < φ j) (R : σ → ℝ) (Fl : σ → Finset ι)
    (hstab : ∀ h, ∑ j ∈ Fl h, r j < R h) :
    ∃ i, ∀ h, i ∈ Fl h → r i < φ i * R h / (∑ j ∈ Fl h, φ j) :=
  exists_flow_below_gps_share r φ hφ R Fl hstab

/-- **Theorem 12.5**, the induction step's residual-capacity form (§12.3.3, p.279–280):
on the active (not-yet-peeled) flow set `J`, local stability gives a flow `i ∈ J` below its
GPS share of the *residual* capacity `R^(h) − ∑_{j∈Fl(h)\J} rⱼ` left after the already-peeled
flows are removed — `rᵢ < φᵢ·(R^(h)−∑_{Fl(h)\J}r)/(∑_{Fl(h)∩J}φ)` at each server it crosses.
Peeling the lighter flows shrinks the share denominator and raises the capacity, so the
next-critical flow is again below its (now larger) share. The library's
`exists_flow_below_residual_share` (`lemma_12_5` is the `J = univ`, no-peeled-flows case). -/
theorem lemma_12_5_residual {ι σ : Type*} [DecidableEq ι]
    (J : Finset ι) (hJ : J.Nonempty) (r φ : ι → ℝ) (hφ : ∀ j, 0 < φ j)
    (R : σ → ℝ) (Fl : σ → Finset ι) (hstab : ∀ h, ∑ j ∈ Fl h, r j < R h) :
    ∃ i ∈ J, ∀ h, i ∈ Fl h ∩ J →
      r i < φ i * (R h - ∑ j ∈ Fl h \ J, r j) / (∑ j ∈ Fl h ∩ J, φ j) :=
  exists_flow_below_residual_share J hJ r φ hφ R Fl hstab

/-- **Theorem 12.5**, step B / per-flow path stability (§12.3.3, p.279): the GPS
analogue of the residual-path stability — a flow `i` crossing a path of GPS servers
(shared weights `φ`, strict aggregate service per hop), each offering it the share
`(φᵢ/∑ⱼφⱼ)·βf`, is globally stable at *every* server on its path once its propagated
arrival curve is locally stable against that share at each hop. The library's
`isGloballyStable_gpsPath`. (This is the peeled critical flow's stability — the
per-flow induction body; the full cyclic induction over the network, with the
variable-per-server flow population, is assembled in `thm_12_5`.) -/
theorem thm_12_5_gpsPath {ι : Type*} [Fintype ι] {n : ℕ}
    {Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop} {βf : ℕ → ℝ≥0 → ℝ≥0} {φ : ι → ℝ≥0} {i : ι}
    (hcaus : ∀ k, IsCausalN (Sf k))
    (hβf : ∀ k, IsStrictMinimalServiceCurve (βf k) (aggregateServer (Sf k)))
    (hgps : ∀ k, IsGpsServerN φ (Sf k))
    (proc : ℕ → Curve) (αs : ℕ → ℝ≥0 → ℝ≥0)
    (hchain : ∀ k, k < n → residualServer (Sf k) i (proc k) (proc (k + 1)))
    (harr0 : IsMaximalArrivalBound (⇑(proc 0)) (αs 0))
    (hprop : ∀ k, k < n → minDeconv (Deviation.liftENN (αs k))
      (Deviation.liftENN (fun v => (φ i / ∑ j, φ j) * βf k v)) ≤ Deviation.liftENN (αs (k + 1)))
    (hstab : ∀ k, k < n → IsLocallyStableServer (αs k) (fun v => (φ i / ∑ j, φ j) * βf k v)) :
    ∀ k, k < n → IsGloballyStableServer (⇑(proc k)) (⇑(proc (k + 1))) :=
  isGloballyStable_gpsPath hcaus hβf hgps proc αs hchain harr0 hprop hstab

/-- **Theorem 12.5**, critical-flow path stability in the book setting (§12.3.3,
p.279): a token-bucket flow `γ_{r,b}` crossing a path of GPS servers with
rate-latency aggregate service `β_{Rₖ,Tₖ}` (shared weights `φ`) is globally stable
at *every* server on its path, from local stability alone (`r < (φᵢ/∑ⱼφⱼ)·Rₖ`). The
per-hop propagation is closed-form (burst `+r·∑Tⱼ`), so no extra hypotheses beyond
local stability. The library's `isGloballyStable_gpsPath_tokenBucket` — the
substantive per-flow content of Theorem 12.5 (the cyclic peeling assembly over the
whole network is `thm_12_5`). -/
theorem thm_12_5_gpsPath_tokenBucket {ι : Type*} [Fintype ι] {n : ℕ}
    {Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop} {φ : ι → ℝ≥0} {i : ι} {r b : ℝ≥0}
    {R T : ℕ → ℝ≥0} (hcaus : ∀ k, IsCausalN (Sf k))
    (hβf : ∀ k, IsStrictMinimalServiceCurve (rateLatency (R k) (T k)) (aggregateServer (Sf k)))
    (hgps : ∀ k, IsGpsServerN φ (Sf k)) (proc : ℕ → Curve)
    (hchain : ∀ k, k < n → residualServer (Sf k) i (proc k) (proc (k + 1)))
    (harr0 : IsMaximalArrivalBound (⇑(proc 0)) (fun t => r * t + b))
    (hr : ∀ k, k < n → r ≤ (φ i / ∑ j, φ j) * R k)
    (hstab : ∀ k, k < n → r < (φ i / ∑ j, φ j) * R k) :
    ∀ k, k < n → IsGloballyStableServer (⇑(proc k)) (⇑(proc (k + 1))) :=
  isGloballyStable_gpsPath_tokenBucket hcaus hβf hgps proc hchain harr0 hr hstab

/-- **Theorem 12.5**, the per-server peeling step (§12.3.3, p.279–280): at a GPS server with
strict rate-latency aggregate `β_{R,T}` and weights `φ`, once the already-peeled flows
`∑_{j∉J} Dⱼ` carry a token-bucket bound `ρ·v+b` (`ρ` their summed rate, `ρ < R`), the
not-yet-peeled critical flow `i ∈ J` is served by the rate-latency strict service curve
`β_{(φᵢ/∑_{j∈J}φ)(R−ρ), (R·T+b)/(R−ρ)}` — the blind residual leaves the `J`-aggregate the
reduced rate `R−ρ` (`residualCurve β_{R,T} (ρ·v+b) = β_{R−ρ,·}`), and the GPS share carves
flow `i`'s slice. The library's `isStrictMinimalServiceCurve_residualServer_gpsPeel`; its
rate exceeds `rᵢ` by `lemma_12_5_residual`. This is the induction step at one server; the
whole-network cyclic induction is assembled in `thm_12_5`. -/
alias thm_12_5_peelStep := isStrictMinimalServiceCurve_residualServer_gpsPeel

/-- **Theorem 12.5**, the network-level theorem for the shared-path tandem (§12.3.3,
p.279–280): a locally stable GPS-constant tandem in which every flow traverses the *same*
line of `m` GPS rate-latency servers (shared weights `φ`, token-bucket ingress) is globally
stable at every hop — the aggregate input/output at each server has a bounded backlogged
period. The whole cyclic-peeling proof: peel flows in increasing `rⱼ/φⱼ` order, the
active-set critical flow being below its GPS share of the residual capacity
(`exists_flow_below_residual_share`) hence stable + token-bucket bounded along the line (the
per-flow induction body `isMaximalArrivalBound_gpsPeelPath_tokenBucket`), recurse, then
aggregate (`Network.isGloballyStable_of_perFlow_bounds`). The only hypothesis beyond the GPS
structure is aggregate local stability `∑ᵢ rᵢ < R^(h)`. The library's
`GpsTandem.isGloballyStable_sharedPath_tandem` — a *fully derived* (no assumed per-flow bound)
network-level instance of Theorem 12.5, a corollary of the general `thm_12_5` (arbitrary
variable-per-server-population routing) specialized to the shared-path line. -/
alias thm_12_5_tandem := GpsTandem.isGloballyStable_sharedPath_tandem

/-- **Theorem 12.5** (§12.3.3, p.279–280), the full general theorem: a locally stable
GPS-constant network — arbitrary per-flow routing `net.paths i : List κ`, variable
per-server populations `net.flowsThrough h`, each server offering a strict rate-latency
aggregate `β_{R h, T h}` to its GPS relation (shared weights `φ`), each flow a token bucket
at ingress — is globally stable at every server: the aggregate input/output has a bounded
backlogged period. The whole cyclic-peeling proof, end to end and fully derived (nothing
assumed beyond the GPS-network trajectory + aggregate local stability `∑_{Fl h} rⱼ < R^(h)`):
peel flows in increasing `rⱼ/φⱼ` order (`exists_flow_below_residual_share`), the active-set
critical flow being below its GPS share of the residual capacity, hence — by the list-path↔
hop-index `bridge` over the per-flow engine body — token-bucket bounded along its path; the
outer strong induction (`GpsNetwork.Traj.peelInduction`) bounds every flow, and the per-flow
bounds aggregate to local stability against each server, discharging global stability through
`Network.isGloballyStable_of_perFlow_bounds`. The library's `GpsNetwork.Traj.isGloballyStable`
(over the trajectory model `GpsNetwork.Traj` wrapping a `Network`). Subsumes the shared-path
tandem `thm_12_5_tandem`. -/
alias thm_12_5 := GpsNetwork.Traj.isGloballyStable

/-- **Theorem 12.5, per-flow form** (library strengthening): in a locally stable GPS-constant
network *each individual flow* `i` has a bounded backlogged period at every server it crosses — not
merely the per-server aggregate. Flow `i` is `r/φ`-minimal in the active set `J = {j : rᵢφⱼ ≤ rⱼφᵢ}`,
so the GPS peel step leaves it the residual `β_{(φᵢ/∑_{Fl h∩J}φ)(R^(h) − ∑_{Fl h\J}r), ·}` (the
lighter flows already bounded), against which it is locally stable. The library's
`GpsNetwork.Traj.isFlowGloballyStable` — the GPS analogue of `thm_12_3_perFlow`. -/
alias thm_12_5_perFlow := GpsNetwork.Traj.isFlowGloballyStable

/-- **Per-flow delay bounds** (library, quantitative companions of the per-flow stability theorems):
in a locally stable network each flow's virtual delay at a crossed server is finite, bounded by
`T' + B'/R'` of its residual rate-latency service (`flowResidualBound` + the server delay bound
`delay_le_of_strictRateLatency_affine`). The library's `SpNetwork.Traj.isFlowDelayBounded` (static
priority) and `GpsNetwork.Traj.isFlowDelayBounded` (GPS). -/
alias thm_12_3_perFlowDelay := SpNetwork.Traj.isFlowDelayBounded

@[inherit_doc thm_12_3_perFlowDelay]
alias thm_12_5_perFlowDelay := GpsNetwork.Traj.isFlowDelayBounded

/-- **Per-flow backlog bounds** (library, companions of the per-flow delay bounds): in a locally
stable network each flow's backlog at a crossed server is finite, bounded by `rᵢ·T' + B'` of its
residual rate-latency service (`flowResidualBound` + the latency-free server backlog bound
`backlog_le_of_strictRateLatency_affine`). The library's `SpNetwork.Traj.isFlowBacklogBounded`
(static priority) and `GpsNetwork.Traj.isFlowBacklogBounded` (GPS). -/
alias thm_12_3_perFlowBacklog := SpNetwork.Traj.isFlowBacklogBounded

@[inherit_doc thm_12_3_perFlowBacklog]
alias thm_12_5_perFlowBacklog := GpsNetwork.Traj.isFlowBacklogBounded

/-- **Per-flow END-TO-END delay in a stable SP network** (library capstone, unifying Thm 12.3 with
the §10.3.4 SP-PMOO end-to-end analysis): in a locally stable static-priority network, every flow
with a nonempty path has a *finite end-to-end delay* (ingress → egress), via the SP-PMOO end-to-end
rate-latency residual along its path — the per-hop trajectory realizes the `concatComp` chain
(`concatComp_of_chain`), cross-traffic bounds come from `allBound`, stability from `∑_{Fl h}r < R^(h)`.
The library's `SpNetwork.Traj.isFlowEndToEndDelayBounded`. -/
alias thm_12_3_endToEndDelay := SpNetwork.Traj.isFlowEndToEndDelayBounded

/-- **Per-flow END-TO-END delay in a stable GPS network** (library capstone, unifying Thm 12.5 with
the §10.4 SFA end-to-end analysis): in a locally stable GPS-constant network, every flow with a
nonempty path has a *finite end-to-end delay*, via the SFA blind-multiplexing end-to-end bound (which
needs only the strict rate-latency aggregate, so it covers GPS). The library's
`GpsNetwork.Traj.isFlowEndToEndDelayBounded`. -/
alias thm_12_5_endToEndDelay := GpsNetwork.Traj.isFlowEndToEndDelayBounded

/-- **Per-flow END-TO-END backlog in a stable network** (library capstone, backlog parallel of the
end-to-end delay capstones): in a locally stable SP / GPS network, every flow with a nonempty path
has a *finite end-to-end backlog* (ingress to egress), via the SP-PMOO / SFA end-to-end bound. The
library's `SpNetwork.Traj.isFlowEndToEndBacklogBounded` (static priority) and
`GpsNetwork.Traj.isFlowEndToEndBacklogBounded` (GPS). -/
alias thm_12_3_endToEndBacklog := SpNetwork.Traj.isFlowEndToEndBacklogBounded

@[inherit_doc thm_12_3_endToEndBacklog]
alias thm_12_5_endToEndBacklog := GpsNetwork.Traj.isFlowEndToEndBacklogBounded

/-- **Per-flow END-TO-END output burstiness** (library capstone, compositionality): in a locally
stable SP / GPS network, a flow's egress (last-server departure) is again token-bucket bounded — the
stable network preserves token-bucket burstiness, so the flow can feed a downstream network. The
library's `SpNetwork.Traj.isFlowEndToEndOutputBounded` and `GpsNetwork.Traj.isFlowEndToEndOutputBounded`. -/
alias thm_12_3_endToEndOutput := SpNetwork.Traj.isFlowEndToEndOutputBounded

@[inherit_doc thm_12_3_endToEndOutput]
alias thm_12_5_endToEndOutput := GpsNetwork.Traj.isFlowEndToEndOutputBounded

/-- **Theorem 12.4** (§12.3.3, p.279), per-flow sufficient direction: under GPS
with strict aggregate service `β` and weights `φ`, flow `i` is globally stable
as soon as its rate stays below its weighted service share,
`r(αᵢ) < (φᵢ/∑ⱼ φⱼ)·R(β)` — the local-stability condition for `i` (GPS gives
flow `i` the share `(φᵢ/∑ⱼ φⱼ)·β` independent of cross-traffic). The library's
`isGloballyStableServer_gps_of_rate_lt`. (The network-wide statement — quantified
over all flows and servers, with the peeling that handles flows above their raw
share — is `thm_12_5`.) -/
alias thm_12_4 := isGloballyStableServer_gps_of_rate_lt

/-! **Beyond the book's SP/FDF/GPS** (library extension, no separate book number): the
same compose-the-residual argument gives per-flow global stability under the frame/fair
schedulers whose residual service curves are formalized in Chapter 8 — DRR
(`isGloballyStableServer_drr`, via `drrResidual`), WRR (`isGloballyStableServer_wrr`, via
`wrrResidual`), and TDMA (`isGloballyStableServer_tdma`, via `tdmaResidual`): a flow
locally stable against its scheduler residual is globally stable. -/

/-- **Definition 12.4** (§12.4.2, p.284): the scaled flow `m·A` of a
cumulative process `A` with factor `m ∈ ℝ≥0`. The library's `scaledFlow`. -/
def def_12_4 := @scaledFlow

/-- **Lemma 12.6** (§12.4.2, p.284): if `A` is `α`-upper-constrained then
`m·A` is `m·α`-upper-constrained. The library's
`isMaximalArrivalBound_scaledFlow`. -/
alias lemma_12_6 := isMaximalArrivalBound_scaledFlow

/-- **Scaling scales the long-term rate** (§12.4.2): the long-term arrival rate
of the scaled flow `m·A` is `m` times that of `A`. The library's
`longTermArrivalRate_scaledFlow`. -/
alias prop_12_scaledRate := longTermArrivalRate_scaledFlow

/-- **§12.4.2 instability boundary** (p.284–285): the cyclic two-server scaling network's per-flow
burst fix-point `σ₁' = … + (m₂m₄/((1−m₂)(1−m₄)))·σ₁'` has a finite solution iff `m₂ + m₄ < 1` — which
is *strictly stronger* than the local stability `m₁+m₄ < 1 ∧ m₂+m₃ < 1`, so a locally stable scaling
network can have a diverging fix-point (no finite NC bound): local stability is not sufficient for
the cyclic network. The library's `exists_scalingFixpoint_iff` (and the gain boundary
`scaling_gain_lt_one_iff`), resting on the linear fix-point criterion `exists_linearFixpoint_iff`. -/
alias ex_12_scalingInstability := exists_scalingFixpoint_iff

end DeepWiki.Dnc
