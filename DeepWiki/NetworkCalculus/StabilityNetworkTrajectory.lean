import DeepWiki.NetworkCalculus.StabilityNetwork
import DeepWiki.NetworkCalculus.ServersMimo
import DeepWiki.NetworkCalculus.ServersResidual
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

/-- **Per-flow global stability under blind multiplexing** (the residual /
cross-traffic case): in an `n`-server whose aggregate offers a strict service
curve `βf`, flow `i` — with its cross-traffic departures `∑_{j≠i} Dⱼ`
constrained by `αcross` and its own arrival constrained by `αi` — sees the
*residual* service curve `residualCurve βf αcross`. If flow `i` is locally
stable against that residual, it is globally stable. The residual being a strict
service curve (`isStrictMinimalServiceCurve_residualServer`) and the residual
server's causality (`isCausal_residualServer`) are derived; this is the genuine
per-flow stability under arbitrary multiplexing. -/
theorem isGloballyStableServer_residual {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {βf αcross αi : ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve βf (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds)
    (hcross : IsMaximalArrivalBound (fun x => ∑ j ∈ Finset.univ.erase i, (Ds j) x) αcross)
    (harr : IsMaximalArrivalBound (⇑(As i)) αi)
    (hstab : IsLocallyStableServer αi (residualCurve βf αcross)) :
    IsGloballyStableServer (⇑(As i)) (⇑(Ds i)) :=
  have hcaus' : IsCausalN (fun A D => S A D ∧ IsMaximalArrivalBound
      (fun x => ∑ j ∈ Finset.univ.erase i, (D j) x) αcross) :=
    fun A D hAD => hcaus A D hAD.1
  isGloballyStableServer_of_isLocallyStableServer
    (isCausal_residualServer hcaus' i)
    (isStrictMinimalServiceCurve_residualServer hcaus hβ)
    ⟨As, Ds, ⟨hp, hcross⟩, rfl, rfl⟩ harr hstab

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

omit [DecidableEq κ] in
/-- **Network global stability from a per-server aggregate bound** (the
generalization of `isGloballyStable_mimo` decoupled from the ingress-sum
`aggregateArrivalCurve`): given, at each server, an arbitrary aggregate-input
arrival bound `σ h` (the *propagated* bound — possibly burstier than the source sum,
as it must be at internal servers) against which the aggregate is locally stable,
every server's aggregate is globally stable. This is the form the peeling assembly
feeds — `σ h` the sum of the per-flow propagated curves established along their
paths. -/
theorem Network.isGloballyStable_mimo_of_aggregateBound (net : Network κ ι)
    (S : κ → (ι → Curve) → (ι → Curve) → Prop)
    (Ain Dout : κ → ι → Curve) (σ : κ → ℝ≥0 → ℝ≥0)
    (hc : ∀ h, IsCausalN (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (net.service h) (aggregateServer (S h)))
    (hp : ∀ h, S h (Ain h) (Dout h))
    (harr : ∀ h, IsMaximalArrivalBound (⇑(∑ i, Ain h i)) (σ h))
    (hstab : ∀ h, IsLocallyStableServer (σ h) (net.service h)) :
    ∀ h, IsGloballyStableServer ⇑(∑ i, Ain h i) ⇑(∑ i, Dout h i) := fun h =>
  isGloballyStableServer_aggregateServer (hc h) (hβ h) (hp h) (harr h) (hstab h)

/-! ## Two-server feed-forward stability, downstream bound DERIVED
The genuine harr-discharge for a tandem: the second server's arrival bound is
not assumed — it is the first server's output bound, obtained from the
propagation engine and read back to `ℝ≥0` through the `liftENN` carrier bridge
(`isMaximalArrivalBound_liftENN_iff`). -/

open Deviation in
/-- **Two-server feed-forward global stability** (single flow, downstream bound
derived). A flow with ingress maximal arrival curve `α` crosses a causal
strict-service server `S₁` (curve `β₁`) and then `S₂` (curve `β₂`), the output
`M` of the first being the input of the second. If the propagated output bound
`α ⊘ β₁` is dominated by a curve `α₂` (the witness for the derived downstream
constraint) and both servers are locally stable, then **both** servers have a
bounded backlogged period. The downstream arrival bound on `M` is *derived*
(`isMaximalArrivalBound_output_of_isStrictMinimalServiceCurve` + the carrier
bridge), not assumed. -/
theorem isGloballyStable_tandem
    {S₁ S₂ : Curve → Curve → Prop} {β₁ β₂ α α₂ : ℝ≥0 → ℝ≥0}
    (hc₁ : IsCausal S₁) (hβ₁ : IsStrictMinimalServiceCurve β₁ S₁)
    (hc₂ : IsCausal S₂) (hβ₂ : IsStrictMinimalServiceCurve β₂ S₂)
    {A M D : Curve} (hp₁ : S₁ A M) (hp₂ : S₂ M D)
    (harr : IsMaximalArrivalBound (⇑A) α)
    (hprop : minDeconv (liftENN α) (liftENN β₁) ≤ liftENN α₂)
    (hstab₁ : IsLocallyStableServer α β₁)
    (hstab₂ : IsLocallyStableServer α₂ β₂) :
    IsGloballyStableServer ⇑A ⇑M ∧ IsGloballyStableServer ⇑M ⇑D := by
  refine ⟨isGloballyStableServer_of_isLocallyStableServer hc₁ hβ₁ hp₁ harr hstab₁, ?_⟩
  -- `M`'s output bound `α ⊘ β₁`, derived by propagation, dominated by `α₂`
  have hMprop : IsMaximalArrivalBound (liftENN ⇑M) (minDeconv (liftENN α) (liftENN β₁)) :=
    isMaximalArrivalBound_output_of_isStrictMinimalServiceCurve hc₁ hβ₁ hp₁
      (isMaximalArrivalBound_liftENN_iff.mpr harr)
  have hMα₂ : IsMaximalArrivalBound (⇑M) α₂ :=
    isMaximalArrivalBound_liftENN_iff.mp (hMprop.mono hprop)
  exact isGloballyStableServer_of_isLocallyStableServer hc₂ hβ₂ hp₂ hMα₂ hstab₂

open Deviation in
omit [DecidableEq κ] in
/-- **Single-flow feed-forward path global stability** (every hop's bound
derived). A flow crosses servers `h 0, h 1, …, h (n-1)` in series (`proc k` is
its process entering hop `k`, served by `S (h k)` to `proc (k+1)`), with ingress
maximal arrival curve `αs 0`. If each hop's propagated output bound
`αs k ⊘ β(h k)` is dominated by the next witness `αs (k+1)` and every hop is
locally stable, then *every* server on the path has a bounded backlogged
period. The per-hop arrival bound `IsMaximalArrivalBound ⇑(proc k) (αs k)` is
*derived* — maintained as the induction invariant by propagating along the
prefix and reading back through the `liftENN` carrier bridge. -/
theorem isGloballyStable_path {n : ℕ}
    {S : κ → Curve → Curve → Prop} {β : κ → ℝ≥0 → ℝ≥0}
    (hc : ∀ h, IsCausal (S h)) (hβ : ∀ h, IsStrictMinimalServiceCurve (β h) (S h))
    (h : ℕ → κ) (proc : ℕ → Curve) (αs : ℕ → ℝ≥0 → ℝ≥0)
    (hchain : ∀ k, k < n → S (h k) (proc k) (proc (k + 1)))
    (harr0 : IsMaximalArrivalBound (⇑(proc 0)) (αs 0))
    (hprop : ∀ k, k < n → minDeconv (liftENN (αs k)) (liftENN (β (h k))) ≤ liftENN (αs (k + 1)))
    (hstab : ∀ k, k < n → IsLocallyStableServer (αs k) (β (h k))) :
    ∀ k, k < n → IsGloballyStableServer (⇑(proc k)) (⇑(proc (k + 1))) := by
  have hinv : ∀ k, k ≤ n → IsMaximalArrivalBound (⇑(proc k)) (αs k) := by
    intro k
    induction k with
    | zero => intro _; exact harr0
    | succ m ih =>
      intro hm
      have hmlt : m < n := Nat.lt_of_succ_le hm
      have hout := isMaximalArrivalBound_output_of_isStrictMinimalServiceCurve
        (hc (h m)) (hβ (h m)) (hchain m hmlt)
        (isMaximalArrivalBound_liftENN_iff.mpr (ih hmlt.le))
      exact isMaximalArrivalBound_liftENN_iff.mp (hout.mono (hprop m hmlt))
  intro k hk
  exact isGloballyStableServer_of_isLocallyStableServer (hc (h k)) (hβ (h k))
    (hchain k hk) (hinv k hk.le) (hstab k hk)

open Deviation in
/-- **Separated-flow per-flow path stability** (multi-flow, multi-server,
cross-traffic): flow `i` crosses a chain of `n`-servers `Sf 0, …, Sf (n-1)`,
each with strict aggregate service `βf k`; at hop `k` its cross-traffic
departures are `αcross k`-constrained, so it sees the residual
`residualCurve (βf k) (αcross k)`. With its ingress curve `αs 0` propagated
along the residual chain (the witness invariant `αs k`) and each hop locally
stable, flow `i` has a bounded backlogged period at *every* server on its path.
The residual-is-strict-service and the per-hop arrival bound are both derived
(`isGloballyStable_path` over residual servers); only the cross-traffic bounds
`αcross k` (computed by propagating the other flows in the SFA topological pass)
are parameters. -/
theorem isGloballyStable_residualPath {n : ℕ}
    {Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop} {βf αcross : ℕ → ℝ≥0 → ℝ≥0}
    {i : ι} (hcaus : ∀ k, IsCausalN (Sf k))
    (hβf : ∀ k, IsStrictMinimalServiceCurve (βf k) (aggregateServer (Sf k)))
    (proc : ℕ → Curve) (αs : ℕ → ℝ≥0 → ℝ≥0)
    (hchain : ∀ k, k < n → residualServer (fun A D => Sf k A D ∧ IsMaximalArrivalBound
      (fun x => ∑ j ∈ Finset.univ.erase i, (D j) x) (αcross k)) i (proc k) (proc (k + 1)))
    (harr0 : IsMaximalArrivalBound (⇑(proc 0)) (αs 0))
    (hprop : ∀ k, k < n → minDeconv (liftENN (αs k))
      (liftENN (residualCurve (βf k) (αcross k))) ≤ liftENN (αs (k + 1)))
    (hstab : ∀ k, k < n → IsLocallyStableServer (αs k) (residualCurve (βf k) (αcross k))) :
    ∀ k, k < n → IsGloballyStableServer (⇑(proc k)) (⇑(proc (k + 1))) :=
  isGloballyStable_path
    (S := fun k => residualServer (fun A D => Sf k A D ∧ IsMaximalArrivalBound
      (fun x => ∑ j ∈ Finset.univ.erase i, (D j) x) (αcross k)) i)
    (β := fun k => residualCurve (βf k) (αcross k))
    (fun k => isCausal_residualServer (fun A D hAD => hcaus k A D hAD.1) i)
    (fun k => isStrictMinimalServiceCurve_residualServer (hcaus k) (hβf k))
    id proc αs hchain harr0 hprop hstab

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
