import DeepWiki.NetworkCalculus.Stability
import DeepWiki.NetworkCalculus.StabilityGlobal
import DeepWiki.NetworkCalculus.StabilityFixPoint
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
`IsLocallyStableServer`. (The network predicate quantifies this over every
server `h`; that quantification needs a network model and is not formalized.) -/
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
(The network predicate asks this of every server.) -/
abbrev def_12_3 := @IsGloballyStableServer

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

/-! **Example 12.1** (§12.2.1, p.273): The example network of Figure 12.1 (top) is transformed by removing arc h'={(4,2),(2,1)} into an acyclic feed-forward network N^FF; flows splitting into sub-flows (i,k). Not formalized in the library. -/

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

/-! **Theorem 12.2** (§12.3.1, p.276): Static priority policies: a network where flows have fixed priorities and a strict priority order (each flow a different priority) is stable if and only if it is locally stable. Not formalized in the library. -/

/-! **Example 12.2** (§12.3.2, p.278): For the Figure 12.1 network under FDF: in server 3 flow 1 has highest priority, then flow 2; flows 2 and 3 share the same priority; in server 2 flows 4 and 3 are highest and flow 1 lowest. Not formalized in the library. -/

/-! **Theorem 12.3** (§12.3.2, p.278): Furthest destination first (FDF): the local stability condition is a sufficient condition for global stability under the FDF policy. Not formalized in the library. -/

/-! **Lemma 12.5** (§12.3.3, p.279): GPS with fixed parameters: with αᵢ=γ_{rᵢ,bᵢ} arrival curves and β^(h)=β_{R^(h),T^(h)} strict service, there is a flow i such that for every server h∈p(i): rᵢ < φᵢ · R^(h)/(∑_{j∈Fl(h)} φⱼ). Not formalized in the library. -/

/-! **Theorem 12.4** (§12.3.3, p.279): GPS with constant rates: the local stability condition is a sufficient condition for global stability. Not formalized in the library. -/

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

end DeepWiki.Dnc
