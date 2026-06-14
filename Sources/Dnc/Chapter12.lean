import DeepWiki.NetworkCalculus.Stability
import Sources.Dnc.Source

/-! # DNC catalog — Chapter 12: Stability in Networks with Cyclic Dependencies
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki

/-- **Definition 12.1** (§12.1.1, p.270): long-term rates — the arrival rate
`limsup_{t→∞} α(t)/t` (`longTermArrivalRate`) and the service rate
`liminf_{t→∞} β(t)/t` (`longTermServiceRate`). -/
noncomputable def def_12_1_arrivalRate := @longTermArrivalRate

/-- **Definition 12.1** (§12.1.1, p.270): the long-term service rate
`liminf_{t→∞} β(t)/t`. -/
noncomputable def def_12_1_serviceRate := @longTermServiceRate

/-! **Definition 12.2** (§12.1.1, p.271): Local stability: a network is locally stable if for every server h, ∑_{i∈Fl(h)} rᵢ < R^(h), or R^(h)=∞ (sum of flow long-term arrival rates below the server's long-term service rate). Not formalized in the library. -/

/-! **Lemma 12.1** (§12.1.1, p.271): If server h is locally stable then ℓmax(∑_{i∈Fl(h)} αᵢ, β^(h)) < ∞, i.e. the maximal length of its backlogged period (as in Theorem 5.5) is finite. Not formalized in the library. -/

/-! **Definition 12.3** (§12.1.2, p.271): Global stability: a network is globally stable if for each server the length of its maximal backlogged period is bounded. Not formalized in the library. -/

/-! **Lemma 12.2** (§12.1.2, p.271): If a network is globally stable then it is locally stable. Not formalized in the library. -/

/-! **Lemma 12.3** (§12.1.2, p.272): If for a network with token-bucket arrival and rate-latency service curves respecting the local stability conditions the network is globally stable, then local stability for any arrival and service curve is also a sufficient condition for global stability. Not formalized in the library. -/

/-! **Lemma 12.4** (§12.1.2, p.272): If αᵢ^(h) are arrival curves for flow i at the input of server h and for all h, ℓmax(∑_{i∈Fl(h)} αᵢ^(h), β^(h)) < ∞, then the network is globally stable. Not formalized in the library. -/

/-! **Example 12.1** (§12.2.1, p.273): The example network of Figure 12.1 (top) is transformed by removing arc h'={(4,2),(2,1)} into an acyclic feed-forward network N^FF; flows splitting into sub-flows (i,k). Not formalized in the library. -/

/-! **Theorem 12.1** (§12.2.3, p.275): Fix-point sufficient condition: let C={α | α ≤ F(α)} be the solutions of α ≤ F(α) and α̂ = sup{α | α∈C}; if α̂ is finite then N is globally stable and each α̂_{i,k} is an arrival curve for flow i at the first server of flow (i,k). Not formalized in the library. -/

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

end DeepWiki.Dnc
