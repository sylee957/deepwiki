import DeepWiki.NetworkCalculus.ServersResidualFifoPmoo
import DeepWiki.NetworkCalculus.ServersResidualFifoPmooConcat
import DeepWiki.NetworkCalculus.ServersResidualGfa
import DeepWiki.NetworkCalculus.ServersResidualGfaTightness
import DeepWiki.NetworkCalculus.ServersResidualGpsStrict
import DeepWiki.NetworkCalculus.ServersResidualPmoo
import DeepWiki.NetworkCalculus.ServersResidualPmooChain
import DeepWiki.NetworkCalculus.ServersResidualPmooPath
import DeepWiki.NetworkCalculus.ServersResidualPmooRateLatency
import DeepWiki.NetworkCalculus.ServersResidualSfa
import DeepWiki.NetworkCalculus.ServersResidualSpPmoo
import DeepWiki.NetworkCalculus.ServersToa
import DeepWiki.NetworkCalculus.ServiceCurveStrict
import Sources.Dnc.Source

/-! # DNC catalog — Chapter 10: Modular Analysis: Computing with Curves
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-! **Definition 10.1** (§10.2, p.233): Network topology classes: feed-forward (acyclic flow graph, topological sort), tandem (servers in a line), and nested tandem (flow paths totally ordered by inclusion, (Nest): i<j ⇔ pᵢ⊆pⱼ). Not formalized in the library. -/

/-! **Example 10** (§10.3.1, p.235): Loss of tightness: on the two-flow two-server network, the two computation methods give incomparable end-to-end service curves β̃₁ (general feed-forward residual) and β̃₂ (PMOO), with neither dominating in general (β₁=β₂ ⇒ β̃₂≤β̃₁; b₁=0,T₁=0,R₂>R₁ ⇒ β̃₁≤β̃₂). Not formalized in the library. -/

/-- **Theorem 10.1** (§10.3.2, p.237): PMOO multi-dimensional operator: in a tandem where flow 1 crosses all servers, each server h offering a strict service curve β⁽ʰ⁾ to its aggregate and each cross-flow i constrained by αᵢ over its sub-path, flow 1 gets the min-plus service curve β = [ inf_{∑uⱼ=t} ∑ⱼβ⁽ʲ⁾(uⱼ) − ∑ᵢαᵢ(∑_{h∈pᵢ}uⱼ) ]⁺. -/
alias thm_10_1 := isMinimalServiceCurve_pmooPathResidual_of_strict_path

/-- **Definition 10** (§10.3.2, p.237): The PMOO operator's service curve: infimum over time splits ∑_{h≤n}uₕ=t of ∑ₕβ⁽ʰ⁾(uₕ) − ∑ᵢαᵢ(∑_{h∈pᵢ}uₕ), the aggregate strict service less each cross-flow's arrival charged over its own contiguous path. -/
noncomputable def def_10_pmooPathResidual := @pmooPathResidual

/-! **Lemma 10.1** (§10.3.2, p.237): Cumulative-process inequality underlying Theorem 10.1: ∀t ∃u₁..uₙ≥0 with ∑uⱼ such that F₁⁽ⁿ⁾(t)−F₁⁽⁰⁾(t−∑uⱼ) ≥ ∑ⱼβⱼ(uⱼ) − ∑ᵢ(Fᵢ^{end(i)}(…)−Fᵢ^{(0)}(…)), and moreover F₁⁽ⁿ⁾(t)−F₁⁽⁰⁾(t−∑uⱼ)≥0 — the telescope of per-hop strict steps over the cascaded starts. Library: DeepWiki.sum_add_pathTelescope_le, DeepWiki.pathNode_floor. -/

/-- **Example 10.1** (§10.3.2, p.238): PMOO on a sink-tree of rate-latency servers β_{Rₕ,Tₕ} with token-bucket cross-traffic γ_{rₐ,bₐ}: the residual is again rate-latency β_{R,T} with R=(⊓ₕRₕ)−∑rₐ and T=∑ₕTₕ + (∑rₐ·∑ₕTₕ+∑bₐ)/R, under stability ∑rₐ<⊓ₕRₕ; the tandem of rate-latency servers folds to one rate-latency server. -/
alias ex_10_1 := pmooResidualChain_rateLatency

/-- **Example 10.1** (§10.3.2, p.238): Supporting fact for Example 10.1: the chain convolution of rate-latency curves β_{Rₕ,Tₕ} over hops 0..n equals the single rate-latency curve β_{⊓ₕRₕ, ∑ₕTₕ} (slowest rate, summed latencies). -/
alias ex_10_1_chainConv := chainConv_rateLatency

/-- **Remark 10** (§10.3.3, p.239): Service policies are not stable under composition: a system composed of two GPS servers (with given weights) is not itself a GPS server — the cross-flow is backlogged end-to-end yet receives strictly less than its equal share. -/
alias remark_10_gps_composition := not_forall_isGps_comp

/-- **Theorem 3** (§10.3.4.1, p.241): Algorithm 3 (PMOO for static-priority, nested tandems): recursively β̃ᵢ over the nesting order; the building block formalized is that the chain of per-server static-priority residual servers offers flow i the end-to-end convolution β̃ᵢ = ∗_{h∈pᵢ}[β⁽ʰ⁾ − ∑_{j<i}αⱼ⁽ʰ⁾]⁺. -/
alias alg_3_sp_pmoo := isMinimalServiceCurve_concatConv_spResidual

/-! **Example 10.2** (§10.3.4.1, p.241): SP-PMOO worked on the nested tandem of Figure 10.1 (bottom): computing β̃₂ = β⁽²⁾, β̃₃ = β⁽³⁾, β̃₁ = (β⁽¹⁾∗β⁽²⁾∗β⁽³⁾ − [β̃₂−α₂]⁺ − [β̃₃−α₃]⁺ …)⁺. Not formalized in the library. -/

/-- **Proposition 10.1** (§10.3.4.2, p.241): FIFO and PMOO: if a FIFO server (system) offers the aggregate min-plus service curve β and flow k has maximal arrival curve α, then [β − α∗δ_θ]⁺ ∧ δ_θ is a min-plus service curve for the m−1 other flows, for any θ — a direct consequence of the FIFO single-server residual and concatenation. -/
alias prop_10_1 := minConv_fifoResidual_le_of_isFifo_group

/-- **Theorem 4** (§10.3.4.2, p.242): Algorithm 4 (PMOO for FIFO, nested tandems): the per-flow FIFO residual over a tandem, β̃ = [∗ₕβ⁽ʰ⁾ − α∗δ_θ]⁺ ∧ δ_θ, with the concatenation service curve ∗ₕβ⁽ʰ⁾ made explicit (then optimized over θ). -/
alias alg_4_fifo_pmoo := minConv_fifoResidual_concatConv_le

/-- **Example 10.3** (§10.3.4.2, p.242): FIFO-PMOO worked on the sink-tree of Figure 10.1 with rate-latency servers and token-bucket arrivals, optimizing θ₁ (greater than C₁) to compute the per-path delay bound d. -/
alias ex_10_3 := DeepWiki.minConv_fifoResidual_concatConv_le

/-- **Theorem 5** (§10.4.1, p.244): Algorithm 5 (Total Output Analysis, TOA): per-server delay d⁽ʰ⁾ = inf{t>0 | α⁽ʰ⁾(t)≤β⁽ʰ⁾(t)} = firstCrossing of aggregate arrival vs strict service; per-flow end-to-end delay dᵢ = ∑_{h∈pᵢ}d⁽ʰ⁾ (additive composition of per-server delays). -/
alias alg_5_toa := delay_le_sum_of_perhop

/-- **Theorem 5** (§10.4.1, p.244): TOA line 4: under a strict service curve β with aggregate arrival curve α, every backlogged period at the server has length at most firstCrossing α β (the per-server delay term summed by TOA). -/
alias alg_5_perhop_delay := maxBackloggedLength_le_firstCrossing

/-- **Example 10.4** (§10.4.1, p.244): TOA worked on Figure 10.2 (top): the output arrival curves αᵢ⁽²⁾ are computed as αᵢ⁽¹⁾⊘β⁽¹⁾ and combined, then the worst-case backlogged-period bound per server. -/
alias ex_10_4 := DeepWiki.delay_le_sum_of_perhop

/-- **Theorem 6** (§10.4.2, p.246): Algorithm 6 (Generic Separated Flow Analysis, SFA): at each server h compute the blind-multiplexing residual βᵢ⁽ʰ⁾ = [β⁽ʰ⁾ − ∑_{j≠i}αⱼ⁽ʰ⁾]⁺ and convolve along flow i's path to the end-to-end min-plus service curve β̃ᵢ = ∗_{h∈pᵢ}βᵢ⁽ʰ⁾. -/
alias alg_6_sfa := isMinimalServiceCurve_concatConv_residualServer

/-- **Example 10.5** (§10.4.2, p.247): SFA worked on the table of Figure 10.1 (top): explicit per-server residual and output arrival curves, then the path convolution giving each flow's end-to-end service curve. -/
alias ex_10_5 := DeepWiki.isMinimalServiceCurve_concatConv_residualServer

/-- **Theorem 7** (§10.4.3, p.250): Algorithm 7 (Generic Group Flow Analysis, GFA): subtract a grouped cross-traffic aggregate η⁽ʰ⁾ (arc-wise flow partition, shaper-capped output arrival (η⊘β)∧σ) rather than the flat ∑_{j≠i}αⱼ; end-to-end β̃ᵢ = ∗_{h∈pᵢ}[β⁽ʰ⁾ − η⁽ʰ⁾]⁺. -/
alias alg_7_gfa := isMinimalServiceCurve_concatConv_groupResidual

/-- **Theorem 7** (§10.4.3, p.250): GFA refines SFA: when the grouped aggregate η⁽ʰ⁾ ≤ ∑_{j≠i}αⱼ⁽ʰ⁾ at every server, the GFA end-to-end service curve dominates the SFA one (residual antitone in subtracted aggregate, path convolution monotone). -/
alias alg_7_gfa_dominates_sfa := concatConv_residualCurve_sfa_le_gfa

/-- **Example 10.6** (§10.4.3, p.249): GFA worked on Figure 10.6 with flow 2 the flow of interest: arc-wise grouping of cross-traffic, the grouped arrival/service curves η and β̃ at each server. -/
alias ex_10_6 := DeepWiki.isMinimalServiceCurve_concatConv_groupResidual

/-! **Theorem 10.2** (§10.5, p.251): NP-hardness: computing an exact worst-case backlog/delay bound for a feed-forward network with arbitrary multiplexing is NP-hard (reduction from 3-dimensional matching / exact cover, via the transformation of an instance of X3C into a network of Figure 10.7). Not formalized in the library. -/

end DeepWiki.Dnc
