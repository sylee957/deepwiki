import DeepWiki.NetworkCalculus.ArrivalCurvesAggregate
import DeepWiki.NetworkCalculus.Servers
import DeepWiki.NetworkCalculus.ServersMimo
import DeepWiki.NetworkCalculus.ServersResidual
import DeepWiki.NetworkCalculus.ServersResidualEdf
import DeepWiki.NetworkCalculus.ServersResidualFifo
import DeepWiki.NetworkCalculus.ServersResidualFifoOutput
import DeepWiki.NetworkCalculus.ServersResidualGps
import DeepWiki.NetworkCalculus.ServersResidualGpsImproved
import DeepWiki.NetworkCalculus.ServersResidualMinimal
import DeepWiki.NetworkCalculus.ServersResidualOutput
import DeepWiki.NetworkCalculus.ServersResidualPriority
import DeepWiki.NetworkCalculus.ServersResidualPriorityPackets
import DeepWiki.NetworkCalculus.ServiceCurveMinimal
import DeepWiki.NetworkCalculus.ServiceCurveStrict
import Sources.Doi_10_1002_9781119440284.Source

/-! # DNC catalog — Chapter 7: Multiple Flows Crossing One Server
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
§7.3: Example 7.1 (FIFO 2-flow residual rate-latency, with figure) `[deferred]`. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-- **Definition 7.1** (§7.1.1, p.152): Aggregate flow: for a finite set I of flows the aggregate cumulative process is the pointwise sum A = ∑_{i∈I} A_i. -/
alias def_7_1 := Curve.sum_apply

/-- **Proposition 7.1** (§7.1.1, p.152): If each A_i has arrival curve α_i then α = ∑_i α_i is an arrival curve for the aggregate process ∑_i A_i. -/
alias prop_7_1 := isMaximalArrivalBound_sum

/-- **Proposition 7.2** (§7.1.1, p.153): Arrival curve of a sub-flow: if α is an arrival curve for the aggregate ∑_i A_i (non-decreasing flows) then α is an arrival curve for each sub-flow A_j. -/
alias prop_7_2 := isMaximalArrivalBound_of_sum

/-- **Definition 7.2** (§7.1.2, p.153): MIMO (n-)server: a relation S ⊆ 𝒞ⁿ × 𝒞ⁿ between input and output vectors of cumulative processes that is causal per flow (D_i ≤ A_i) and left-total. -/
abbrev def_7_2 := @IsServerN

/-- **Definition 7.3** (§7.1.2, p.154): Aggregate server S_Σ of an n-server: relates the summed input ∑_i A_i to the summed output ∑_i D_i over served families. -/
abbrev def_7_3 := @aggregateServer

/-- **Definition 7.4** (§7.1.2, p.154): Residual server S_i of an n-server for flow i: the projection of the relation onto coordinate i (the other flows are cross-traffic), possibly non-deterministic. -/
noncomputable def def_7_4 := @residualServer

/-! **Definition 7.5** (§7.1.2, p.154): Aggregate service curve: a MIMO server S offers β as an aggregate service curve of type 𝒯 iff its aggregate server S_Σ offers β as a service curve of type 𝒯. -/
/-- **Definition 7.5** (linked: `aggregateServer`). -/
noncomputable def def_7_5_1 := @aggregateServer
/-- **Definition 7.5** (linked: `IsMinimalServiceCurve`). -/
noncomputable def def_7_5_2 := @IsMinimalServiceCurve
/-- **Definition 7.5** (linked: `IsStrictMinimalServiceCurve`). -/
alias def_7_5_3 := IsStrictMinimalServiceCurve

/-! **Definition 7.6** (§7.1.2, p.154): Residual service curve: a MIMO server S offers β as a residual service curve for flow i iff its residual server S_i offers β as a service curve. -/
/-- **Definition 7.6** (linked: `residualServer`). -/
noncomputable def def_7_6_1 := @residualServer
/-- **Definition 7.6** (linked: `isMinimalServiceCurve_residualServer_of_minimal_aggregate`). -/
alias def_7_6_2 := isMinimalServiceCurve_residualServer_of_minimal_aggregate

/-! **Lemma 7.1** (§7.1.2, p.155): MIMO server backlogged period: for a causal family, the aggregate is backlogged on a period iff at each instant some flow is backlogged; a flow's backlogged period is one for any aggregate containing it. -/
/-- **Lemma 7.1** (linked: `isBacklogged_sum_iff`). -/
alias lemma_7_1_1 := isBacklogged_sum_iff
/-- **Lemma 7.1** (linked: `isBacklogged_sum_of_isBacklogged`). -/
alias lemma_7_1_2 := isBacklogged_sum_of_isBacklogged

/-- **Theorem 7.1** (§7.2.1, p.156): Blind multiplexing from an aggregate strict service: an n-server with a strict aggregate curve β and α_j-bounded arrivals serves flow i at the min-plus residual β_i = [β − ∑_{j≠i} α_j]⁺↑, i.e. D_i ≥ A_i ∗ β_i. -/
alias thm_7_1 := minConv_residualCurve_le_of_isStrictMinimalServiceCurve

/-- **Theorem 7.2** (§7.2.2, p.159): Blind multiplexing and strict residual: if the cross-traffic departures ∑_{j≠i} D_j are α-constrained, the residual server for flow i offers [β − α]⁺↑ as a strict residual service curve. -/
alias thm_7_2 := isStrictMinimalServiceCurve_residualServer

/-- **Corollary 7.1** (§7.2.2, p.160): Strict residual from arrival curves: an n-server with strict aggregate β where each A_j has arrival curve α_j offers flow i the strict residual β_i = [β − ((∑_{j≠i} α_j) ⊘ [β − α_i]⁺↑)*]⁺↑. -/
alias cor_7_1 := isStrictMinimalServiceCurve_residualServer_of_closure_le

/-- **Theorem 7.3** (§7.2.3, p.161): Blind multiplexing from a min-plus aggregate (warning): an n-server with a left-continuous min-plus aggregate β and α_j-bounded arrivals serves flow i at the raw residual β − ∑_{j≠i} α_j, which may be negative and so cannot feed performance bounds. -/
alias thm_7_3 := minConv_residualCurveEReal_le_of_minimal_aggregate

/-- **Definition 7.7** (§7.3.1.1, p.164): FIFO service policy: an n-server is FIFO iff D_i(t) > A_i(u) ⟹ D_j(t) ≥ A_j(u) for all flows i,j and all t,u (data gone for one flow is gone for all, and conversely). -/
abbrev def_7_7 := @IsFifo

/-! **Lemma 7.2** (§7.3.1.1, p.165): FIFO characterization via aggregate: the two FIFO implications are contrapositives, and a FIFO aggregate comparison ∑A_j(u) ≤ ∑D_j(t) (or the reverse) transfers to every flow. -/
/-- **Lemma 7.2** (linked: `isFifo_iff`). -/
alias lemma_7_2_1 := isFifo_iff
/-- **Lemma 7.2** (linked: `forall_le_of_sum_le_of_isFifo`). -/
alias lemma_7_2_2 := forall_le_of_sum_le_of_isFifo
/-- **Lemma 7.2** (linked: `forall_le_of_le_sum_of_isFifo`). -/
alias lemma_7_2_3 := forall_le_of_le_sum_of_isFifo

/-- **Theorem 7.4** (§7.3.1.2, p.165): FIFO delay bound: a FIFO server with min-plus aggregate β and aggregate arrival curve α offers each flow the pure delay δ_dM for any dM ≥ hDev(α, β); dM bounds every flow's delay. -/
alias thm_7_4 := apply_tsub_le_of_isFifo

/-- **Theorem 7.5** (§7.3.1.3, p.166): FIFO residual service curves (θ-family): a FIFO server with min-plus aggregate β and cross arrival curves α_j offers flow i the residual β_i^θ = [β − ∑_{j≠i} α_j ∗ δ_θ]⁺ ∧ δ_θ for every offset θ. -/
alias thm_7_5 := minConv_fifoResidual_le_of_isFifo

/-- **Corollary 7.2** (§7.3.1.3, p.167): FIFO departure arrival curve: an arrival curve for the
departure process of flow i is `⨅_{θ≥0} (α_i ⊘ β_i^θ)` using the θ-family residual — proved by
applying the deconvolution output bound (Thm 5.3) per offset θ and taking the infimum (Prop 5.2).
The library's `isMaximalArrivalBound_fifoOutput_iInf`. -/
alias cor_7_2 := isMaximalArrivalBound_fifoOutput_iInf

/-- **Definition 7.8** (§7.3.2, p.169): Static priority (preemptive): if the higher-priority aggregate ∑_{j<i} A_j is backlogged on [s,t], flow i is frozen, D_i(t) = D_i(s). -/
abbrev def_7_8 := @IsStaticPriority

/-- **Theorem 7.6** (§7.3.2, p.170): SP residual: under preemptive static priority with left-continuous strict aggregate β and α_j-constrained higher-priority arrivals, flow i is offered the strict residual [β − ∑_{j<i} α_j]⁺↑. -/
alias thm_7_6 := add_residualCurve_le_of_isStaticPriority

/-- **Definition 7.9** (§7.3.3, p.171): GPS (generalized processor sharing) with weights φ_i: on every backlogged period of flow i the served amounts respect proportional shares φ_i·(D_j(t)−D_j(s)) ≤ φ_j·(D_i(t)−D_i(s)). -/
abbrev def_7_9 := @IsGps

/-- **Theorem 7.7** (§7.3.3, p.171): GPS residual service curve: a GPS server offering strict aggregate β with weights φ offers flow i the strict residual service curve (φ_i/∑_j φ_j)·β. -/
alias thm_7_7 := isStrictMinimalServiceCurve_residualServer_of_isGps

/-- **Theorem 7.8** (§7.3.3, p.172): GPS with variable capacity / arrival-constrained cross-flow k (convex β, concave α): flow i≠k is offered the improved residual φ_i·max(β/Φ, (β−α_k)/Φ_{−k}) as a strict service curve. -/
alias thm_7_8 := add_max_div_mul_le_of_isGps_ungated

/-- **Lemma 7.3** (§7.3.3, p.173): GPS aggregate-share lemma: on a backlogged period of flow i, the rest-of-traffic increment is controlled by flow i's increment scaled by the weights, ∑_{j≠1}(D_j(t)−D_j(s)) relation used in the improved-GPS proof. -/
alias lemma_7_3 := mul_sum_le_sum_mul_of_isGps

/-- **Lemma 7.4** (§7.3.3, p.173): GPS backlogged-period bound: under the hypotheses of Thm 7.8, the per-flow released share over a backlogged period is bounded below by the gated residual (φ_k·β − Φ·α released after crossing T). -/
alias lemma_7_4 := add_gatedResidual_le_of_isGps

/-- **Lemma 7.5** (§7.3.3, p.174): Under the hypotheses of Thm 7.8, for each flow i≥2 the curve φ_i·max(β/Φ, (β−α_1)/Φ_{−1}) is a strict service curve for flow i (the maximum of the two share curves). -/
alias lemma_7_5 := isStrictMinimalServiceCurve_max_residualServer_of_isGps_ungated

/-- **Definition 7.10** (§7.3.4.1, p.177): EDF (earliest-deadline-first) scheduler with relative deadlines d_i: if the deadline-T aggregate (data due by T) is backlogged, flow j's data with deadline after T receives nothing — a deadline-ordered preemptive priority. -/
abbrev def_7_10 := @IsEdf

/-- **Theorem 7.9** (§7.3.4.1, p.178): EDF residual service curve: an EDF server with deadlines d, strict left-continuous aggregate β and cross arrival curves α_j offers flow i the residual β_i^θ = [β − ∑_{j≠i} α_j ∗ δ_{[θ−Δ_{ij}]⁺}]⁺ ∧ δ_θ for every θ. -/
alias thm_7_9 := minConv_edfResidual_le_of_isEdf

/-- **Definition 7.11** (§7.3.4.2, p.179): Deadline compatibility: every flow's arrivals are served within its relative deadline, A_i ∗ δ_{d_i} ≤ D_i, i.e. A_i(t − d_i) ≤ D_i(t) for all i,t. -/
abbrev def_7_11 := @IsDeadlineCompatible

/-- **Theorem 7.10** (§7.3.4.2, p.180): Necessary condition for deadline compatibility: if a server with min-plus aggregate β is deadline compatible for d under arrival curves α_i, then β ≥ ∑_i α_i ∗ δ_{d_i} (witnessed at the greedy trajectory). -/
alias thm_7_10 := sum_apply_tsub_le_of_isDeadlineCompatible

/-- **Theorem 7.11** (§7.3.4.3, p.181): Sufficient condition: an EDF server with strict left-continuous aggregate β meeting ∑_i α_i ∗ δ_{d_i} ≤ β (the capacity condition) is deadline compatible. -/
alias thm_7_11 := isDeadlineCompatible_of_isEdf

end DeepWiki.Dnc
