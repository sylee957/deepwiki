import DeepWiki.NetworkCalculus.ServersResidualFifoPmoo
import DeepWiki.NetworkCalculus.ServersResidualFifoPmooConcat
import DeepWiki.NetworkCalculus.ServersResidualGfa
import DeepWiki.NetworkCalculus.ServersResidualGfaTightness
import DeepWiki.NetworkCalculus.ServersResidualGpsStrict
import DeepWiki.NetworkCalculus.ServersResidualPmoo
import DeepWiki.NetworkCalculus.ServersResidualPmooChain
import DeepWiki.NetworkCalculus.ServersResidualPmooPath
import DeepWiki.NetworkCalculus.ServersResidualPmooRateLatency
import DeepWiki.NetworkCalculus.ServersResidualPmooDelay
import DeepWiki.NetworkCalculus.ServersResidualSfa
import DeepWiki.NetworkCalculus.ServersResidualSfaDelay
import DeepWiki.NetworkCalculus.ServersResidualGfaDelay
import DeepWiki.NetworkCalculus.ServersResidualSpPmooDelay
import DeepWiki.NetworkCalculus.ServersResidualSpPmoo
import DeepWiki.NetworkCalculus.ServersToa
import DeepWiki.NetworkCalculus.ServiceCurveStrict
import DeepWiki.NetworkCalculus.NetworkTopology
import DeepWiki.NetworkCalculus.PmooSeparatedFlowIncomparable
import DeepWiki.NetworkCalculus.StaticPriorityPmooNestedTandem
import DeepWiki.NetworkCalculus.WorstCaseBoundX3CReduction
import DeepWiki.NetworkCalculus.WorstCaseBoundX3CReductionBridge
import DeepWiki.NetworkCalculus.WorstCaseBoundX3CReductionNetwork
import DeepWiki.NetworkCalculus.WorstCaseBoundX3CReductionConvexity
import DeepWiki.NetworkCalculus.WorstCaseBoundX3CReductionTrajectory
import Sources.Doi_10_1002_9781119440284.Source

/-! # DNC catalog — Chapter 10: Modular Analysis: Computing with Curves
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
§10.5: Theorem 10.2 (NP-hardness of exact worst-case bounds, X3C reduction) — the combinatorial CORE
(`thm_10_2_core`) AND the reduction correctness (`thm_10_2_reduction`: worst-case backlog ≥ 3s−2q ⟺
exact 3-cover, the worst-case objective as a `programOptimum`) are done — the formalizable poly-time
reduction. The network-served realization (`thm_10_2_network`) computes the ACTUAL backlog at `W` from
the Figure-10.7 served rate equations and transfers the `3s−2q ⟺ cover` threshold to it. The two
former analysis residuals are now CLOSED: fractional-routing optimality (`thm_10_2_fractional`: every
fractional fluid routing has objective ≤ q, by convexity + `convexHull_pi` — no fractional advantage)
and the continuous-time realization (`thm_10_2_trajectory`: the rate-based backlog as a genuine
capped-ramp trajectory, value at `t→1⁻`). The SOLE residual is the `NPHard` typeclass `[external]` —
Mathlib has no complexity-class framework, so the "therefore NP-hard" label (given the correct
poly-time reduction, which IS formalized) is unstatable, a separate framework-building project. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-- **Definition 10.1**, feed-forward (§10.2, p.233): the flow graph is acyclic
— there is a server ranking under which every flow path strictly increases.
The library's `IsFeedForward`. -/
def def_10_1_feedforward := @IsFeedForward

/-- **Definition 10.1**, tandem (§10.2, p.233): every flow path is a contiguous
subpath of one line of servers. The library's `IsTandemNetwork`. -/
def def_10_1_tandem := @IsTandemNetwork

/-- **Definition 10.1**, nested tandem (§10.2, p.233): the flow paths are
totally ordered by contiguous-subpath inclusion (the (Nest) condition). The
library's `IsNestedTandem`. -/
def def_10_1_nested := @IsNestedTandem

/-- **Theorem 10.1** (§10.3.2, p.237): PMOO multi-dimensional operator: in a tandem where flow 1 crosses all servers, each server h offering a strict service curve β⁽ʰ⁾ to its aggregate and each cross-flow i constrained by αᵢ over its sub-path, flow 1 gets the min-plus service curve β = [ inf_{∑uⱼ=t} ∑ⱼβ⁽ʲ⁾(uⱼ) − ∑ᵢαᵢ(∑_{h∈pᵢ}uⱼ) ]⁺. -/
alias thm_10_1 := isMinimalServiceCurve_pmooPathResidual_of_strict_path

/-- **Definition 10** (§10.3.2, p.237): The PMOO operator's service curve: infimum over time splits ∑_{h≤n}uₕ=t of ∑ₕβ⁽ʰ⁾(uₕ) − ∑ᵢαᵢ(∑_{h∈pᵢ}uₕ), the aggregate strict service less each cross-flow's arrival charged over its own contiguous path. -/
noncomputable def def_10_pmooPathResidual := @pmooPathResidual

/-! **Lemma 10.1** (§10.3.2, p.237): Cumulative-process inequality underlying Theorem 10.1: ∀t ∃u₁..uₙ≥0 with ∑uⱼ such that F₁⁽ⁿ⁾(t)−F₁⁽⁰⁾(t−∑uⱼ) ≥ ∑ⱼβⱼ(uⱼ) − ∑ᵢ(Fᵢ^{end(i)}(…)−Fᵢ^{(0)}(…)), and moreover F₁⁽ⁿ⁾(t)−F₁⁽⁰⁾(t−∑uⱼ)≥0 — the telescope of per-hop strict steps over the cascaded starts. -/
/-- **Lemma 10.1** (linked: `sum_add_pathTelescope_le`). -/
alias lemma_10_1_1 := sum_add_pathTelescope_le
/-- **Lemma 10.1** (linked: `pathNode_floor`). -/
alias lemma_10_1_2 := pathNode_floor

/-- **Example 10.1** (§10.3.2, p.238): PMOO on a sink-tree of rate-latency servers β_{Rₕ,Tₕ} with token-bucket cross-traffic γ_{rₐ,bₐ}: the residual is again rate-latency β_{R,T} with R=(⊓ₕRₕ)−∑rₐ and T=∑ₕTₕ + (∑rₐ·∑ₕTₕ+∑bₐ)/R, under stability ∑rₐ<⊓ₕRₕ; the tandem of rate-latency servers folds to one rate-latency server. -/
alias ex_10_1 := pmooResidualChain_rateLatency

/-- **Example 10.1** (§10.3.2, p.238): Supporting fact for Example 10.1: the chain convolution of rate-latency curves β_{Rₕ,Tₕ} over hops 0..n equals the single rate-latency curve β_{⊓ₕRₕ, ∑ₕTₕ} (slowest rate, summed latencies). -/
alias ex_10_1_chainConv := chainConv_rateLatency

/-- **PMOO end-to-end delay/backlog** (performance consequence of Example 10.1, §10.3.2): a
token-bucket flow `γ_{r,b}` (with `r ≤ (⊓ₕRₕ)−∑rₐ`) crossing the PMOO rate-latency tandem has
end-to-end delay `≤ T' + b/R'` and backlog `≤ r·T' + b` (`R' = (⊓ₕRₕ)−∑rₐ`, `T'` the folded
latency) — each cross flow's burst paid once across the whole tandem, not per hop. The library's
`delay_le_pmooChain_rateLatency` / `backlog_le_pmooChain_rateLatency`. -/
alias pmoo_end_to_end_delay := delay_le_pmooChain_rateLatency

@[inherit_doc pmoo_end_to_end_delay]
alias pmoo_end_to_end_backlog := backlog_le_pmooChain_rateLatency

/-- **Remark 10** (§10.3.3, p.239): Service policies are not stable under composition: a system composed of two GPS servers (with given weights) is not itself a GPS server — the cross-flow is backlogged end-to-end yet receives strictly less than its equal share. -/
alias remark_10_gps_composition := not_forall_isGps_comp

/-- **Theorem 3** (§10.3.4.1, p.241): Algorithm 3 (PMOO for static-priority, nested tandems): recursively β̃ᵢ over the nesting order; the building block formalized is that the chain of per-server static-priority residual servers offers flow i the end-to-end convolution β̃ᵢ = ∗_{h∈pᵢ}[β⁽ʰ⁾ − ∑_{j<i}αⱼ⁽ʰ⁾]⁺. -/
alias alg_3_sp_pmoo := isMinimalServiceCurve_concatConv_spResidual

/-- **SP-PMOO end-to-end delay/backlog** (performance consequence of Algorithm 3, §10.3.4.1): for
left-continuous strict rate-latency static-priority servers with higher-priority cross-traffic
aggregating to affine `∑_{j<i}αⱼ⁽ʰ⁾ = ρ h·v+bc h`, the chain folds to `β_{⨅(R h−ρ h),∑T'_h}`, so a
token-bucket flow `γ_{r,b}` with `r ≤ ⨅(R h−ρ h)` has end-to-end delay ≤ ∑T'_h + b/⨅(R h−ρ h) and
backlog ≤ r·∑T'_h+b over arbitrary `List` routing. The library's `delay_le_spPmoo_rateLatency` /
`backlog_le_spPmoo_rateLatency`. -/
alias spPmoo_end_to_end_delay := delay_le_spPmoo_rateLatency

@[inherit_doc spPmoo_end_to_end_delay]
alias spPmoo_end_to_end_backlog := backlog_le_spPmoo_rateLatency

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

/-- **SFA end-to-end delay/backlog** (performance consequence of Algorithm 6, §10.4.2): for
rate-latency servers β_{R h,T h} with per-hop cross-traffic aggregating to affine ρ h·v+bc h, the SFA
end-to-end service curve folds to the single rate-latency β_{⨅(R h−ρ h), ∑T'_h}, so a token-bucket
flow γ_{r,b} with r ≤ ⨅(R h−ρ h) has end-to-end delay ≤ ∑T'_h + b/⨅(R h−ρ h) and backlog ≤ r·∑T'_h+b
over arbitrary `List` routing. The library's `delay_le_sfa_rateLatency` / `backlog_le_sfa_rateLatency`. -/
alias sfa_end_to_end_delay := delay_le_sfa_rateLatency

@[inherit_doc sfa_end_to_end_delay]
alias sfa_end_to_end_backlog := backlog_le_sfa_rateLatency

/-- **Theorem 7** (§10.4.3, p.250): Algorithm 7 (Generic Group Flow Analysis, GFA): subtract a grouped cross-traffic aggregate η⁽ʰ⁾ (arc-wise flow partition, shaper-capped output arrival (η⊘β)∧σ) rather than the flat ∑_{j≠i}αⱼ; end-to-end β̃ᵢ = ∗_{h∈pᵢ}[β⁽ʰ⁾ − η⁽ʰ⁾]⁺. -/
alias alg_7_gfa := isMinimalServiceCurve_concatConv_groupResidual

/-- **GFA end-to-end delay/backlog** (performance consequence of Algorithm 7, §10.4.3): rate-latency
servers with grouped affine cross-traffic η⁽ʰ⁾ = ρ h·v+bc h ⟹ end-to-end folds to β_{⨅(R h−ρ h),∑T'_h},
so a token-bucket flow has delay ≤ ∑T'_h + b/⨅(R h−ρ h) and backlog ≤ r·∑T'_h+b over arbitrary `List`
routing (smaller than SFA when the grouped η is tighter). The library's `delay_le_gfa_rateLatency` /
`backlog_le_gfa_rateLatency`. -/
alias gfa_end_to_end_delay := delay_le_gfa_rateLatency

@[inherit_doc gfa_end_to_end_delay]
alias gfa_end_to_end_backlog := backlog_le_gfa_rateLatency

/-- **Theorem 7** (§10.4.3, p.250): GFA refines SFA: when the grouped aggregate η⁽ʰ⁾ ≤ ∑_{j≠i}αⱼ⁽ʰ⁾ at every server, the GFA end-to-end service curve dominates the SFA one (residual antitone in subtracted aggregate, path convolution monotone). -/
alias alg_7_gfa_dominates_sfa := concatConv_residualCurve_sfa_le_gfa

/-- **Example 10.6** (§10.4.3, p.249): GFA worked on Figure 10.6 with flow 2 the flow of interest: arc-wise grouping of cross-traffic, the grouped arrival/service curves η and β̃ at each server. -/
alias ex_10_6 := DeepWiki.isMinimalServiceCurve_concatConv_groupResidual

/-- **Example 10.1** (§10.3, p.250, loss of tightness): on the non-nested tandem (flow of interest on
all 3 servers, cross-flows on `{1,2}` and `{2,3}`), the PMOO and separated-flow (SFA) end-to-end
service curves are INCOMPARABLE — they share the rate `R−r₂−r₃` but neither latency uniformly
dominates over the parameter family, so neither analysis is uniformly tighter. The citable `¬∀` pair
`DeepWiki.{not_forall_pmooCurve_le_sfaCurve, not_forall_sfaCurve_le_pmooCurve}`. -/
theorem ex_10_1_incomparable :
    (¬ ∀ R T r₂ b₂ r₃ b₃ t, DeepWiki.pmooCurve R T r₂ b₂ r₃ b₃ t
        ≤ DeepWiki.sfaCurve R T r₂ b₂ r₃ b₃ t)
      ∧ (¬ ∀ R T r₂ b₂ r₃ b₃ t, DeepWiki.sfaCurve R T r₂ b₂ r₃ b₃ t
        ≤ DeepWiki.pmooCurve R T r₂ b₂ r₃ b₃ t) :=
  ⟨DeepWiki.not_forall_pmooCurve_le_sfaCurve, DeepWiki.not_forall_sfaCurve_le_pmooCurve⟩

/-- **Example 10.2** (§10.3, p.251, SP-PMOO on the Figure 10.1 nested tandem): the peel-from-inside
recursion `β̃₁ = β⁽²⁾`, `β̃₂ = β⁽¹⁾ ∗ [β⁽²⁾−α₁]⁺↑`, `β̃₃ = [β̃₂−α₂]⁺↑ ∗ β⁽³⁾`. For identical
rate-latency servers `β_{R,T}` and affine inner arrivals, the end-to-end `β̃₃` is rate-latency with
bottleneck rate `R−r₁−r₂` (`nestedBeta₃_rateLatency`; `β̃₂` is `nestedBeta₂_rateLatency`). The library's
`DeepWiki.nestedBeta₃_rateLatency`. -/
theorem ex_10_2 (R T r₁ b₁ r₂ b₂ : ℝ≥0) (hR : r₁ < R) (hR₂ : r₂ < R - r₁) :
    DeepWiki.nestedBeta₃ (rateLatency R T) (rateLatency R T) (rateLatency R T)
        (fun t => r₁ * t + b₁) (fun t => r₂ * t + b₂)
      = rateLatency (DeepWiki.nestedBeta₃Rate R r₁ r₂) (DeepWiki.nestedBeta₃Latency R T r₁ b₁ r₂ b₂) :=
  DeepWiki.nestedBeta₃_rateLatency R T r₁ b₁ r₂ b₂ hR hR₂

/-- **Theorem 10.2** (§10.5, p.255): computing exact worst-case backlog/delay in a feed-forward network
with arbitrary multiplexing is NP-hard (X3C reduction, Figure 10.7). The combinatorial CORE is
formalized — over an X3C instance (3-element subsets of a `3q`-set), the reduction's saturated subsets
are member-disjoint and the optimum `saturatedCount ≤ q` (`X3CInstance.saturatedCount_le_q`), reaching
`q` **iff** an exact 3-cover exists (`X3CInstance.saturatedCount_eq_q_iff_exists_cover` — the
"feasible bound ⟺ exact cover" correspondence). The full NP-hardness wrapper (a poly-time-reduction
type class + the network→backlog semantics + the convex-maximization-attains-vertices step) is
`[external]` — Mathlib has no NP-hardness framework. The library's
`DeepWiki.X3CInstance.saturatedCount_eq_q_iff_exists_cover`. -/
theorem thm_10_2_core {ι α : Type*} [DecidableEq ι] [DecidableEq α] [Fintype ι] [Fintype α]
    (I : DeepWiki.X3CInstance ι α) {assign : α → ι} (hassign : I.IsAssignment assign) :
    I.saturatedCount assign = I.q ↔
      ∃ C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) :=
  I.saturatedCount_eq_q_iff_exists_cover hassign

/-- **Theorem 10.2, the reduction correctness** (§10.5): the X3C → worst-case-backlog-decision
polynomial reduction is correct — `(∃ exact 3-cover) ↔ (worst-case backlog at W reaches the threshold
3s−2q)`. The worst-case backlog is the `programOptimum` of the convex objective over integral vertices,
`worstCaseBacklog = ⨆_assign 3(s−q)+saturatedCount` (≤ 3s−2q, `satOptimum_le_q`), and the decision
`reduceToDecision` carries (value, threshold) with `reduceToDecision_correct`. This is the formalizable
NP-hardness content (a correct poly-time reduction from X3C); the full `NPHard` typeclass (no Mathlib
complexity framework) and the network-dynamics→backlog realization (the convex-maximization-attains-
integral-vertices analysis step) are `[external]`. The library's
`DeepWiki.X3CInstance.threshold_le_worstCaseBacklog_iff_exists_cover` (+ `reduceToDecision_correct`).
NB the book's backlog is `3(s−q)+saturatedCount` (INCREASING in the maximized saturation), reaching
`3s−2q` exactly when a cover exists. -/
theorem thm_10_2_reduction {ι α : Type*} [DecidableEq ι] [DecidableEq α] [Fintype ι] [Fintype α]
    (I : DeepWiki.X3CInstance ι α) (hne : I.HasAssignment) (hsq : I.q ≤ I.numSubsets) :
    3 * I.numSubsets - 2 * I.q ≤ I.worstCaseBacklog ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) :=
  I.threshold_le_worstCaseBacklog_iff_exists_cover hne hsq

/-- **Theorem 10.2, network-served realization** (§10.5): the threshold correspondence holds for the
ACTUAL network backlog computed from the Figure-10.7 served rate equations (not just the abstract
objective). At an integral routing the backlog at the bottom server `W` at time `1⁻` is
`3(s−q)+saturatedCount` (`backlogAtW_eq_backlogValue`, real arithmetic over the upper/middle served
totals), so the worst case over integral routings is `worstCaseBacklog`
(`worstCaseBacklogAtW_eq`) and `3s−2q ≤ network-backlog ⟺ exact 3-cover`
(`threshold_le_worstCaseBacklogAtW_iff_exists_cover`). The library's
`DeepWiki.X3CInstance.threshold_le_worstCaseBacklogAtW_iff_exists_cover`. (Residual above the
served-equation layer: continuous-time rate→`Curve` integration with the `t→1⁻` left-limit `[infra]`;
fractional-vs-integral routing optimality — a finite convex-maximization-on-a-polytope fact `[research]`;
the `NPHard` typeclass `[external]`.) -/
theorem thm_10_2_network {ι α : Type*} [DecidableEq ι] [DecidableEq α] [Fintype ι] [Fintype α]
    (I : DeepWiki.X3CInstance ι α) (hne : I.HasAssignment) (hsq : I.q ≤ I.numSubsets) :
    3 * I.numSubsets - 2 * I.q ≤ I.worstCaseBacklogAtW ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) :=
  I.threshold_le_worstCaseBacklogAtW_iff_exists_cover hne hsq

/-- **Theorem 10.2, fractional-routing optimality** (§10.5): no FRACTIONAL fluid routing beats the
integral vertices — every feasible routing `r : α → ι → ℝ` (nonneg, supported on the containing
subsets, `Σᵢ rₑᵢ = 1`) has objective `fracObjective r ≤ q` (`fracObjective_le_q_of_feasible`). Proof:
`fracObjective` is convex (`convexOn_fracObjective`, `[·−2]⁺` sums), the polytope is the convex hull of
the integral routings (`convexHull_pi`), and a convex function is maximized at a vertex
(`ConvexOn.le_sup_of_mem_convexHull`), each vertex giving `saturatedCount ≤ q`. This closes the
convex-maximization step over ALL routings (no fractional advantage). The library's
`DeepWiki.X3CInstance.fracObjective_le_q_of_feasible`. -/
theorem thm_10_2_fractional {ι α : Type*} [DecidableEq ι] [DecidableEq α] [Fintype ι] [Fintype α]
    (I : DeepWiki.X3CInstance ι α) {r : α → ι → ℝ} (hr : I.IsFeasible r) :
    I.fracObjective r ≤ (I.q : ℝ) :=
  I.fracObjective_le_q_of_feasible hr

/-- **Theorem 10.2, continuous-time realization** (§10.5): the rate-based worst-case `W`-backlog is a
genuine continuous-time trajectory. With capped-ramp cumulatives `A_W = a·min(t,1)`, `D_W = d·min(t,1)`
(`rampCapped`, continuous + left-continuous + null-at-origin) and net rate `a − d = backlogAtW`, the
served-pair backlog `Deviation.backlog A_W D_W = backlogAtW` (`backlog_trajectory_eq_backlogAtW`) and
its instantaneous value at `t→1⁻` tends to `backlogAtW` (`tendsto_backlogAt_trajectory_backlogAtW`).
This closes the continuous-time rate→`Curve` integration layer. The library's
`DeepWiki.X3CInstance.backlog_trajectory_eq_backlogAtW`. -/
theorem thm_10_2_trajectory {ι : Type*} {αT : Type*} [DecidableEq ι] [DecidableEq αT] [Fintype ι]
    [Fintype αT] (I : DeepWiki.X3CInstance ι αT) {assign : αT → ι} {a d : ℝ≥0} (hda : d ≤ a)
    (hrate : a - d = (I.backlogAtW assign : ℝ≥0)) :
    Deviation.backlog (DeepWiki.rampCapped a) (DeepWiki.rampCapped d)
      = ((I.backlogAtW assign : ℝ≥0) : ℝ≥0∞) :=
  I.backlog_trajectory_eq_backlogAtW hda hrate

end DeepWiki.Dnc
