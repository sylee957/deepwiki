import DeepWiki.NetworkCalculus.WorstCaseLP
import DeepWiki.NetworkCalculus.WorstCaseLPFifoNode
import DeepWiki.NetworkCalculus.WorstCaseLPArbMuxNode
import DeepWiki.NetworkCalculus.WorstCaseLPBacklog
import DeepWiki.NetworkCalculus.WorstCaseLPInstance
import DeepWiki.NetworkCalculus.WorstCaseLPTandem
import DeepWiki.NetworkCalculus.WorstCaseLPTandemChain
import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainRateLatency
import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainBridge
import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainExact
import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainExactWindowed
import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainExactWindowedReindex
import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainExactReorder
import DeepWiki.NetworkCalculus.WorstCaseLPTandemBacklog
import DeepWiki.NetworkCalculus.TandemLinearProgram
import DeepWiki.NetworkCalculus.TandemFifoMilp
import DeepWiki.NetworkCalculus.TandemWorstCaseExamples
import DeepWiki.NetworkCalculus.TandemLinearProgramWitness
import DeepWiki.NetworkCalculus.TandemFifoMilpWitness
import Sources.Doi_10_1002_9781119440284.Source

/-! # DNC catalog — Chapter 11: Tight Worst-case Performances
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
§11.1: Example 11.1 (two-server tandem worked delay bound) is `ex_11_1`. Remark 11.1 / Table 11.1 (the finite tandem LP construction) is now done as DATA + soundness (`table_11_1`/`thm_11_1_sound`: the general `n`-server LP variables+constraints, feasibility ⟹ delay ≤ objective); the exact worst-case end-to-end delay is now formalized in closed form for ANY rate-latency tandem:
`(∑ₕTₕ) + b/(minₕRₕ)` (`thm_11_1_exact`/`worstCaseChainDelay_tokenBucketNN_rateLatencyNN`, via the PMOO
chain convolution). The §11.1.2 LP (`thm_11_1_optimum`) is the SFA RELAXATION `(RT+b)/(R−r)` — its
optimum is attained as the LP value (homogeneous via `tandemWitness`) but STRICTLY over-estimates the
true worst case for `r>0` (`thm_11_1_relaxation_gap`/`worstCaseChainDelay_lt_programOptimum`, equal iff
`r=0`). The EXACT relaxation-free LP is built (`thm_11_1_exact_lp`/`exactChainOptimum`/
`programOptimum_exactServer`: optimum `(∑T)+b/(minR)` for all `r`, via the date-split polytope the SFA LP
dropped) AND in genuine per-server-WINDOWED form (`thm_11_1_exact_lp_windowed`/`programOptimum_windowed
_last`: one date/window per server, optimum `(∑Tₕ)+b/(R_bottleneck)`, n=2 bridged to `exactChainOptimum`).
The general-n windowed→analytic bridge is proved under the bottleneck-last hypothesis
(`thm_11_1_exact_lp_windowed_bridge`/`programOptimum_windowed_last_eq_exactChainOptimum`: windowed-last
optimum = `exactChainOptimum`, ANY n). The ARBITRARY-ORDER case is now also handled
(`thm_11_1_exact_reorder`/`chainValue_perm`: the exact worst case `(∑T)+b/(minR)` is permutation-
invariant — depends only on the server multiset — and `exists_perm_programOptimum_windowed_eq_exact
ChainOptimum` relabels the bottleneck last). NB the in-place windowed-last identity stays order-DEPENDENT
(`b/R_last` vs `b/minR`); the manifestly order-independent exact LP is the collapsed `thm_11_1_exact_lp`.
Ch11's §11.1 LP-optimum-=-worst-case is now COMPLETE (exact value, exact LP in 3 forms, order-independence).
§11.2: Example 11.2 (single FIFO node, closed-form worst-case delay `T+(b₁+b₂)/R`) is `ex_11_2`. Theorem 11.2 general FIFO tandem is now done as DATA + soundness (`lemma_11_1_1` big-M order encoding, `thm_11_2_sound`: the FIFO MILP = arbitrary-mux tandem LP + per-server big-M FIFO ordering, feasibility ⟹ delay ≤ objective, FIFO optimum ≤ arbitrary-mux optimum); the MILP optimum = worst case is now done for the HOMOGENEOUS tandem (`thm_11_2_optimum`/`fifoTandem_programOptimum_homogeneous`, the `z=0` lifted witness); residual `[infra]`/`[research]`: the general heterogeneous case (SFA objective not tight) + the exponential binary-tree multi-flow layout (`Fᵢ^{(h)}`/`pᵢ`/`Fl(h)`) with the §11.2.2 trajectory-from-solution reconstruction over the `2^?` Boolean orderings (an extremal/existence argument, not a closed form). The book defers this exact general case to **[BOU 16b]** (Bouillard–Stea, DOI 10.1109/TNET.2014.2332071) — now formalized from the paper itself (`FifoFeedForwardExact`: Theorem 1 = Lemmas 2/3 logical bridge, the §IV.D LP bracket `v_LP ≤ WCD ≤ V_LP`, the `2^(N+1)−1` variable count, single/multi-node exact instances). The CONCRETE general-N construction is also now formalized one layer below the abstract bridge (`FifoFeedForwardConcrete`: the depth-N binary-tree date layout `DateTree` with `count=2^(N+1)−1`, the `Scenario` properties 1–3, Lemma 2's per-constraint sample discharges `Scenario.sample_feasible_pointwise`, and Lemma 3's min-plus extrapolation core `extrapolate`/`extrapolate_arrival`); Lemma 1 (the convolution-time attainment the backward recursion needs) is now PROVED
(`FifoFeedForwardReconstruction.exists_serviceCurveTime`), and the single-node case has a CONCRETE full
Theorem-1 round-trip via an actual admissible burst trajectory (`fifoNode_reconstruction`, no Boolean
variables). Only the genuinely solver-dependent general-N residual stays scoped — Lemma 2's backward
date recursion composed over the `2^(N+1)−1` `DateTree`, and Lemma 3's global monotonicity/left-continuity
+ FIFO-order preservation across the `2^?` orderings (`[infra]`/`[research]`). Paper-side
double-reference catalog: `Sources/Doi_10_1109_TNET_2014_2332071` (`DeepWiki.Bs.*`). -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-- **Worst-case value as a program optimum** (the `obj`-over-`Feasible`
supremum underlying §11.1.2's LP). The library's `programOptimum`. -/
noncomputable def def_11_optimum := @programOptimum

/-- **Theorem 11.1** (§11.1.3, p.261), worst-case = optimum (arbitrary
multiplexing): the worst-case end-to-end delay (resp. backlog) is the
`programOptimum` of the delay (resp. backlog) over the feasible trajectories —
its least upper bound (`isLUB_programOptimum`): an upper bound on every
realizable value and the tightest one. (That this optimum is computed by the
finite O(nm)-variable LP of §11.1.2 is the modeling content, not formalized.) -/
theorem thm_11_1 {ι : Type*} (Feasible : ι → Prop) (obj : ι → EReal) :
    IsLUB (Set.range fun c : {c // Feasible c} => obj c.1)
      (programOptimum Feasible obj) :=
  isLUB_programOptimum Feasible obj

/-- **Theorem 11.1, single-node instance** (§11.1/§11.2.1) — the *genuine*
optimum-equals-worst-case for one server: the worst-case delay
`worstCaseServerDelay α β` (the supremum of the delay over all feasible
`α`-arrival-constrained, `β`-served trajectories — the single-node program
optimum) equals the closed-form horizontal deviation `hDev(α, β)`. Proven by
the upper bound `delay ≤ hDev` on every feasible trajectory and the greedy pair
`(α, α∗β)` attaining it. (For one node the program optimum is the curve bound;
the multi-server LP of §11.1.2, where the optimum is strictly below the
curve-composition bound, is the part that needs the finite-LP construction.) -/
theorem thm_11_1_singleNode {α : ℝ≥0 → ℝ≥0} {β : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) (hα0 : IsNullAtOrigin α) (hαsub : IsSubadditive α)
    (hβmono : Monotone β) (hβ0 : β 0 = 0) :
    worstCaseServerDelay α β = (hDev (Deviation.liftENN α) β : ℝ≥0∞) :=
  worstCaseServerDelay_eq_hDev hαmono hα0 hαsub hβmono hβ0

/-- **Theorem 11.1, single-node backlog form** (§11.1/§11.2.1, the "resp. backlog"):
the worst-case backlog `worstCaseServerBacklog α β` (the optimum of the backlog
over all feasible trajectories) equals the closed-form vertical deviation
`vDev(α, β)`. The bound `b ≤ vDev` holds on every feasible trajectory and the
greedy pair `(α, α∗β)` attains it. The library's `worstCaseServerBacklog_eq_vDev`. -/
theorem thm_11_1_singleNode_backlog {α : ℝ≥0 → ℝ≥0} {β : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) (hα0 : IsNullAtOrigin α) (hαsub : IsSubadditive α)
    (hβ0 : β 0 = 0) :
    worstCaseServerBacklog α β = (vDev (Deviation.liftENN α) β : ℝ≥0∞) :=
  worstCaseServerBacklog_eq_vDev hαmono hα0 hαsub hβ0

/-- **Theorem 11.1, two-node single-flow specialization** (§11.1.3, n=2) — the
optimum-equals-worst-case for a *single* flow through two servers in series: the
worst-case end-to-end delay `worstCaseTandemDelay α β₁ β₂` (the optimum over all
feasible tandem trajectories) equals the closed-form `hDev(α, β₁ ∗ β₂)` against
the concatenated service curve. The service constraints collapse by `minConv`
associativity to a single concatenated server, and the greedy trajectory
`(α, α∗β₁, α∗(β₁∗β₂))` attains the bound. The library's
`worstCaseTandemDelay_eq_hDev_conv`. (Single flow, no cross-traffic — here the
concatenation `β₁ ∗ β₂` is already tight; the *multi-flow* tandem of Example 11.1
under arbitrary multiplexing, where the LP optimum is strictly below the
curve-composition bound, needs the finite-LP construction and is not formalized.) -/
theorem thm_11_1_tandem {α : ℝ≥0 → ℝ≥0} {β₁ β₂ : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) (hα0 : IsNullAtOrigin α) (hαsub : IsSubadditive α)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂) (hβ₁0 : β₁ 0 = 0) (hβ₂0 : β₂ 0 = 0) :
    worstCaseTandemDelay α β₁ β₂ = (hDev (Deviation.liftENN α) (minConv β₁ β₂) : ℝ≥0∞) :=
  worstCaseTandemDelay_eq_hDev_conv hαmono hα0 hαsub hβ₁mono hβ₂mono hβ₁0 hβ₂0

/-- **Theorem 11.1, n-server single-flow specialization** (§11.1.3, arbitrary path
length) — the worst-case end-to-end delay of a single flow through a tandem of
servers `β₀ :: βs` (`worstCaseChainDelay`, the optimum over all feasible chain
trajectories) equals the closed-form `hDev(α, β₀ ∗ β₁ ∗ ⋯)` against the chain
convolution. The per-hop service constraints collapse inductively (by `minConv`
associativity) to one concatenated server; the greedy chain attains the bound. The
library's `worstCaseChainDelay_eq_hDev_minConvChain` (recovers `thm_11_1_singleNode`
at `βs = []` and `thm_11_1_tandem` at `βs = [β₂]`). (Single flow, no cross-traffic;
the multi-flow strict improvement of §11.1 needs the finite-LP construction and is
not formalized.) -/
theorem thm_11_1_chain {α : ℝ≥0 → ℝ≥0} {β₀ : ℝ≥0 → ℝ≥0∞} {βs : List (ℝ≥0 → ℝ≥0∞)}
    (hαmono : Monotone α) (hα0 : IsNullAtOrigin α) (hαsub : IsSubadditive α)
    (hβ₀mono : Monotone β₀) (hβsmono : ∀ γ ∈ βs, Monotone γ)
    (hβ₀0 : β₀ 0 = 0) (hβs0 : ∀ γ ∈ βs, γ 0 = 0) :
    worstCaseChainDelay α β₀ βs = (hDev (Deviation.liftENN α) (minConvChain β₀ βs) : ℝ≥0∞) :=
  worstCaseChainDelay_eq_hDev_minConvChain hαmono hα0 hαsub hβ₀mono hβsmono hβ₀0 hβs0

/-- **Theorem 11.1, n-server tandem backlog form** — the worst-case end-to-end
backlog (total in-flight data) of a single flow through the tandem `β₀ :: βs`,
`worstCaseChainBacklog`, equals the vertical deviation `vDev(α, β₀ ∗ β₁ ∗ ⋯)`
against the chain convolution. The library's
`worstCaseChainBacklog_eq_vDev_minConvChain`. -/
theorem thm_11_1_chain_backlog {α : ℝ≥0 → ℝ≥0} {β₀ : ℝ≥0 → ℝ≥0∞} {βs : List (ℝ≥0 → ℝ≥0∞)}
    (hαmono : Monotone α) (hα0 : IsNullAtOrigin α) (hαsub : IsSubadditive α)
    (hβ₀0 : β₀ 0 = 0) (hβs0 : ∀ γ ∈ βs, γ 0 = 0) :
    worstCaseChainBacklog α β₀ βs = (vDev (Deviation.liftENN α) (minConvChain β₀ βs) : ℝ≥0∞) :=
  worstCaseChainBacklog_eq_vDev_minConvChain hαmono hα0 hαsub hβ₀0 hβs0

/-- **Worked instance of Theorem 11.1 on the canonical curves** (§11.2.1): the
worst-case delay of a token-bucket flow `γ_{r,b}` (`r ≤ R`) through a rate-latency
server `β_{R,T}` (`R > 0`, `b > 0`), over *all* feasible trajectories, is exactly
the textbook bound `T + b/R` — the optimum is attained, not just bounded. The
library's `worstCaseServerDelay_tokenBucketNN_rateLatencyNN`. -/
theorem example_11_tokenBucketRateLatency (r b R T : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hrR : r ≤ R) :
    worstCaseServerDelay (tokenBucketArrival r b) (rateLatencyNN R T)
      = ((T + b / R : ℝ≥0) : ℝ≥0∞) :=
  worstCaseServerDelay_tokenBucketNN_rateLatencyNN r b R T hR hb hrR

/-- **Worked instance, backlog form** (§11.2.1): the worst-case backlog of the same
`γ_{r,b}` flow (`r ≤ R`, `T > 0`) through `β_{R,T}`, over all feasible trajectories,
is exactly `r·T + b`. The library's `worstCaseServerBacklog_tokenBucketNN_rateLatencyNN`. -/
theorem example_11_tokenBucketRateLatency_backlog (r b R T : ℝ≥0)
    (hrR : r ≤ R) (hT : 0 < T) :
    worstCaseServerBacklog (tokenBucketArrival r b) (rateLatencyNN R T)
      = ((r * T + b : ℝ≥0) : ℝ≥0∞) :=
  worstCaseServerBacklog_tokenBucketNN_rateLatencyNN r b R T hrR hT

/-- **Worked instance, two-server tandem** (§11.1.1): the canonical end-to-end
worst-case delay of a `γ_{r,b}` flow through two rate-latency servers in series,
`β_{R₁,T₁}` then `β_{R₂,T₂}` (`R₁,R₂ > 0`, `b > 0`, `r ≤ R₁,R₂`), is exactly
`T₁ + T₂ + b/(R₁ ⊓ R₂)`. The library's
`worstCaseTandemDelay_tokenBucketNN_rateLatencyNN`. -/
theorem example_11_tokenBucketRateLatency_tandem (r b R₁ T₁ R₂ T₂ : ℝ≥0)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hb : 0 < b) (hr₁ : r ≤ R₁) (hr₂ : r ≤ R₂) :
    worstCaseTandemDelay (tokenBucketArrival r b) (rateLatencyNN R₁ T₁) (rateLatencyNN R₂ T₂)
      = ((T₁ + T₂ + b / (R₁ ⊓ R₂) : ℝ≥0) : ℝ≥0∞) :=
  worstCaseTandemDelay_tokenBucketNN_rateLatencyNN r b R₁ T₁ R₂ T₂ hR₁ hR₂ hb hr₁ hr₂

/-- **Worked instance, two-server tandem backlog** (§11.1.1): the end-to-end
worst-case backlog (total in-flight data) of the same `γ_{r,b}` flow through
`β_{R₁,T₁}` then `β_{R₂,T₂}` (`r ≤ R₁,R₂`, `0 < T₁+T₂`) is exactly `r·(T₁+T₂) + b`.
The library's `worstCaseChainBacklog_tokenBucketNN_two_rateLatencyNN`. -/
theorem example_11_tokenBucketRateLatency_tandem_backlog (r b R₁ T₁ R₂ T₂ : ℝ≥0)
    (hr₁ : r ≤ R₁) (hr₂ : r ≤ R₂) (hT : 0 < T₁ + T₂) :
    worstCaseChainBacklog (tokenBucketArrival r b) (rateLatencyNN R₁ T₁) [rateLatencyNN R₂ T₂]
      = ((r * (T₁ + T₂) + b : ℝ≥0) : ℝ≥0∞) :=
  worstCaseChainBacklog_tokenBucketNN_two_rateLatencyNN r b R₁ T₁ R₂ T₂ hr₁ hr₂ hT

/-- **Table 11.1** (§11.1.1, p.259): the explicit linear program for the worst-case delay of one
server under *arbitrary (blind) multiplexing*, crossed by two token-bucket flows `γ_{bᵢ,rᵢ}` under
a strict rate-latency curve `β_{R,T}` — the feasible set over the dates `t₀≤u≤t₁` and sampled
cumulative values, with the monotonicity, backlogged-start, causality, arrival, aggregate-service
and `u`-insertion constraints (no FIFO coupling). The library's `ArbMuxNodeFeasible`. -/
abbrev table_11_1_singleNode := @DeepWiki.ArbMuxNodeFeasible

/-- **Theorem 11.1, single node under arbitrary multiplexing** (§11.1.3, p.261): the optimum of
the Table 11.1 program (n=1) equals `(R·T+b₁+b₂)/(R−r₂)`, the exact worst-case blind-multiplexing
delay of the tagged flow 1 — its residual-service delay `hDev(γ_{b₁,r₁}, β_{R,T} ⊖ γ_{b₂,r₂})`.
The aggregate burst `b₁+b₂` is cleared at the residual rate `R−r₂` (cross traffic can be served
ahead of the tagged bit), so the LP optimum is *larger* than the FIFO `T+(b₁+b₂)/R`. Both bounds
are linear arithmetic on the program variables. The library's `arbMuxNode_programOptimum`. -/
alias thm_11_1_arbMuxNode := DeepWiki.arbMuxNode_programOptimum

/-- **§11.1.2, backlog objective** (p.260–261): the single-server program with the aggregate
backlog objective `max ∑(Aᵢ−Dᵢ)(t₁)` has optimum `(b₁+b₂)+(r₁+r₂)·T`, the aggregate vertical
deviation `vDev(γ_{b₁+b₂,r₁+r₂}, β_{R,T})` (policy-independent). The library's
`arbMuxNodeBacklog_programOptimum`. -/
alias thm_11_1_arbMuxNode_backlog := DeepWiki.arbMuxNodeBacklog_programOptimum

/-- **Lemma 11.1** (§11.2.2, p.264): the big-M Boolean ordering linearizing the
FIFO date order — given the four big-M constraints and `b ∈ {0,1}`,
`x₁<x₂ ⟹ b=0 ∧ y₁≤y₂` and `x₂<x₁ ⟹ b=1 ∧ y₂≤y₁`. The library's `bigM_ordering`. -/
alias lemma_11_1 := bigM_ordering

/-- **Lemma 11.1, boxed equivalence** (§11.2.2, p.264): the full content — with values boxed in
`[0,M]`, the four big-M constraints are *equivalent* to the selector `b` consistently ordering both
pairs (`b=0 → x₁≤x₂ ∧ y₁≤y₂`, `b=1 → x₂≤x₁ ∧ y₂≤y₁`), so the linearization is faithful, not merely
sound. The library's `bigM_ordering_iff`. -/
alias lemma_11_1_boxed := DeepWiki.bigM_ordering_iff

/-- **Table 11.2** (§11.2.1, p.263): the explicit linear program for the worst-case delay of one
FIFO server crossed by two token-bucket flows `γ_{bᵢ,rᵢ}` under a rate-latency curve `β_{R,T}` —
the feasible set over the dates `t₁≥t₂≥t₃` and sampled cumulative values, with the monotonicity,
arrival, service and FIFO (`Dᵢ(t₁)=Aᵢ(t₂)`) constraints. The library's `FifoNodeFeasible`. -/
abbrev table_11_2 := @DeepWiki.FifoNodeFeasible

/-- **Theorem 11.2, single FIFO node** (§11.2.1–11.2.2, p.263–265): the optimum of the Table 11.2
program equals `T + (b₁+b₂)/R`, the exact worst-case FIFO delay of the aggregate. Both bounds are
linear arithmetic on the program variables (the `≤` from the constraints, the `≥` from an explicit
feasible point), so the finite LP itself — not just its abstract optimum — computes the worst case.
The library's `fifoNode_programOptimum`. -/
alias thm_11_2_fifoNode := DeepWiki.fifoNode_programOptimum

/-- **§11.2.3 upper bound** (p.267): relaxing the MILP by dropping the Boolean variables enlarges
the feasible set, so the relaxed LP's optimum is a (polynomial-time) upper bound on the worst-case
delay. The library's `milpOptimum_le_relaxationOptimum`. -/
alias bound_11_2_3_upper := DeepWiki.milpOptimum_le_relaxationOptimum

/-- **§11.2.3 lower bound** (p.267): adding date-merging equality constraints shrinks the feasible
set, so the reduced LP's optimum is a (polynomial-time) lower bound on the worst-case delay. The
library's `reducedOptimum_le_milpOptimum`. -/
alias bound_11_2_3_lower := DeepWiki.reducedOptimum_le_milpOptimum

/-- **Table 11.1 / §11.1.2** the general `n`-server tandem LP as DATA: variables `TandemLP.Vars`
(boundary dates `t₀ ≥ ⋯ ≥ tₙ` + aggregate cumulatives sampled at them) and the linear constraints
`TandemLP.Feasible` (date ordering, cumulative monotonicity, token-bucket arrival at the source,
per-server rate-latency strict service, flow conservation across boundaries), over the network data
`TandemLP.Tandem`. The library's `DeepWiki.TandemLP.{Tandem,Vars,Feasible}`. -/
abbrev table_11_1 := @DeepWiki.TandemLP.Feasible

/-- **Theorem 11.1 / §11.1.3, soundness** (the representable half): a feasible point of the tandem LP
has its end-to-end delay bounded by the LP objective `(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)`
(`delay_le_objectiveValue`) — every feasible LP point is a valid worst-case scenario, so the objective
upper-bounds the realized delay (`TandemLP.delay = ∑ₕ windowₕ` telescoping + the bottleneck inequality).
The library's `DeepWiki.TandemLP.delay_le_objectiveValue`. (The optimization half — LP optimum EQUALS
the worst case — is the extremal/existence content needing a solver, not a closed-form Lean lemma; the
multi-flow routing and the Thm 11.2 FIFO MILP Boolean date-orderings are likewise not built.) -/
theorem thm_11_1_sound {n : ℕ} {N : DeepWiki.TandemLP.Tandem n} {v : DeepWiki.TandemLP.Vars n}
    (hv : DeepWiki.TandemLP.Feasible N v) {Rmin : ℝ} (hRmin : ∀ h : Fin n, Rmin ≤ N.rate h)
    (hstab : N.rate0 < Rmin) :
    DeepWiki.TandemLP.delay v ≤ DeepWiki.TandemLP.objectiveValue N Rmin :=
  DeepWiki.TandemLP.delay_le_objectiveValue hv hRmin hstab

/-- **Lemma 11.1.1** (§11.2, p.263), the big-M order encoding `x ≤_b y`: a Boolean `b ∈ {0,1}` with the
constraint pair `x + (1−b)M ≥ y`, `y + bM ≥ x` (dates boxed in `[0,M]`) encodes the order disjunction —
`bigMOrder_iff : (the big-M pair) ↔ ((b=0 → x ≤ y) ∧ (b=1 → y ≤ x))`. The library's
`DeepWiki.TandemFifo.{BigMOrder, bigMOrder_iff}`. -/
theorem lemma_11_1_1 {M x y b : ℝ} (hxge0 : 0 ≤ x) (hxleM : x ≤ M) (hyge0 : 0 ≤ y) (hyleM : y ≤ M)
    (hb : b = 0 ∨ b = 1) :
    (x + (1 - b) * M ≥ y ∧ y + b * M ≥ x) ↔ ((b = 0 → x ≤ y) ∧ (b = 1 → y ≤ x)) :=
  DeepWiki.TandemFifo.bigMOrder_iff hxge0 hxleM hyge0 hyleM hb

/-- **Theorem 11.2 / §11.2** (general FIFO tandem), the representable half: the FIFO tandem MILP as DATA
+ soundness. `TandemFifo.FifoFeasible` extends the arbitrary-mux tandem LP (`TandemLP.Feasible`) with a
per-server Boolean date-ordering selector `z` constrained by the Lemma-11.1.1 big-M encoding (FIFO: an
earlier-arriving bit departs earlier). FIFO is a restriction of arbitrary-mux (`FifoFeasible.feasible`),
so a FIFO-feasible point's delay is bounded by the §11.1 objective (`thm_11_2_sound`/
`fifoDelay_le_objectiveValue`), and the FIFO MILP optimum is below the arbitrary-mux LP optimum
(`fifoOptimum_le_arbMuxOptimum`, §11.2.3). The library's `DeepWiki.TandemFifo.*`. (Solver-dependent
residual `[infra]`: the exponential binary-tree multi-flow layout `Fᵢ^{(h)}`/`pᵢ`/`Fl(h)`, and the
MILP-optimum = worst-case `≥` direction — the §11.2.2 trajectory-from-solution reconstruction over the
`2^?` Boolean orderings, an extremal/existence argument, not a closed form.) -/
theorem thm_11_2_sound {n : ℕ} {N : DeepWiki.TandemLP.Tandem n} {M : ℝ}
    {v : DeepWiki.TandemFifo.FifoVars n} (hv : DeepWiki.TandemFifo.FifoFeasible N M v) {Rmin : ℝ}
    (hRmin : ∀ h : Fin n, Rmin ≤ N.rate h) (hstab : N.rate0 < Rmin) :
    DeepWiki.TandemFifo.fifoDelay v ≤ DeepWiki.TandemLP.objectiveValue N Rmin :=
  DeepWiki.TandemFifo.fifoDelay_le_objectiveValue hv hRmin hstab

/-- **Theorem 11.2, FIFO-MILP optimum = worst case** (§11.2.2) for the HOMOGENEOUS-rate tandem: the
FIFO MILP optimum is attained, `programOptimum (FifoFeasible N M) fifoDelay = objectiveValue N Rmin`
(any n, for `M` ≥ the witness window-sum), via the worst-case vertex `TandemLP.tandemWitness` lifted to
`FifoVars` with the all-zero Boolean ordering `z=0` (on the monotone-date vertex every FIFO ordering
collapses to `z=0`, so attainment is a finite computation). The library's
`DeepWiki.TandemFifo.fifoTandem_programOptimum_homogeneous`. ★ Note the n=1 tandem-LP FIFO model (SFA
`(RT+b)/(R−r)`) is DISTINCT from the Table 11.2 two-flow node (tight `T+(b₁+b₂)/R`, `ex_11_2`/
`fifoNode_programOptimum`) — strict gap `objectiveValue_one_gt_tight`. Residual `[infra]`/`[research]`:
the general heterogeneous case (SFA not tight) + the exponential `2^?` Boolean-ordering
trajectory-from-solution reconstruction (§11.2.2). -/
theorem thm_11_2_optimum {n : ℕ} (N : DeepWiki.TandemLP.Tandem (n + 1)) {Rmin M : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0) (hrate : ∀ h : Fin (n + 1), N.rate h = Rmin)
    (hlat : ∀ h : Fin (n + 1), 0 ≤ N.lat h) (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin)
    (hM : (∑ k : Fin (n + 1), DeepWiki.TandemLP.witnessWindow N Rmin k) ≤ M) :
    programOptimum (DeepWiki.TandemFifo.FifoFeasible N M)
        (fun v => ((DeepWiki.TandemFifo.fifoDelay v : ℝ) : EReal))
      = ((DeepWiki.TandemLP.objectiveValue N Rmin : ℝ) : EReal) :=
  DeepWiki.TandemFifo.fifoTandem_programOptimum_homogeneous N hRmin hrate0 hrate hlat hb hstab hM

/-- **Example 11.2** (§11.2.1, p.263): one FIFO server with two token-bucket flows `γ_{rᵢ,bᵢ}` under
rate-latency `β_{R,T}` (Table 11.2 LP). The worst-case end-to-end delay is the CLOSED-FORM program
optimum `T + (b₁+b₂)/R` (single node ⟹ exact, both bound and attaining witness). The library's
`DeepWiki.TandemWorstCaseExamples.example_11_2_fifo_optimum` (symmetric equal-flow case
`T + 2b/R`). Curves are symbolic (the book gives no figure numerics). -/
theorem ex_11_2 {b₁ b₂ r₁ r₂ R T : ℝ} (hR : 0 < R) (hstab : r₁ + r₂ ≤ R)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hT : 0 ≤ T) :
    programOptimum (FifoNodeFeasible b₁ b₂ r₁ r₂ R T) (fun v => ((fifoNodeDelay v : ℝ) : EReal))
      = ((T + (b₁ + b₂) / R : ℝ) : EReal) :=
  DeepWiki.TandemWorstCaseExamples.example_11_2_fifo_optimum hR hstab hb₁ hb₂ hT

/-- **Example 11.1** (§11.1.1, p.258): the two-server tandem of Figure 10.2 with token-bucket arrivals
`γ_{r,b}` (each flow) and strict rate-latency `β_{R,T}` (each server). The §11.1.3 soundness half: every
feasible Table-11.1 LP point has end-to-end delay `≤ (2RT+2b)/(R−2r)` (aggregating the two `γ_{r,b}`
flows into `γ_{2r,2b}`), under stability `2r < R`. The library's
`DeepWiki.TandemWorstCaseExamples.example_11_1_delay_bound` (objective
`example_11_1_objectiveValue`). The optimum-equals-worst-case direction is the `[infra]` solver half. -/
theorem ex_11_1 {b r R T : ℝ} (hstab : 2 * r < R) {v : TandemLP.Vars 2}
    (hv : TandemLP.Feasible (TandemWorstCaseExamples.example_11_1_tandem b r R T) v) :
    TandemLP.delay v ≤ (2 * (R * T) + 2 * b) / (R - 2 * r) :=
  DeepWiki.TandemWorstCaseExamples.example_11_1_delay_bound hstab hv

/-- **Theorem 11.1, optimum = worst case** (§11.1.3) for a HOMOGENEOUS-rate tandem (`∀h, Rₕ = Rmin`):
the LP optimum is attained — `programOptimum (Feasible N) delay = objectiveValue N Rmin`
(`TandemLP.tandem_programOptimum_homogeneous`, any `n`; specialized `…_one`/`…_two` for the §11.1
example cases) — via a worst-case witness vertex `tandemWitness` (whole source burst as backlog at the
first boundary, cleared at the bottleneck rate). The library's
`DeepWiki.TandemLP.tandem_programOptimum_homogeneous`. ★ For a HETEROGENEOUS tandem the SFA/bottleneck
objective is genuinely NOT the optimum — when a server has `Rₕ > Rmin` and `Tₕ > 0`, attainment would
force a negative backlog (`objectiveValue_not_tight_heterogeneous`: a concrete 2-server witness, rates
1,2 / latencies 0,1, where the bottleneck objective 3 strictly exceeds the exact 3/2); the exact
heterogeneous optimum is the value the finite LP computes (solver) — that vertex remains `[infra]`. -/
theorem thm_11_1_optimum {n : ℕ} (N : TandemLP.Tandem (n + 1)) {Rmin : ℝ} (hRmin : 0 < Rmin)
    (hrate0 : 0 ≤ N.rate0) (hrate : ∀ h : Fin (n + 1), N.rate h = Rmin)
    (hlat : ∀ h : Fin (n + 1), 0 ≤ N.lat h) (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin) :
    programOptimum (TandemLP.Feasible N) (fun v => ((TandemLP.delay v : ℝ) : EReal))
      = ((TandemLP.objectiveValue N Rmin : ℝ) : EReal) :=
  TandemLP.tandem_programOptimum_homogeneous N hRmin hrate0 hrate hlat hb hstab

/-- **The EXACT heterogeneous tandem worst-case delay** (§11.1, the true optimum). For a token-bucket
flow `γ_{r,b}` through a tandem of rate-latency servers `β_{Rₕ,Tₕ}` (ANY rates), the worst-case
end-to-end delay over all feasible trajectories is the closed form `(∑ₕTₕ) + b/(minₕRₕ)` — via the PMOO
chain convolution `β₀∗⋯∗βₙ = β_{minR,∑T}` (`minConvChain_rateLatencyNN`) and
`worstCaseChainDelay_eq_hDev_minConvChain`. The library's
`DeepWiki.worstCaseChainDelay_tokenBucketNN_rateLatencyNN`. ★ This is BELOW the §11.1.2 LP
(`thm_11_1_optimum`/`objectiveValue`), which is the SFA RELAXATION `(RT+b)/(R−r)`: the LP strictly
over-estimates for `r>0` (`worstCaseChainDelay_lt_programOptimum`), coinciding only at `r=0`
(`worstCaseChainDelay_eq_programOptimum_of_rate0`). So the exact worst case is this PMOO value; an
exact finite LP would need the §11.1.3 multi-window reconstruction (`[infra]`). -/
theorem thm_11_1_exact (r b R₀ T₀ : ℝ≥0) (ps : List (ℝ≥0 × ℝ≥0)) (hb : 0 < b)
    (hRmin : 0 < ps.foldr (fun p R => p.1 ⊓ R) R₀) (hrR : r ≤ ps.foldr (fun p R => p.1 ⊓ R) R₀) :
    worstCaseChainDelay (tokenBucketArrival r b) (rateLatencyNN R₀ T₀)
        (ps.map (fun p => rateLatencyNN p.1 p.2))
      = (((T₀ + (ps.map Prod.snd).sum) + b / (ps.foldr (fun p R => p.1 ⊓ R) R₀) : ℝ≥0) : ℝ≥0∞) :=
  DeepWiki.worstCaseChainDelay_tokenBucketNN_rateLatencyNN r b R₀ T₀ ps hb hRmin hrR

/-- **The §11.1.2 LP is a sound relaxation** (the over-estimation gap, made precise). For a single
rate-latency server with token-bucket arrival, the exact worst-case delay `T+b/R` is ≤ the LP optimum
`(RT+b)/(R−r)` (`worstCaseChainDelay_le_programOptimum`), STRICTLY so for `r>0`
(`worstCaseChainDelay_lt_programOptimum`), with equality iff `r=0`. The library's
`DeepWiki.worstCaseChainDelay_lt_programOptimum`. -/
theorem thm_11_1_relaxation_gap (r b R T : ℝ≥0) (hb : 0 < b) (hR : 0 < R) (hr : 0 < r)
    (hstab : r < R) :
    ((worstCaseChainDelay (tokenBucketArrival r b) (rateLatencyNN R T) [] : ℝ≥0∞) : EReal)
      < programOptimum (TandemLP.Feasible (DeepWiki.singleServerTandem r b R T))
          (fun v => ((TandemLP.delay v : ℝ) : EReal)) :=
  DeepWiki.worstCaseChainDelay_lt_programOptimum r b R T hb hR hr hstab

/-- **§11.1.3, the EXACT relaxation-free finite LP** (Theorem 11.1, tight form). The exact tandem LP
optimum equals the true worst-case delay `(∑Tₕ)+b/(minₕRₕ)` — for ALL `r` (including `r>0`, where the
§11.1.2 SFA `TandemLP` strictly over-estimates). Two forms: (a) `exactChainOptimum` = the `programOptimum`
over the full `ChainServed` trajectory set = `worstCaseChainDelay` = the closed form
(`exactChainOptimum_tokenBucketNN_rateLatencyNN`); (b) a genuinely finite-dimensional LP
`ExactServerFeasible` (the §11.1.3 polytope with the date-split `s≤u` charging the token bucket over
`[s,u]` — the constraint the SFA LP dropped) whose optimum is exactly `T+b/R` per server
(`programOptimum_exactServer`), collapsing for the n-server tandem to `(∑T)+b/(minR)`
(`programOptimum_exactServer_collapsed_eq_exactChainOptimum`). The library's
`DeepWiki.{exactChainOptimum, programOptimum_exactServer}`. (Residual `[infra]`: a per-server-windowed
finite encoding for general n — cosmetic; the collapsed encoding is already exact.) -/
theorem thm_11_1_exact_lp (r b R T : ℝ) (hR : 0 < R) (hrR : r ≤ R) (hb : 0 ≤ b) (hT : 0 ≤ T) :
    programOptimum (DeepWiki.ExactServerFeasible r b R T)
        (fun v => ((DeepWiki.exactServerDelay v : ℝ) : EReal))
      = ((T + b / R : ℝ) : EReal) :=
  DeepWiki.programOptimum_exactServer hR hrR hb hT

/-- **§11.1.3, the per-server-WINDOWED exact LP** (the genuine multi-window form). One date/window per
server (`WindowedVars`/`WindowedFeasible`: `n+1` boundary dates, each server's rate-latency
strict-service constraint measured from the common backlog start with prefix-sum latency
`cumLatency`), NOT collapsed before sampling. Its optimum is the exact worst case
`(∑ₕTₕ) + b/(R_{hstar})` at the bottleneck server (`programOptimum_windowed`; bottleneck-last form
`programOptimum_windowed_last`). The non-summation in the rate (`min`, not `∑1/Rₕ`) is genuine: the
windows all measure from the common start `s`, so delay is dominated by the single slowest server.
For n=2 this equals the analytic `exactChainOptimum` (`programOptimum_windowed_two_eq_exactChainOptimum`).
The library's `DeepWiki.programOptimum_windowed_last`. (Residual: the general-n bridge to
`exactChainOptimum` is pure `Fin`↔`List` reindexing plumbing — no further math.) -/
theorem thm_11_1_exact_lp_windowed {n : ℕ} {r b : ℝ} {R T : Fin (n + 1) → ℝ}
    (hRpos : ∀ h, 0 < R h) (hrR : r ≤ R (Fin.last n)) (hb : 0 ≤ b) (hT : ∀ h, 0 ≤ T h) :
    programOptimum (DeepWiki.WindowedFeasible r b R T)
        (fun v => ((DeepWiki.windowedDelay (Fin.last n) v : ℝ) : EReal))
      = ((((∑ h, T h) + b / R (Fin.last n) : ℝ) : EReal)) :=
  DeepWiki.programOptimum_windowed_last hRpos hrR hb hT

/-- **§11.1.3 windowed↔analytic bridge** (general n): the per-server-windowed LP optimum equals the
analytic `exactChainOptimum` of the rate-latency chain — for ANY n, under the **bottleneck-last**
hypothesis `∀ h, R(Fin.last n) ≤ R h` (both `(∑Tₕ)+b/(R_last)`, the `Fin`→`List` reindexing
`sum_eq_head_add_tail` + `foldrInf_rate_eq_last`). Subsumes the n=2 case. The library's
`DeepWiki.programOptimum_windowed_last_eq_exactChainOptimum`. ★ The hypothesis is load-bearing, not
cosmetic: the windowed objective is the delay to the LAST server (`b/R_last`) while `exactChainOptimum`
uses `b/minR`, equal iff the last server is the bottleneck. The UNRESTRICTED (arbitrary-order) identity
is false without a reorder; it needs a `Fin (n+1)` polytope-reindexing `Equiv` on the windowed side
(the analytic side is order-independent by `List.Perm`) — genuine `[infra]`, deferred. -/
theorem thm_11_1_exact_lp_windowed_bridge {n : ℕ} (r b : ℝ≥0) (R T : Fin (n + 1) → ℝ≥0)
    (hb : 0 < b) (hRpos : ∀ h, 0 < R h) (hbot : ∀ h, R (Fin.last n) ≤ R h)
    (hrR : r ≤ R (Fin.last n)) :
    programOptimum
        (DeepWiki.WindowedFeasible (r : ℝ) (b : ℝ) (fun h => (R h : ℝ)) (fun h => (T h : ℝ)))
        (fun v => ((DeepWiki.windowedDelay (Fin.last n) v : ℝ) : EReal))
      = exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN (R 0) (T 0))
          ((List.ofFn (fun i : Fin n => (R i.succ, T i.succ))).map
            (fun p => rateLatencyNN p.1 p.2)) :=
  DeepWiki.programOptimum_windowed_last_eq_exactChainOptimum r b R T hb hRpos hbot hrR

/-- **§11.1.3 arbitrary-order reorder** (the order-independence of the exact tandem worst case). The
exact worst-case delay depends only on the server MULTISET: `chainValue_perm` — for permuted server
lists `servers₁ ~ servers₂`, the closed form `(∑Tₕ)+b/(minₕRₕ)` is equal (latency sum via
`List.Perm.sum_eq`, rate-min via the comm/assoc `⊓`-fold). So for ANY tandem (no bottleneck-last
hypothesis) there is a relabeling putting the bottleneck last whose windowed LP computes the exact
order-independent worst case (`exists_perm_programOptimum_windowed_eq_exactChainOptimum`). The library's
`DeepWiki.chainValue_perm` (+ the relabeling bridge). ★ NB the literal in-place windowed-last identity
stays order-DEPENDENT (windowed `b/R_last` vs exact `b/minR`), so arbitrary order is handled by this
reorder, not by an in-place reindexing; the manifestly order-independent exact LP is the COLLAPSED form
`thm_11_1_exact_lp`. -/
theorem thm_11_1_exact_reorder (b : ℝ≥0) {servers₁ servers₂ : List (ℝ≥0 × ℝ≥0)}
    (hperm : List.Perm servers₁ servers₂) :
    DeepWiki.chainValue b servers₁ = DeepWiki.chainValue b servers₂ :=
  DeepWiki.chainValue_perm b hperm

end DeepWiki.Dnc
