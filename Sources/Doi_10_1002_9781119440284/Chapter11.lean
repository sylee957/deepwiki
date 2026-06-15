import DeepWiki.NetworkCalculus.WorstCaseLP
import DeepWiki.NetworkCalculus.WorstCaseLPBacklog
import DeepWiki.NetworkCalculus.WorstCaseLPInstance
import DeepWiki.NetworkCalculus.WorstCaseLPTandem
import DeepWiki.NetworkCalculus.WorstCaseLPTandemChain
import DeepWiki.NetworkCalculus.WorstCaseLPTandemBacklog
import Sources.Doi_10_1002_9781119440284.Source

/-! # DNC catalog — Chapter 11: Tight Worst-case Performances
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-- **Worst-case value as a program optimum** (the `obj`-over-`Feasible`
supremum underlying §11.1.2's LP). The library's `programOptimum`. -/
noncomputable def def_11_optimum := @programOptimum

/-! **Example 11.1** (§11.1.1, p.258): two servers in tandem under arbitrary multiplexing — the worked trajectory example motivating the LP encoding of worst-case end-to-end delay/backlog. Its worst-case value is `programOptimum` of the delay over the feasible trajectories; the concrete two-server numbers are not formalized. -/

/-! **Remark 11.1 / Table 11.1** (§11.1.2, p.259): the linear program for a tandem network — maximize the objective subject to dates ≥ 0, monotonicity, causality, arrival (`α`) and service (`β`) constraints (O(nm) variables, O(mn²) constraints). The objective-over-feasible optimum is `programOptimum`; the finite-LP construction itself is not formalized. -/

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

/-! **Example 11.2** (§11.2.1, p.263): single FIFO node example + Table 11.2 (the LP for one FIFO server). The single-node worst-case delay is `worstCaseServerDelay`, equal to the closed form `hDev(α, β)` (`thm_11_1_singleNode`); the concrete FIFO-LP numbers are not formalized. -/

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

/-- **Lemma 11.1** (§11.2.2, p.264): the big-M Boolean ordering linearizing the
FIFO date order — given the four big-M constraints and `b ∈ {0,1}`,
`x₁<x₂ ⟹ b=0 ∧ y₁≤y₂` and `x₂<x₁ ⟹ b=1 ∧ y₂≤y₁`. The library's `bigM_ordering`. -/
alias lemma_11_1 := bigM_ordering

/-! **Theorem 11.2** (§11.2.2, p.265): FIFO tandem equivalence — the worst-case delay is the optimum of the MILP whose feasible set adds the Boolean FIFO-ordering constraints (`bigM_ordering`) to the LP. As with Theorem 11.1 the optimum-as-worst-case is `isLUB_programOptimum` (over the MILP-feasible set); the finite-MILP construction with its `0/1` ordering variables is the modeling content, not formalized. -/

end DeepWiki.Dnc
