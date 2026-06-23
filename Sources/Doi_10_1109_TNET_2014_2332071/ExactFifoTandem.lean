import DeepWiki.NetworkCalculus.FifoFeedForwardExact
import Sources.Doi_10_1109_TNET_2014_2332071.Source

/-! # Bouillard–Stea — exact worst-case delay in FIFO-multiplexing feed-forward networks — catalog
Paper-side ("double reference") pointers to the `DeepWiki.NetworkCalculus` theorems formalizing this
paper, complementing the DNC book catalog's `Chapter11` (§11.2 defers the general/heterogeneous exact
FIFO worst-case to this paper). The paper writes the MILP and a solver evaluates it (feasible to ~6–7
nodes); the formalized content is its logical structure, the LP bracket, the variable count, and the
single/multi-node exact instances — the exponential general-`N` Boolean-ordering reconstruction is
scoped `[infra]`/`[research]` in the library file. -/

namespace DeepWiki.Bs

open DeepWiki

/-- **Theorem 1** (p.7): the FIFO-tandem MILP optimum *is* the worst-case end-to-end delay — proved by
**Lemma 2** (every scenario of delay `d` gives a feasible MILP point of objective `d`) and **Lemma 3**
(every feasible point of objective `d` gives a scenario of delay `≥ d`). The abstract delay-preserving
scenario↔solution bridge: `DeepWiki.FifoFeedForward.programOptimum_eq_of_scenarioSolution`. -/
alias thm_1 := FifoFeedForward.programOptimum_eq_of_scenarioSolution

/-- **§IV.D** (p.8): the LP bracket `v_LP ≤ WCD ≤ V_LP` — the binary-relaxation optimum `V_LP` upper-
bounds and the date-merge reduced optimum `v_LP` lower-bounds the exact worst-case delay. The library's
`DeepWiki.FifoFeedForward.worstCaseDelay_mem_lpBracket`. -/
alias bracket_IV_D := FifoFeedForward.worstCaseDelay_mem_lpBracket

/-- **§IV (p.6): MILP size.** The `N`-node tandem MILP has `2^(N+1) − 1` time variables (the binary-tree
date layout doubling per node — the source of the exponential blow-up). The library's
`DeepWiki.FifoFeedForward.tandemMilpNumTimes_eq`. -/
alias milp_numTimes := FifoFeedForward.tandemMilpNumTimes_eq

/-- **Theorem 1, single-FIFO-node exact instance**: the worst-case delay of two token-bucket flows
`γ_{rᵢ,bᵢ}` through a rate-latency `β_{R,T}` FIFO node is the closed form `T + (b₁+b₂)/R`. The library's
`DeepWiki.FifoFeedForward.fifoNode_worstCaseDelay_eq`. -/
alias thm_1_fifoNode := FifoFeedForward.fifoNode_worstCaseDelay_eq

/-- **Theorem 1, multi-node homogeneous exact instance**: for a homogeneous-rate tandem the FIFO MILP
optimum equals the worst-case delay `(∑ₕRₕTₕ + b)/(Rmin − r)` (Lemma 2 collapses to the single all-zero
Boolean-ordering witness). The library's `DeepWiki.FifoFeedForward.fifoTandemHomogeneous_worstCaseDelay`. -/
alias thm_1_homogeneous := FifoFeedForward.fifoTandemHomogeneous_worstCaseDelay

end DeepWiki.Bs
