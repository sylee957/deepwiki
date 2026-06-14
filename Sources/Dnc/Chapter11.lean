import DeepWiki.NetworkCalculus.WorstCaseLP
import Sources.Dnc.Source

/-! # DNC catalog — Chapter 11: Tight Worst-case Performances
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki

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

/-! **Example 11.2** (§11.2.1, p.263): Single FIFO node example with arrival/service curves; Table 11.2 lists the LP for one FIFO server — maximize ta−ts subject to ts≤ta≤tb, monotonicity, arrival D−D≤β, and the FIFO date-ordering constraint Ai−... ≥ ... − RT, illustrating the FIFO worst-case delay encoding. Not formalized in the library. -/

/-- **Lemma 11.1** (§11.2.2, p.264): the big-M Boolean ordering linearizing the
FIFO date order — given the four big-M constraints and `b ∈ {0,1}`,
`x₁<x₂ ⟹ b=0 ∧ y₁≤y₂` and `x₂<x₁ ⟹ b=1 ∧ y₂≤y₁`. The library's `bigM_ordering`. -/
alias lemma_11_1 := bigM_ordering

/-! **Theorem 11.2** (§11.2.2, p.265): FIFO tandem equivalence — the worst-case delay is the optimum of the MILP whose feasible set adds the Boolean FIFO-ordering constraints (`bigM_ordering`) to the LP. As with Theorem 11.1 the optimum-as-worst-case is `isLUB_programOptimum` (over the MILP-feasible set); the finite-MILP construction with its `0/1` ordering variables is the modeling content, not formalized. -/

end DeepWiki.Dnc
