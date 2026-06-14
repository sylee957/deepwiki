import Sources.Dnc.Source

/-! # DNC catalog — Chapter 11: Tight Worst-case Performances
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

/-! **Example 11.1** (§11.1.1, p.258): Two servers in tandem under arbitrary multiplexing: cumulative-process constraints C1≤A1≤A2, C2≤A2, A3≤A1, A4≤A2(?) plus service curves Bi≥βi·... — the worked trajectory example motivating the linear-program encoding of worst-case end-to-end delay/backlog. Not formalized in the library. -/

/-! **Remark 11.1** (§11.1.2, p.259): Table 11.1: the linear program for a tandem network — maximize objective subject to dates ti≥0, monotonicity A1≥A2≥..., causality, arrival constraints Ai−Ai≤αi(ts−tt), and service constraints — the O(nm) variables / O(mn²) constraints encoding. Not formalized in the library. -/

/-! **Theorem 11.1** (§11.1.3, p.261): Equivalence theorem (arbitrary multiplexing): for a tandem network with n servers and m flows, the described linear program (O(nm) variables, O(mn²) constraints) has optimum equal to the worst-case end-to-end delay for flow i (resp. worst-case backlog at server j). Not formalized in the library. -/

/-! **Example 11.2** (§11.2.1, p.263): Single FIFO node example with arrival/service curves; Table 11.2 lists the LP for one FIFO server — maximize ta−ts subject to ts≤ta≤tb, monotonicity, arrival D−D≤β, and the FIFO date-ordering constraint Ai−... ≥ ... − RT, illustrating the FIFO worst-case delay encoding. Not formalized in the library. -/

/-! **Lemma 11.1** (§11.2.2, p.264): Constraint-implication auxiliary for FIFO date ordering: given x1+(1−b)M≥x2, x2+bM≥x1, y1+(1−b)M≥y2, y2+bM≥y1, 0≤x1,x2,y1,y2≤M, b∈{0,1}, then x1<x2 ⇒ y1≤y2 and x2<x1 ⇒ y2≤y1 (the big-M Boolean ordering lemma). Not formalized in the library. -/

/-! **Theorem 11.2** (§11.2.2, p.265): FIFO tandem equivalence theorem: the worst-case delay for flow 1 is the optimal solution of the described mixed-integer linear program (MILP) with the time/order/monotonicity/FIFO-hypothesis/service/arrival constraints and Boolean ordering variables; objective max t1−t2n. Not formalized in the library. -/

end DeepWiki.Dnc
