/-! # Source (paper): Exact Worst-Case Delay in FIFO-Multiplexing Feed-Forward Networks
Reference paper for the **exact** worst-case end-to-end delay of a flow in a FIFO-multiplexing
feed-forward network, computed as a mixed-integer linear program (the MILP optimum *is* the worst-case
delay, Theorem 1). The Deterministic Network Calculus book's Chapter 11 (§11.2, Theorem 11.2) defers
the general/heterogeneous exact-FIFO case to this paper. Its catalog file points at the
`DeepWiki.NetworkCalculus` theorems formalizing the paper's logical structure (Lemmas 2/3 → Theorem 1,
the §IV.D LP bracket, the `2^(N+1)−1` variable count, the single/multi-node exact instances). -/

namespace DeepWiki.Bs

/-- DOI of the source paper (IEEE/ACM Transactions on Networking 23(5):1387–1400, 2016). -/
def doi : String := "10.1109/TNET.2014.2332071"

/-- Title of the source paper. -/
def title : String := "Exact Worst-Case Delay in FIFO-Multiplexing Feed-Forward Networks"

/-- Authors of the source paper. -/
def authors : List String := ["Anne Bouillard", "Giovanni Stea"]

end DeepWiki.Bs
