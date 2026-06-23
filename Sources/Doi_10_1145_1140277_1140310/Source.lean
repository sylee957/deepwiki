/-! # Source (paper): An End-to-End Network Calculus with Data Scaling
Reference paper introducing the **data-scaling** network calculus — a flow's cumulative scaled by a
scaling function `S ∈ ℱ`, with maximal scaling curves `S̄` and scaled arrival-curve propagation. The
Deterministic Network Calculus book's §12.4.2 (constant-scaling instability) defers its data-scaling
machinery and the explicit instability trajectory to this paper. Its catalog file points at the
`DeepWiki.NetworkCalculus` theorems formalizing the scaling operator, the maximal scaling curve, the
scaled-output arrival curve, and the gain-identity grounding the §12.4.2 divergence. -/

namespace DeepWiki.Fs

/-- DOI of the source paper (ACM SIGMETRICS/Performance '06, Saint-Malo, pp. 287–298). -/
def doi : String := "10.1145/1140277.1140310"

/-- Title of the source paper. -/
def title : String :=
  "On the Way to a Distributed Systems Calculus: An End-to-End Network Calculus with Data Scaling"

/-- Authors of the source paper. -/
def authors : List String := ["Markus Fidler", "Jens B. Schmitt"]

end DeepWiki.Fs
