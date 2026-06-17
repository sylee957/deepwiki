/-! # Source (paper): From Timed Automata to Logic — and Back
Reference paper for the timed Hennessy–Milner characterization — timed bisimilarity
coincides with timed modal-logic `Lν` equivalence via characteristic formulae — to
which the Reactive Systems book defers Theorems 12.4/12.5. Its catalog files point at
the `DeepWiki.ReactiveSystems` library theorems derived from it. -/

namespace DeepWiki.Llw

/-- DOI of the source paper (BRICS report RS-95-2; also MFCS 1995, LNCS 969,
pp. 529–539). -/
def doi : String := "10.7146/brics.v2i2.19504"

/-- Title of the source paper. -/
def title : String := "From Timed Automata to Logic — and Back"

/-- Authors of the source paper. -/
def authors : List String :=
  ["François Laroussinie", "Kim G. Larsen", "Carsten Weise"]

end DeepWiki.Llw
