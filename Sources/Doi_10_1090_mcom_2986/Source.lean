/-! # Source (paper): Fast Weak-KAM Integrators for Separable Hamiltonian Systems
Reference paper for the general **convex–concave–convex three-part decomposition** of a `convex ∗ concave`
(min,plus) convolution (the paper's Theorem 4.6), via the inf-convolution / Lax–Oleinik semi-group
structure of Hamilton–Jacobi equations. The Deterministic Network Calculus book's Theorem 4.2 (§4.2.2.2)
defers its formal proof to this paper. Its catalog file points at the `DeepWiki.NetworkCalculus`
theorems formalizing the faithful statement, the convolution engines the proof rests on, and a concrete
three-part witness; the full weak-KAM induction over bounded-support PWL functions stays scoped. -/

namespace DeepWiki.Bfz

/-- DOI of the source paper (Mathematics of Computation 85(297):85–117, 2016; arXiv 1210.4090). -/
def doi : String := "10.1090/mcom/2986"

/-- Title of the source paper. -/
def title : String := "Fast weak-KAM integrators for separable Hamiltonian systems"

/-- Authors of the source paper. -/
def authors : List String := ["Anne Bouillard", "Erwan Faou", "Maxime Zavidovique"]

end DeepWiki.Bfz
