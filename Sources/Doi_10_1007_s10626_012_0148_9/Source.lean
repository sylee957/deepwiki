/-! # Source (paper): Container of (min,+)-linear systems
Reference paper for the **container** theory of (min,+)-linear systems — a pair of bounds `[f̲,f̄]_𝓛`
modulo the Legendre–Fenchel class, with *inclusion functions* `[⊕]`/`[*]`/`[⋆]` that are both sound
(`f[⋄]g ⊃ f⋄g`) and **internal** to the container class `F` (Definition 23). The Deterministic Network
Calculus book's Chapter 4 (Theorem 4.4 / Definition 4.5, and Remark 4.1 of §4.4) defers its full
container F-closure proof to this paper. Its catalog file points at the `DeepWiki.NetworkCalculus`
theorems formalizing the paper's internality results (the Le Boudec–Thiran concave identities, the
`ℱ_acv` closure, and the canonical-container internality of the lifted meet). -/

namespace DeepWiki.Lcch

/-- DOI of the source paper (Discrete Event Dynamic Systems 24(1):15–52, 2014). -/
def doi : String := "10.1007/s10626-012-0148-9"

/-- Title of the source paper. -/
def title : String := "Container of (min, +)-linear systems"

/-- Authors of the source paper. -/
def authors : List String := ["Euriell Le Corronc", "Bertrand Cottenceau", "Laurent Hardouin"]

end DeepWiki.Lcch
