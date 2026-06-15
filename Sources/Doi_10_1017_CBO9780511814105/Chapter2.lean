import DeepWiki.ReactiveSystems.LabelledTransitionSystems
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 2: The language CCS
Each numbered item of the book's Chapter 2 is one declaration named by its
book number: an `abbrev` aliasing the library declaration for definitions, a
`theorem` (the book-faithful statement, discharged by the `DeepWiki` library)
for theorems/propositions. The book numbering lives here in the catalog, never
in the library; the citation (section, page) is in each docstring, the source's
DOI in `Sources.Doi_10_1017_CBO9780511814105.Source`. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems

/-! ## §2.2.1 The model of labelled transition systems -/

/-- **Definition 2.1** (§2.2.1, p.19). A labelled transition system is a triple
`(Proc, Act, {→ᵃ | a ∈ Act})` of states, labels, and a transition relation per
label. The library's `LTS`. -/
abbrev def_2_1 := @LTS

/-- **§2.2.1** (p.17), the refusal predicate `p ↛ᵃ`: `p` admits no `a`-move.
The library's `LTS.Refuses`. -/
abbrev refuses := @LTS.Refuses

/-- **§2.2.1, Remark 2.1** (p.18), reachable states: `q` is reachable from `p`
by finitely many transitions. The library's `LTS.Reachable`. -/
abbrev reachable := @LTS.Reachable

/-- **Definition 2.1** (§2.2.1, p.19), finiteness: an LTS is finite when its
state and label sets are both finite. The library's `LTS.IsFinite`. -/
abbrev def_2_1_finite := @LTS.IsFinite

end DeepWiki.Rs
