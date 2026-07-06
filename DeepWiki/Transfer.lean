import DeepWiki.Transfer.Denote
import DeepWiki.Transfer.Basic

/-! # Transfer: a general denotation-transfer framework

Topic-agnostic infrastructure for transferring facts across a denotation (a `@[denote]`-tagged simp
set of homomorphism squares), independent of any one topic. `DeepWiki.Transfer.Denote` registers the
`denote` attribute; `DeepWiki.Transfer.Basic` provides the `transfer%` term elaborator and the
`transfer` whole-goal tactic (the Lean analog of Isabelle's Transfer / Coq's Trocq, realized as a
metaprogram because pure typeclass resolution cannot do the required decomposition).
-/
