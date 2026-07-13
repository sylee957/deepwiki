import DeepWiki.Refine.Basic
import DeepWiki.Refine.RelationStructure
import DeepWiki.Refine.FunctionalRelation
import DeepWiki.Refine.Dependent
import DeepWiki.Refine.ProofTransfer
import DeepWiki.Refine.TypeEquivalence
import DeepWiki.Refine.CoreParametricity
import DeepWiki.Refine.ParametricityTranslations
import DeepWiki.Refine.WitnessWeakening
import DeepWiki.Refine.Resolve
import DeepWiki.Refine.Goal
import DeepWiki.Refine.Poly
import DeepWiki.Refine.Gcd
import DeepWiki.Refine.ResolverTheory

/-! # Refine — a relational refinement/transfer kernel (CoqEAL/Trocq-style)

An isolated, relation-based proof-transfer core: the `Refines` relation, the `⟹` respectful arrow,
and the single `Refines.app` composition rule — the principled logic behind Isabelle `Transfer`,
CoqEAL, and Trocq, built directly rather than on `simp`. `Refine/Poly` supplies the
`DensePoly ⇄ Polynomial` witnesses; and `Refine/Resolve` — the `MetaM` resolver (the Lean analog of
Trocq's Elpi engine): a `@[refines]` witness table + an `isDefEq`-driven `refine_transfer` tactic that
synthesizes a term's abstract denotation and proof by relational composition, no `simp`.
`Refine/Goal` lifts the same resolver to first-order propositions via `Iff` and provides
`refine_goal`. The theory modules formalize the six-level annotation lattice, contractible
functional relations, type equivalence and explicit univalence hypotheses, dependent respectful
products, recursive witness weakening, and an intrinsic core abstraction theorem; `ResolverTheory`
identifies the executable resolver with its multisorted arrow fragment. -/
