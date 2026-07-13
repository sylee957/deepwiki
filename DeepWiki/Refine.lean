import DeepWiki.Refine.Basic
import DeepWiki.Refine.Resolve
import DeepWiki.Refine.Poly

/-! # Refine — a relational refinement/transfer kernel (CoqEAL/Trocq-style)

An isolated, relation-based proof-transfer core: the `Refines` relation, the `⟹` respectful arrow,
and the single `Refines.app` composition rule — the principled logic behind Isabelle `Transfer`,
CoqEAL, and Trocq, built directly rather than on `simp`. `Refine/Poly` supplies the
`DensePoly ⇄ Polynomial` witnesses; and `Refine/Resolve` — the `MetaM` resolver (the Lean analog of
Trocq's Elpi engine): a `@[refines]` witness table + an `isDefEq`-driven `refine_transfer` tactic that
synthesizes a term's abstract denotation and proof by relational composition, no `simp`. -/
