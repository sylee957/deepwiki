import DeepWiki.Refine.Basic
import DeepWiki.Refine.Poly

/-! # Refine — a relational refinement/transfer kernel (CoqEAL/Trocq-style)

An isolated, relation-based proof-transfer core: the `Refines` relation, the `⟹` respectful arrow,
and the single `Refines.app` composition rule — the principled logic behind Isabelle `Transfer`,
CoqEAL, and Trocq, built directly rather than on `simp`. `Refine/Poly` supplies the
`DensePoly ⇄ Polynomial` witnesses. A `MetaM` resolver automating the composition (the Lean analog of
Trocq's Elpi engine) is the next layer. -/
