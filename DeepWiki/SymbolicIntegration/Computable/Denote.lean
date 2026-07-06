import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Simps.Basic
import Aesop

/-! # The `denote` simp attribute and the `Refines` aesop rule set -/

/-- Simp set of denotation-homomorphism lemmas pushing a denotation (`CFieldSpec.toK`,
`toPolyG`, …) through a computable operation to its abstract counterpart. -/
register_simp_attr denote

/-- Label for refinement-respect lemmas used by proof-side transfer helpers. -/
register_label_attr refines

-- Aesop rule set of `RefinesPolyG` respect lemmas; consumed by the `transfer` tactic to synthesize
-- the abstract polynomial from a computable expression's structure (rule set must be declared in a
-- file imported by its users, not in the same file).
declare_aesop_rule_sets [Refines]
