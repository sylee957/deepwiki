import Mathlib.Tactic.Simps.Basic

/-! # The `denote` simp attribute -/

/-- Simp set of denotation-homomorphism lemmas pushing a denotation (`CFieldSpec.toK`,
`toPolyG`, …) through a computable operation to its abstract counterpart. -/
register_simp_attr denote
