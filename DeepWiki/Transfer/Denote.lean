import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Simps.Basic

/-! # The `denote` simp attribute -/

/-- Simp set of denotation-homomorphism lemmas pushing a denotation (e.g. `toPoly`) through a
computable operation to its abstract counterpart. The `transfer` elaborator (`DeepWiki.Transfer.Basic`)
is driven by this set. -/
register_simp_attr denote
