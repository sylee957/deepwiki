import Mathlib.Tactic.Simps.Basic

/-! # The `denote` simp attribute

Registers the single simp set collecting the engine's *denotation homomorphism* lemmas.
Kept in its own module because a `register_simp_attr` attribute is only usable in files that
*import* the registration (its initializer runs at import time). -/

/-- Simp set of *denotation homomorphism* lemmas: every lemma pushing a denotation
(`CFieldSpec.toK`, `toPolyG`, …) through a computable operation to its abstract Mathlib
counterpart (`toK (add a b) = toK a + toK b`, `toPolyG (caddG p q) = toPolyG p + toPolyG q`, …).
`simp only [denote]` normalizes a denotation to leaves without invoking the full default
`simp` set — the standard tool for the engine's commuting-square proofs. Tag a lemma
`@[denote]` iff its statement is such a homomorphism square with the denotation pushed inward. -/
register_simp_attr denote
