import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.Transfer

/-! # Transfer examples for the `toPoly` denotation

Validates the general `DeepWiki.Transfer` framework on this topic's `toPoly` denotation: `transfer%`
synthesizes the abstract polynomial as data, and the `transfer` tactic does whole-goal transfer.
-/

open DeepWiki.Transfer DeepWiki.SymbolicIntegration CPoly Polynomial

variable {α : Type*} [CField α] [CFieldSpec α]

/-- The abstract side is *computed* by `transfer%`, not written — what `simp`/TC could not do
(elaboration fills the RHS before a tactic runs). -/
example (p q r : CPoly α) :
    toPoly (cmul (cadd p q) r) = (toPoly p + toPoly q) * toPoly r :=
  transfer% (toPoly (cmul (cadd p q) r))

/-- Synthesis into a hole: `h`'s RHS is filled by the elaborator. -/
example (p q : CPoly α) : True := by
  have h := transfer% (toPoly (cmul p q))
  guard_hyp h : toPoly (cmul p q) = toPoly p * toPoly q
  trivial

/-- The `transfer` tactic closes a denotation-equality goal (whole-goal, then reflexive). -/
example (p q r : CPoly α) :
    toPoly (cmul (cadd p q) r) = (toPoly p + toPoly q) * toPoly r := by
  transfer

/-- Whole-goal transfer under an arbitrary head (here `natDegree`): the denotation is pushed through
regardless of the surrounding relation — the reach equality-only transfer lacks. -/
example (p q : CPoly α) :
    (toPoly (cmul p q)).natDegree = (toPoly p * toPoly q).natDegree := by
  transfer
