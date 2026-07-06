import DeepWiki.SymbolicIntegration.Computable.MonomialDeriv
import DeepWiki.Transfer

/-! # Transfer examples for the `toPolyG` denotation

Validates the general `DeepWiki.Transfer` framework on this topic's `toPolyG` denotation: `transfer%`
synthesizes the abstract polynomial as data, and the `transfer` tactic does whole-goal transfer.
-/

open DeepWiki.Transfer DeepWiki.SymbolicIntegration CPolyG Polynomial

variable {α : Type*} [CField α] [CFieldSpec α]

/-- The abstract side is *computed* by `transfer%`, not written — what `simp`/TC could not do
(elaboration fills the RHS before a tactic runs). -/
example (p q r : CPolyG α) :
    toPolyG (cmulG (caddG p q) r) = (toPolyG p + toPolyG q) * toPolyG r :=
  transfer% (toPolyG (cmulG (caddG p q) r))

/-- Synthesis into a hole: `h`'s RHS is filled by the elaborator. -/
example (p q : CPolyG α) : True := by
  have h := transfer% (toPolyG (cmulG p q))
  guard_hyp h : toPolyG (cmulG p q) = toPolyG p * toPolyG q
  trivial

/-- The `transfer` tactic closes a denotation-equality goal (whole-goal, then reflexive). -/
example (p q r : CPolyG α) :
    toPolyG (cmulG (caddG p q) r) = (toPolyG p + toPolyG q) * toPolyG r := by
  transfer

/-- Whole-goal transfer under an arbitrary head (here `natDegree`): the denotation is pushed through
regardless of the surrounding relation — the reach equality-only transfer lacks. -/
example (p q : CPolyG α) :
    (toPolyG (cmulG p q)).natDegree = (toPolyG p * toPolyG q).natDegree := by
  transfer
