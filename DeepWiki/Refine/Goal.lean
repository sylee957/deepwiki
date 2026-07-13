import DeepWiki.Refine.Resolve

/-! # First-order proposition and goal transfer

The proposition layer interprets related propositions by `Iff`. It lets the existing resolver
synthesize an abstract proposition and lets `refine_goal` replace the concrete goal with it. -/

open Lean Meta Elab
open scoped DeepWiki.Refine

namespace DeepWiki.Refine

/-- A proof of a proposition related by `Iff` transfers back to the original proposition. -/
theorem Refines.prove {p q : Prop} (h : Refines Iff p q) (hq : q) : p := h.prf.mpr hq

/-- An unchanged proposition refines itself; this is the proposition-level leaf rule. -/
@[refines_leaf] theorem refines_iff_self (p : Prop) : Refines Iff p p := ⟨Iff.rfl⟩

/-- Conjunction respects proposition refinement by `Iff`. -/
@[refines] theorem refines_and : Refines (Iff ⟹ Iff ⟹ Iff) And And where
  prf _ _ hp _ _ hq := and_congr hp hq

/-- Disjunction respects proposition refinement by `Iff`. -/
@[refines] theorem refines_or : Refines (Iff ⟹ Iff ⟹ Iff) Or Or where
  prf _ _ hp _ _ hq := or_congr hp hq

/-- Negation respects proposition refinement by `Iff`. -/
@[refines] theorem refines_not : Refines (Iff ⟹ Iff) Not Not where
  prf _ _ hp := not_congr hp

open Lean.Elab.Tactic in
/-- `refine_goal` transfers a first-order proposition through the `@[refines]` witness table and
replaces it with the synthesized abstract goal. -/
elab "refine_goal" : tactic => withMainContext do
  let goal ← getMainGoal
  let concreteGoal ← instantiateMVars (← goal.getType)
  let (abstractGoal, proof) ← resolve (mkConst ``Iff) concreteGoal
  if ← isDefEq concreteGoal abstractGoal then
    throwError "refine_goal: the resolver did not change the goal"
  let newGoal ← mkFreshExprMVar abstractGoal (kind := .syntheticOpaque)
  goal.assign (← mkAppM ``Refines.prove #[proof, newGoal])
  replaceMainGoal [newGoal.mvarId!]

end DeepWiki.Refine
