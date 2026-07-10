import Mathlib.Tactic

/-! # Computation tactics

Centralized proof automation for concrete executable computable-algebra goals. -/

/-- Close a concrete executable goal by reduction, kernel decision, or compiled decision. -/
macro "ccompute" : tactic => `(tactic| first | rfl | native_decide | decide)
