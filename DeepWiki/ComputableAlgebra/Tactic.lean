import Mathlib.Tactic

/-! # Computation tactics

Centralized proof automation for concrete executable computable-algebra goals. -/

/-- Close a concrete executable goal, preferring kernel reduction before compiled decision. -/
macro "ccompute" : tactic => `(tactic| first | rfl | decide | decide +native)

/-- Prove a concrete represented-fraction denominator passes its executable nonzero test. -/
macro "cfrac_nonzero" : tactic => `(tactic| ccompute)
