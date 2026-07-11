import Mathlib.Tactic

/-! # Computation tactics

Centralized proof automation for concrete executable computable-algebra goals. -/

/-- Close a concrete decidable goal using only kernel-checked reduction. -/
macro "cdecide" : tactic => `(tactic| first | rfl | decide)

/-- Close a concrete executable showcase by kernel-checked reduction or decision. -/
macro "ccompute" : tactic => `(tactic| first | rfl | decide)

/-- Prove a concrete represented-fraction denominator passes its kernel-reducible nonzero test. -/
macro "cfrac_nonzero" : tactic => `(tactic| cdecide)
