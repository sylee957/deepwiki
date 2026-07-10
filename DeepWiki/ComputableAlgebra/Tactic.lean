import Mathlib.Tactic

/-! # Kernel-safe computation tactics

Small proof automation for executable computable-algebra goals using only kernel-checked reduction. -/

/-- Close a concrete computable goal by definitional reduction or kernel-checked `decide`. -/
macro "ccompute" : tactic => `(tactic| first | rfl | decide)
