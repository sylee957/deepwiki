import DeepWiki.ReactiveSystems.TimedHennessyMilnerClocks
import Mathlib.Data.Set.Insert

/-! # Algebraic equivalences between `Mₜ` formulae
Algebraic equivalences that hold by the satisfaction clauses
alone: `y in (y = 0) ≡ tt` and `y in (y > 0) ≡ ff` (a just-reset clock is exactly
`0`); `[a]tt ≡ tt`; and reset commutation `x in (y in F) ≡ y in (x in F)`. (The
`∃∃F ≡ ∃F` law needs the TLTS time-continuity axioms; the inequivalence of
`x in ∃(y in ∃F)` and `y in ∃(x in ∃F)` is a separate counterexample.) -/

namespace DeepWiki.ReactiveSystems

open TLTS

variable {Proc Act D : Type*}

/-- `y in (y = 0) ≡ tt`: a just-reset clock always reads `0`. -/
theorem resetClockZero_equiv_tt (T : TLTS Proc Act) (p : Proc) (u : Valuation D) (y : D) :
    MtSat T p u (Mt.reset y (Mt.guard (ClockConstraint.atom y Cmp.eq 0))) ↔ MtSat T p u Mt.tt := by
  simp [MtSat, satisfies, Cmp.holds, Valuation.reset_mem (show y ∈ ({y} : Set D) by simp)]

/-- `y in (y > 0) ≡ ff`: a just-reset clock is never strictly positive. -/
theorem resetClockPos_equiv_ff (T : TLTS Proc Act) (p : Proc) (u : Valuation D) (y : D) :
    MtSat T p u (Mt.reset y (Mt.guard (ClockConstraint.atom y Cmp.gt 0))) ↔ MtSat T p u Mt.ff := by
  simp [MtSat, satisfies, Cmp.holds, Valuation.reset_mem (show y ∈ ({y} : Set D) by simp)]

/-- `[a]tt ≡ tt`: a box over the trivially-true formula holds everywhere. -/
theorem box_tt_equiv_tt (T : TLTS Proc Act) (p : Proc) (u : Valuation D) (a : Act) :
    MtSat T p u (Mt.box a Mt.tt) ↔ MtSat T p u Mt.tt := by
  simp [MtSat]

/-- Reset commutation: `x in (y in F) ≡ y in (x in F)` for every formula `F`. -/
theorem reset_comm_mt (T : TLTS Proc Act) (p : Proc) (u : Valuation D) (x y : D) (F : Mt Act D) :
    MtSat T p u (Mt.reset x (Mt.reset y F)) ↔ MtSat T p u (Mt.reset y (Mt.reset x F)) := by
  simp only [MtSat]
  rw [Valuation.reset_comm]

end DeepWiki.ReactiveSystems
