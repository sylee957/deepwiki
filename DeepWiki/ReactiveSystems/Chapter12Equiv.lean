import DeepWiki.ReactiveSystems.TimedHennessyMilnerClocks
import Mathlib.Data.Set.Insert

/-! # Exercise 12.3 — equivalences between `Mₜ` formulae
The algebraic equivalences of Exercise 12.3 that hold by the satisfaction clauses
alone: `y in (y = 0) ≡ tt` and `y in (y > 0) ≡ ff` (a just-reset clock is exactly
`0`); `[a]tt ≡ tt`; and reset commutation `x in (y in F) ≡ y in (x in F)`. (Part 2,
`∃∃F ≡ ∃F`, needs the TLTS time-continuity axioms of §9; the inequivalence of
`x in ∃(y in ∃F)` and `y in ∃(x in ∃F)` is a separate counterexample.) -/

namespace DeepWiki.ReactiveSystems

open TLTS

variable {Proc Act D : Type*}

/-- Two single-clock resets commute: `u[y][x] = u[x][y]`. -/
theorem Valuation.reset_comm {C : Type*} (x y : C) (u : Valuation C) :
    Valuation.reset {x} (Valuation.reset {y} u) = Valuation.reset {y} (Valuation.reset {x} u) := by
  funext z
  by_cases hx : z = x <;> by_cases hy : z = y <;>
    simp [Valuation.reset, Set.mem_singleton_iff, hx, hy]

/-- **Exercise 12.3(1)** (§12.1, p.227). `y in (y = 0) ≡ tt`: a just-reset clock
always reads `0`. -/
theorem ex_12_3_1a (T : TLTS Proc Act) (p : Proc) (u : Valuation D) (y : D) :
    MtSat T p u (Mt.reset y (Mt.guard (ClockConstraint.atom y Cmp.eq 0))) ↔ MtSat T p u Mt.tt := by
  simp [MtSat, satisfies, Cmp.holds, Valuation.reset_mem (show y ∈ ({y} : Set D) by simp)]

/-- **Exercise 12.3(1)** (§12.1, p.227). `y in (y > 0) ≡ ff`: a just-reset clock is
never strictly positive. -/
theorem ex_12_3_1b (T : TLTS Proc Act) (p : Proc) (u : Valuation D) (y : D) :
    MtSat T p u (Mt.reset y (Mt.guard (ClockConstraint.atom y Cmp.gt 0))) ↔ MtSat T p u Mt.ff := by
  simp [MtSat, satisfies, Cmp.holds, Valuation.reset_mem (show y ∈ ({y} : Set D) by simp)]

/-- **Exercise 12.3(3)** (§12.1, p.227). `[a]tt ≡ tt`: a box over the trivially-true
formula holds everywhere. -/
theorem ex_12_3_3 (T : TLTS Proc Act) (p : Proc) (u : Valuation D) (a : Act) :
    MtSat T p u (Mt.box a Mt.tt) ↔ MtSat T p u Mt.tt := by
  simp [MtSat]

/-- **Exercise 12.3(5)** (§12.1, p.227). Reset commutation: `x in (y in F) ≡ y in
(x in F)` for every formula `F`. -/
theorem ex_12_3_5 (T : TLTS Proc Act) (p : Proc) (u : Valuation D) (x y : D) (F : Mt Act D) :
    MtSat T p u (Mt.reset x (Mt.reset y F)) ↔ MtSat T p u (Mt.reset y (Mt.reset x F)) := by
  simp only [MtSat]
  rw [Valuation.reset_comm]

end DeepWiki.ReactiveSystems
