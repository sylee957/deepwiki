import DeepWiki.ReactiveSystems.HmlRecursion

/-! # Specifying mutual exclusion
Mutual exclusion is a safety property: it is *invariably* the case that the two
processes are never simultaneously in their critical sections. Following §7.1,
"process `i` is in its critical section" is observed as "the exit action `eᵢ` is
enabled", so the property is the invariant of `[e₁]ff ∨ [e₂]ff` — at least one
critical section is always unavailable. Via Theorem 6.1 this reduces to a
reachability statement. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-- A process is in its critical section guarded by `e` exactly when it can
perform the exit action `e`. -/
def CanDo (L : LTS Proc Act) (e : Act) (p : Proc) : Prop := ∃ p', L.step p e p'

/-- The mutual-exclusion safety formula (§7.1, p.147): `[e₁]ff ∨ [e₂]ff` — at
least one of the two critical sections is unavailable. -/
def mutexFormula (e1 e2 : Act) : HML Act := (HML.box e1 HML.ff).or (HML.box e2 HML.ff)

/-- The mutual-exclusion property (§7.1): the invariant that the two processes are
never both in their critical sections. -/
def MutEx (L : LTS Proc Act) (e1 e2 : Act) : Set Proc := Inv L (mutexFormula e1 e2)

/-- The safety formula holds at a state iff the two critical sections are not both
available there. -/
theorem mem_denot_mutexFormula (L : LTS Proc Act) (e1 e2 : Act) (q : Proc) :
    q ∈ denot L (mutexFormula e1 e2) ↔ ¬ (CanDo L e1 q ∧ CanDo L e2 q) := by
  show (q ⊨[L] mutexFormula e1 e2) ↔ _
  simp only [mutexFormula, sat_or, sat_box_ff, LTS.Refuses, CanDo, not_and_or, not_exists]

/-- **§7.1** (p.147). The mutual-exclusion property as an invariant: a state has
mutual exclusion iff no state reachable from it has both critical sections
simultaneously available. (A direct application of Theorem 6.1.) -/
theorem mem_MutEx (L : LTS Proc Act) (e1 e2 : Act) (p : Proc) :
    p ∈ MutEx L e1 e2 ↔ ∀ q, L.Reachable p q → ¬ (CanDo L e1 q ∧ CanDo L e2 q) := by
  show p ∈ Inv L (mutexFormula e1 e2) ↔ _
  rw [Inv_eq]
  simp only [Set.mem_setOf_eq, mem_denot_mutexFormula]

/-- A state with mutual exclusion is itself safe: it is not in both critical
sections at once. -/
theorem MutEx_safe (L : LTS Proc Act) {e1 e2 : Act} {p : Proc} (h : p ∈ MutEx L e1 e2) :
    ¬ (CanDo L e1 p ∧ CanDo L e2 p) := (mem_MutEx L e1 e2 p).mp h p (reachable_refl L p)

/-- Mutual exclusion is inherited by reachable states. -/
theorem MutEx_reachable (L : LTS Proc Act) {e1 e2 : Act} {p q : Proc}
    (h : p ∈ MutEx L e1 e2) (hr : L.Reachable p q) : q ∈ MutEx L e1 e2 :=
  (mem_MutEx L e1 e2 q).mpr fun r hr' => (mem_MutEx L e1 e2 p).mp h r (reachable_trans L hr hr')

end LTS

end DeepWiki.ReactiveSystems
