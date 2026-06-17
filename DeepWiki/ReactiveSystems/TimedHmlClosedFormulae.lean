import DeepWiki.ReactiveSystems.TimedHmlClocks
import Mathlib.Data.Set.Insert

/-! # Closed `Mₜ` formulae are valuation-independent
A formula `F ∈ Mₜ` is *closed* when every formula clock occurring in a guard is
within the scope of a reset `x in ·` that binds it. For a closed `F`, satisfaction
`(p, u) ⊨ F` does not depend on the formula-clock valuation `u`; for non-closed
formulae (e.g. the guard `y = 1`) it does. -/

namespace DeepWiki.ReactiveSystems

open TLTS

variable {Proc Act D : Type*}

/-- The set of formula clocks occurring in a clock constraint. -/
def ClockConstraint.clocks {C : Type*} : ClockConstraint C → Set C
  | .true_ => ∅
  | .atom x _ _ => {x}
  | .and g₁ g₂ => g₁.clocks ∪ g₂.clocks

/-- Satisfaction of a clock constraint depends only on the clocks it mentions. -/
theorem satisfies_congr {C : Type*} {u u' : Valuation C} {g : ClockConstraint C}
    (h : ∀ x ∈ g.clocks, u x = u' x) : satisfies u g ↔ satisfies u' g := by
  induction g with
  | true_ => rfl
  | atom x c n =>
      simp only [satisfies]
      rw [h x (by simp [ClockConstraint.clocks])]
  | and g₁ g₂ ih₁ ih₂ =>
      simp only [satisfies]
      exact and_congr (ih₁ fun x hx => h x (Set.mem_union_left _ hx))
        (ih₂ fun x hx => h x (Set.mem_union_right _ hx))

/-- `F.ClosedUnder B`: every guard in `F` mentions only clocks already bound — by a
surrounding reset (collected in `B`) — so `F`'s truth never reads a free formula
clock. `reset x` extends the bound set by `x`. -/
def Mt.ClosedUnder {Act D : Type*} (B : Set D) : Mt Act D → Prop
  | .tt => True
  | .ff => True
  | .and F G => F.ClosedUnder B ∧ G.ClosedUnder B
  | .or F G => F.ClosedUnder B ∧ G.ClosedUnder B
  | .dia _ F => F.ClosedUnder B
  | .box _ F => F.ClosedUnder B
  | .existsDelay F => F.ClosedUnder B
  | .forallDelay F => F.ClosedUnder B
  | .reset x F => F.ClosedUnder (insert x B)
  | .guard g => ClockConstraint.clocks g ⊆ B

/-- A formula is *closed* when it is closed under the empty set of
bound clocks: no guard reads a clock that has not been reset above it. -/
def Mt.Closed {Act D : Type*} (F : Mt Act D) : Prop := F.ClosedUnder ∅

/-- The key invariant: on a formula closed under `B`, satisfaction agrees between any
two valuations that agree on `B` — because every guard reads only `B`-clocks, and
the binders/delays keep the `B`-clocks synchronised down both runs. -/
theorem mtSat_valuation_indep (T : TLTS Proc Act) (F : Mt Act D) :
    ∀ (B : Set D), F.ClosedUnder B → ∀ (p : Proc) (u u' : Valuation D),
      (∀ z ∈ B, u z = u' z) → (MtSat T p u F ↔ MtSat T p u' F) := by
  induction F with
  | tt => intro B _ p u u' _; simp only [MtSat]
  | ff => intro B _ p u u' _; simp only [MtSat]
  | and F G ihF ihG =>
      intro B hC p u u' hag
      simp only [MtSat]
      exact and_congr (ihF B hC.1 p u u' hag) (ihG B hC.2 p u u' hag)
  | or F G ihF ihG =>
      intro B hC p u u' hag
      simp only [MtSat]
      exact or_congr (ihF B hC.1 p u u' hag) (ihG B hC.2 p u u' hag)
  | dia a F ihF =>
      intro B hC p u u' hag
      simp only [MtSat]
      exact exists_congr fun p' => and_congr_right fun _ => ihF B hC p' u u' hag
  | box a F ihF =>
      intro B hC p u u' hag
      simp only [MtSat]
      exact forall_congr' fun p' => imp_congr_right fun _ => ihF B hC p' u u' hag
  | existsDelay F ihF =>
      intro B hC p u u' hag
      simp only [MtSat]
      refine exists_congr fun d => exists_congr fun p' => and_congr_right fun _ => ?_
      exact ihF B hC p' (u.add d) (u'.add d) fun z hz => by simp only [Valuation.add_apply, hag z hz]
  | forallDelay F ihF =>
      intro B hC p u u' hag
      simp only [MtSat]
      refine forall_congr' fun d => forall_congr' fun p' => imp_congr_right fun _ => ?_
      exact ihF B hC p' (u.add d) (u'.add d) fun z hz => by simp only [Valuation.add_apply, hag z hz]
  | reset x F ihF =>
      intro B hC p u u' hag
      simp only [MtSat]
      refine ihF (insert x B) hC p (Valuation.reset {x} u) (Valuation.reset {x} u') ?_
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hzB
      · rw [Valuation.reset_mem (by simp), Valuation.reset_mem (by simp)]
      · by_cases hzx : z = x
        · rw [hzx, Valuation.reset_mem (by simp), Valuation.reset_mem (by simp)]
        · rw [Valuation.reset_not_mem (by simp [hzx]), Valuation.reset_not_mem (by simp [hzx])]
          exact hag z hzB
  | guard g =>
      intro B hC p u u' hag
      simp only [MtSat]
      exact satisfies_congr fun z hz => hag z (hC hz)

/-- If `F` is closed, the extended states satisfying
it are independent of the formula-clock valuation `u`: `(p, u) ⊨ F ↔ (p, u') ⊨ F`. -/
theorem mtSat_closed_valuation_indep (T : TLTS Proc Act) {F : Mt Act D} (hF : F.Closed)
    (p : Proc) (u u' : Valuation D) : MtSat T p u F ↔ MtSat T p u' F :=
  mtSat_valuation_indep T F ∅ hF p u u' fun z hz => ((Set.mem_empty_iff_false z).mp hz).elim

/-- The valuation-independence fails for
*arbitrary* (non-closed) formulae: the guard `y = 1` is satisfied under the valuation
`y ↦ 1` but not under `y ↦ 0`. -/
theorem not_mtSat_valuation_indep_general :
    ∃ (T : TLTS Unit Unit) (p : Unit) (F : Mt Unit Unit) (u u' : Valuation Unit),
      ¬ (MtSat T p u F ↔ MtSat T p u' F) := by
  refine ⟨⟨fun _ _ _ => False⟩, (), .guard (.atom () .eq 1), fun _ => 1, fun _ => 0, ?_⟩
  intro h
  have h1 : MtSat (⟨fun _ _ _ => False⟩ : TLTS Unit Unit) () (fun _ => 1)
      (.guard (.atom () .eq 1)) := by simp [MtSat, satisfies, Cmp.holds]
  have h2 := h.mp h1
  simp [MtSat, satisfies, Cmp.holds] at h2

end DeepWiki.ReactiveSystems
