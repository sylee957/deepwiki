import DeepWiki.ReactiveSystems.TimedTraces
import DeepWiki.ReactiveSystems.TimedBisimulationUntimed

/-! # The bisimilarity/trace-equivalence inclusions are strict
Timed bisimilarity implies timed (and untimed) trace equivalence, and untimed
bisimilarity implies untimed trace equivalence (the positive directions). The two
remaining implications fail, witnessed by concrete TLTSs:

* **Untimed bisimilarity does not imply timed-trace equivalence.** `TimingForgotten`
  has two states that each perform one action after a *fixed* delay (`1` vs `2`):
  forgetting the durations they are untimed bisimilar, yet the timed trace `[(1, *)]`
  separates their timed languages.
* **Timed-trace equivalence does not imply untimed bisimilarity.** `Branching` is the
  classic `a.(b + c)` versus `a.b + a.c` with *no* time-delay transitions, so every
  timed language collapses to `{[]}` (an action needs a preceding delay) — the two
  start states are timed-trace equivalent but not untimed bisimilar. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-! ## Untimed bisimilar but not timed-trace equivalent -/

namespace TimingForgotten

/-- States: two delay/action lines, acting at fixed times `1` (`start1`) and `2`
(`start2`), sharing the final `stop`. -/
inductive St | start1 | ready1 | start2 | ready2 | stop
  deriving DecidableEq

/-- One transition relation: `start1` delays `1` to `ready1`, `start2` delays `2`
to `ready2`, and each `ready` performs the single action `()` to `stop`. -/
inductive Step : St → (Unit ⊕ ℝ≥0) → St → Prop
  | delay1 : Step .start1 (.inr 1) .ready1
  | delay2 : Step .start2 (.inr 2) .ready2
  | act1 : Step .ready1 (.inl ()) .stop
  | act2 : Step .ready2 (.inl ()) .stop

/-- The TLTS built from `Step`. -/
def tlts : TLTS St Unit := ⟨Step⟩

/-- Inversion: a delay step is `start1 →1→ ready1` or `start2 →2→ ready2`. -/
theorem step_inr {x y : St} {d : ℝ≥0} (h : Step x (.inr d) y) :
    (x = .start1 ∧ y = .ready1) ∨ (x = .start2 ∧ y = .ready2) := by
  cases h with
  | delay1 => exact Or.inl ⟨rfl, rfl⟩
  | delay2 => exact Or.inr ⟨rfl, rfl⟩

/-- Inversion recording the duration of `start2`'s delay (`d = 2`). -/
theorem step_start2_inr {d : ℝ≥0} {y : St} (h : Step .start2 (.inr d) y) :
    d = 2 ∧ y = .ready2 := by
  cases h; exact ⟨rfl, rfl⟩

/-- Inversion: an action step is `ready1 →()→ stop` or `ready2 →()→ stop`. -/
theorem step_inl {x y : St} (h : Step x (.inl ()) y) :
    (x = .ready1 ∧ y = .stop) ∨ (x = .ready2 ∧ y = .stop) := by
  cases h with
  | act1 => exact Or.inl ⟨rfl, rfl⟩
  | act2 => exact Or.inr ⟨rfl, rfl⟩

/-- The relating relation: pair the two lines step for step. -/
def rel : St → St → Prop := fun x y =>
  (x = .start1 ∧ y = .start2) ∨ (x = .ready1 ∧ y = .ready2) ∨ (x = .stop ∧ y = .stop)

/-- `rel` is a bisimulation on the untimed LTS (delays matched by *some* delay). -/
theorem isBisimulation_rel : LTS.IsBisimulation tlts.untimedLTS rel := by
  rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · refine ⟨fun lab x' hstep => ?_, fun lab y' hstep => ?_⟩
    · cases lab with
      | none =>
          obtain ⟨d, hd⟩ := hstep
          rcases step_inr hd with ⟨_, rfl⟩ | ⟨h, _⟩
          · exact ⟨.ready2, ⟨2, Step.delay2⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
          · exact absurd h (by decide)
      | some u =>
          cases u
          rcases step_inl hstep with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
    · cases lab with
      | none =>
          obtain ⟨d, hd⟩ := hstep
          rcases step_inr hd with ⟨h, _⟩ | ⟨_, rfl⟩
          · exact absurd h (by decide)
          · exact ⟨.ready1, ⟨1, Step.delay1⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      | some u =>
          cases u
          rcases step_inl hstep with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
  · refine ⟨fun lab x' hstep => ?_, fun lab y' hstep => ?_⟩
    · cases lab with
      | none =>
          obtain ⟨d, hd⟩ := hstep
          rcases step_inr hd with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
      | some u =>
          cases u
          rcases step_inl hstep with ⟨_, rfl⟩ | ⟨h, _⟩
          · exact ⟨.stop, Step.act2, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
          · exact absurd h (by decide)
    · cases lab with
      | none =>
          obtain ⟨d, hd⟩ := hstep
          rcases step_inr hd with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
      | some u =>
          cases u
          rcases step_inl hstep with ⟨h, _⟩ | ⟨_, rfl⟩
          · exact absurd h (by decide)
          · exact ⟨.stop, Step.act1, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  · refine ⟨fun lab x' hstep => ?_, fun lab y' hstep => ?_⟩ <;>
      cases lab with
      | none =>
          obtain ⟨d, hd⟩ := hstep
          rcases step_inr hd with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
      | some u =>
          cases u
          rcases step_inl hstep with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)

/-- The two lines are untimed bisimilar: durations are forgotten. -/
theorem start1_untimedBisimilar_start2 : tlts.UntimedBisimilar .start1 .start2 :=
  isBisimulation_rel.le_bisimilar (Or.inl ⟨rfl, rfl⟩)

/-- But their timed languages differ: `[(1, ())]` is a timed trace of `start1`
(acts at time `1`) and not of `start2` (acts only at time `2`). -/
theorem start1_timedLang_ne_start2 : tlts.timedLang .start1 ≠ tlts.timedLang .start2 := by
  intro heq
  have hp : [((1 : ℝ≥0), ())] ∈ tlts.timedLang .start1 := by
    refine ⟨.ready1, .stop, zero_le, ?_, Step.act1, trivial⟩
    rw [tsub_zero]; exact Step.delay1
  rw [heq] at hp
  obtain ⟨s1, s2, -, hdel, -, -⟩ := hp
  rw [tsub_zero] at hdel
  obtain ⟨h12, -⟩ := step_start2_inr hdel
  exact absurd h12 (by norm_num)

end TimingForgotten

/-- **Untimed bisimilarity does not imply timed-trace equivalence.** -/
theorem untimedBisimilar_not_imp_timedLangEq :
    ∃ (Q : Type) (T : TLTS Q Unit) (p q : Q),
      T.UntimedBisimilar p q ∧ T.timedLang p ≠ T.timedLang q :=
  ⟨TimingForgotten.St, TimingForgotten.tlts, .start1, .start2,
    TimingForgotten.start1_untimedBisimilar_start2, TimingForgotten.start1_timedLang_ne_start2⟩

/-! ## Timed-trace equivalent but not untimed bisimilar -/

namespace Branching

/-- Three visible actions. -/
inductive Act | a | b | c
  deriving DecidableEq

/-- States of `a.(b + c)` (`abc`, `bc`) versus `a.b + a.c`
(`abPlusAc`, `afterB`, `afterC`), sharing the dead `nil`. -/
inductive St | abc | bc | abPlusAc | afterB | afterC | nil
  deriving DecidableEq

/-- The action transitions of the two processes (no time delays). -/
inductive Step : St → Act → St → Prop
  | l_a : Step .abc .a .bc
  | l_b : Step .bc .b .nil
  | l_c : Step .bc .c .nil
  | r_a1 : Step .abPlusAc .a .afterB
  | r_a2 : Step .abPlusAc .a .afterC
  | r_b : Step .afterB .b .nil
  | r_c : Step .afterC .c .nil

/-- The TLTS: actions from `Step`, *no* time-delay transitions. -/
def tlts : TLTS St Act where
  step p l q := match l with
    | .inl act => Step p act q
    | .inr _ => False

/-- With no delays, no action is ever enabled (each needs a preceding delay), so
every timed language is `{[]}`: `w` is a timed trace iff `w = []`. -/
theorem mem_timedLang (s : St) (w : List (ℝ≥0 × Act)) :
    w ∈ tlts.timedLang s ↔ w = [] := by
  cases w with
  | nil => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | cons hd tl =>
      obtain ⟨t, act⟩ := hd
      refine ⟨fun h => ?_, fun h => absurd h (List.cons_ne_nil _ _)⟩
      obtain ⟨s1, s2, -, hdel, -, -⟩ := h
      exact False.elim hdel

/-- All states are timed-trace equivalent (every timed language is `{[]}`). -/
theorem timedLang_eq (s s' : St) : tlts.timedLang s = tlts.timedLang s' := by
  ext w; rw [mem_timedLang, mem_timedLang]

/-- `a.(b + c)` and `a.b + a.c` are not untimed bisimilar: the `a`-successor `bc`
offers both `b` and `c`, but each `a`-successor of `a.b + a.c` offers only one. -/
theorem abc_not_untimedBisimilar_abPlusAc : ¬ tlts.UntimedBisimilar .abc .abPlusAc := by
  intro h
  rw [TLTS.untimedBisimilar_iff] at h
  obtain ⟨q', hq'a, hb⟩ := h.1 .a .bc Step.l_a
  rw [TLTS.untimedBisimilar_iff] at hb
  have hq' : Step .abPlusAc .a q' := hq'a
  cases hq' with
  | r_a1 =>
      obtain ⟨r, hr, -⟩ := hb.1 .c .nil Step.l_c
      have hc : Step .afterB .c r := hr
      cases hc
  | r_a2 =>
      obtain ⟨r, hr, -⟩ := hb.1 .b .nil Step.l_b
      have hbb : Step .afterC .b r := hr
      cases hbb

end Branching

/-- **Timed-trace equivalence does not imply untimed bisimilarity.** -/
theorem timedLangEq_not_imp_untimedBisimilar :
    ∃ (Q A : Type) (T : TLTS Q A) (p q : Q),
      T.timedLang p = T.timedLang q ∧ ¬ T.UntimedBisimilar p q :=
  ⟨Branching.St, Branching.Act, Branching.tlts, .abc, .abPlusAc,
    Branching.timedLang_eq _ _, Branching.abc_not_untimedBisimilar_abPlusAc⟩

end DeepWiki.ReactiveSystems
