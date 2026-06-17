import DeepWiki.ReactiveSystems.HennessyMilner
import DeepWiki.ReactiveSystems.Ccs
import Mathlib.Tactic.DeriveFintype

/-! # Distinguishing Hennessy–Milner formulae and the everlasting clock
Two pairs of finite CCS processes that are *not* bisimilar, each separated by an
explicit HML formula (over the alphabet `Fin 4`, `a = 0, b = 1, c = 2, d = 3`):
`⟨a⟩[b]ff` separates `a.b.0 + a.c.0` from `a.(b.0 + c.0)`, and `⟨a⟩[b]⟨c⟩tt`
separates `a.b.c.0 + a.b.d.0` from `a.(b.c.0 + b.d.0)`. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- The constant-free CCS environment over `Fin 4`. -/
abbrev d55 : Empty → CCS (Fin 4) Empty := Empty.elim

/-- `a.b.0 + a.c.0`. -/
abbrev p55a : CCS (Fin 4) Empty :=
  .choice (.pre (.name 0) (.pre (.name 1) .nil)) (.pre (.name 0) (.pre (.name 2) .nil))
/-- `a.(b.0 + c.0)`. -/
abbrev p55b : CCS (Fin 4) Empty :=
  .pre (.name 0) (.choice (.pre (.name 1) .nil) (.pre (.name 2) .nil))
/-- `⟨a⟩[b]ff`. -/
abbrev f55 : HML (Act (Fin 4)) := .dia (.name 0) (.box (.name 1) .ff)

/-- `a.b.c.0 + a.b.d.0`. -/
abbrev p55c : CCS (Fin 4) Empty :=
  .choice (.pre (.name 0) (.pre (.name 1) (.pre (.name 2) .nil)))
    (.pre (.name 0) (.pre (.name 1) (.pre (.name 3) .nil)))
/-- `a.(b.c.0 + b.d.0)`. -/
abbrev p55d : CCS (Fin 4) Empty :=
  .pre (.name 0) (.choice (.pre (.name 1) (.pre (.name 2) .nil))
    (.pre (.name 1) (.pre (.name 3) .nil)))
/-- `⟨a⟩[b]⟨c⟩tt`. -/
abbrev g55 : HML (Act (Fin 4)) := .dia (.name 0) (.box (.name 1) (.dia (.name 2) .tt))

/-- `a.b.0 + a.c.0 ⊨ ⟨a⟩[b]ff` (take the right summand `a.c.0`; `c.0` refuses `b`). -/
theorem p55a_sat : p55a ⊨[ccsLTS d55] f55 := by
  refine ⟨.pre (.name 2) .nil, by rw [ccsLTS_step]; exact Step.sumr (Step.act _ _), ?_⟩
  intro q hq
  rw [ccsLTS_step, step_pre_iff] at hq
  exact absurd hq.1 (by decide)

/-- `a.(b.0 + c.0) ⊭ ⟨a⟩[b]ff` (its sole `a`-successor `b.0 + c.0` can do `b`). -/
theorem p55b_unsat : ¬ (p55b ⊨[ccsLTS d55] f55) := by
  rintro ⟨p', hp', hbox⟩
  rw [ccsLTS_step, step_pre_iff] at hp'
  obtain ⟨_, rfl⟩ := hp'
  exact hbox CCS.nil (by rw [ccsLTS_step]; exact Step.suml (Step.act _ _))

/-- `a.b.c.0 + a.b.d.0 ⊨ ⟨a⟩[b]⟨c⟩tt` (left summand `a.b.c.0`; its `b`-successor
`c.0` can do `c`). -/
theorem p55c_sat : p55c ⊨[ccsLTS d55] g55 := by
  refine ⟨.pre (.name 1) (.pre (.name 2) .nil),
    by rw [ccsLTS_step]; exact Step.suml (Step.act _ _), ?_⟩
  intro q hq
  rw [ccsLTS_step, step_pre_iff] at hq
  obtain ⟨_, rfl⟩ := hq
  exact ⟨CCS.nil, by rw [ccsLTS_step]; exact Step.act _ _, trivial⟩

/-- `a.(b.c.0 + b.d.0) ⊭ ⟨a⟩[b]⟨c⟩tt` (its `a`-successor has a `b`-successor `d.0`
which cannot do `c`). -/
theorem p55d_unsat : ¬ (p55d ⊨[ccsLTS d55] g55) := by
  rintro ⟨p', hp', hbox⟩
  rw [ccsLTS_step, step_pre_iff] at hp'
  obtain ⟨_, rfl⟩ := hp'
  have hd : (CCS.pre (.name 3) .nil : CCS (Fin 4) Empty) ⊨[ccsLTS d55] (HML.dia (.name 2) HML.tt) :=
    hbox (.pre (.name 3) .nil) (by rw [ccsLTS_step]; exact Step.sumr (Step.act _ _))
  obtain ⟨q, hq, _⟩ := hd
  rw [ccsLTS_step, step_pre_iff] at hq
  exact absurd hq.1 (by decide)

/-- Each pair of non-bisimilar CCS processes is separated by an HML formula. -/
theorem hmlDistinguishes_nonBisimilarProcessPairs :
    (∃ F : HML (Act (Fin 4)), (p55a ⊨[ccsLTS d55] F) ∧ ¬ (p55b ⊨[ccsLTS d55] F)) ∧
    (∃ G : HML (Act (Fin 4)), (p55c ⊨[ccsLTS d55] G) ∧ ¬ (p55d ⊨[ccsLTS d55] G)) :=
  ⟨⟨f55, p55a_sat, p55b_unsat⟩, ⟨g55, p55c_sat, p55d_unsat⟩⟩

/-! ## An LTS satisfying three given HML formulae -/

/-- States of the witnessing LTS. -/
inductive S57 | s | s1 | s2 | s3 | s4 | s5 | s6 | s7
  deriving DecidableEq, Fintype

/-- Actions of the witnessing LTS. -/
inductive A57 | a | b | c
  deriving DecidableEq, Fintype

/-- The witnessing LTS: `s —a→ s₁`; `s₁ —c→ s₅`, `s₁ —b→ s₂/s₃/s₄`; `s₂ —c→ s₆`;
`s₃ —a→ s₇`; `s₄,s₅,s₆,s₇` deadlocked. -/
def edge57 : S57 → A57 → S57 → Bool
  | .s, .a, .s1 => true
  | .s1, .c, .s5 => true
  | .s1, .b, .s2 => true
  | .s2, .c, .s6 => true
  | .s1, .b, .s3 => true
  | .s3, .a, .s7 => true
  | .s1, .b, .s4 => true
  | _, _, _ => false

/-- The witnessing LTS (reducible, so satisfaction is decidable). -/
abbrev lts57 : LTS S57 A57 := .ofBool edge57

/-- The state `s` satisfies all three formulae:
`⟨a⟩(⟨b⟩⟨c⟩tt ∧ ⟨c⟩tt)`, `⟨a⟩⟨b⟩([a]ff ∧ [b]ff ∧ [c]ff)`, and
`[a]⟨b⟩([c]ff ∧ ⟨a⟩tt)`. -/
theorem s57_satisfiesThreeFormulae :
    (S57.s ⊨[lts57] HML.dia .a (HML.and (HML.dia .b (HML.dia .c HML.tt)) (HML.dia .c HML.tt))) ∧
    (S57.s ⊨[lts57]
      HML.dia .a (HML.dia .b (HML.and (HML.box .a HML.ff)
        (HML.and (HML.box .b HML.ff) (HML.box .c HML.ff))))) ∧
    (S57.s ⊨[lts57] HML.box .a (HML.dia .b (HML.and (HML.box .c HML.ff) (HML.dia .a HML.tt)))) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [sat_dia, sat_box, sat_and, sat_tt, sat_ff] <;> decide

/-! ## The everlasting `Clock` -/

/-- Channels of `Clock`. -/
inductive ClockChan | tick | tock
  deriving DecidableEq

/-- The single constant `clk`. -/
inductive ClockK | clk
  deriving DecidableEq

/-- `Clock ≝ tick.Clock`. -/
def clockDefn : ClockK → CCS ClockChan ClockK
  | .clk => .pre (.name .tick) (.const .clk)

/-- `Clock`'s only transition: a `tick` back to itself. -/
theorem clock_step_iff {α : Act ClockChan} {p' : CCS ClockChan ClockK} :
    Step clockDefn (CCS.const .clk) α p' ↔ α = Act.name .tick ∧ p' = CCS.const .clk := by
  rw [step_const_iff, clockDefn, step_pre_iff]

/-- `Clock —tick→ Clock`. -/
theorem clock_tick :
    (ccsLTS clockDefn) ⊢ (CCS.const ClockK.clk) ⟶[Act.name .tick] (CCS.const ClockK.clk) := by
  rw [ccsLTS_step]; exact clock_step_iff.2 ⟨rfl, rfl⟩

/-- `Clock ⊨ [tick](⟨tick⟩tt ∧ [tock]ff)`: after any
`tick`, another `tick` is possible but `tock` is refused. -/
theorem clock_boxProperty :
    (CCS.const ClockK.clk) ⊨[ccsLTS clockDefn]
      (HML.box (Act.name .tick)
        (HML.and (HML.dia (Act.name .tick) HML.tt) (HML.box (Act.name .tock) HML.ff))) := by
  intro p' hp'
  rw [ccsLTS_step, clock_step_iff] at hp'
  obtain ⟨_, rfl⟩ := hp'
  refine ⟨⟨CCS.const .clk, clock_tick, trivial⟩, ?_⟩
  intro q hq
  rw [ccsLTS_step, clock_step_iff] at hq
  exact absurd hq.1 (by decide)

/-- The `n`-fold diamond `⟨a⟩ⁿtt`. -/
def diaIter (a : Act ClockChan) : ℕ → HML (Act ClockChan)
  | 0 => HML.tt
  | n + 1 => HML.dia a (diaIter a n)

/-- For every `n`, `Clock ⊨ ⟨tick⟩ⁿtt`: the clock
can tick arbitrarily many times. -/
theorem clock_canIterateDiamond (n : ℕ) :
    (CCS.const ClockK.clk) ⊨[ccsLTS clockDefn] (diaIter (Act.name .tick) n) := by
  induction n with
  | zero => trivial
  | succ m ih => exact ⟨CCS.const .clk, clock_tick, ih⟩

end DeepWiki.ReactiveSystems
