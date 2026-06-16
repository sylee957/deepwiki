import DeepWiki.ReactiveSystems.TimedAutomata

/-! # Hennessy–Milner logic with time and formula clocks (`Mt`, §12.1)
The full timed logic `Mt` of Definition 12.1 adds to the action and delay
modalities two constructs over a set of *formula clocks* `D` (disjoint from the
automaton's own clocks): a reset `x in F` (evaluate `F` after setting clock `x`
to zero) and an atomic clock constraint `g ∈ B(D)` (the formula-clock valuation
must satisfy `g`). Formulae are interpreted over *extended states* `(p, u)` — a
process state `p` together with a formula-clock valuation `u` — and time-delay
steps advance `u` alongside the process (Definition 12.2). Timed-bisimilar states
satisfy the same `Mt` formulae under every formula-clock valuation, the soundness
half of the timed Hennessy–Milner theorem for the full logic. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- **Definition 12.1.** Hennessy–Milner formulae with time, `Mt`, over actions
`Act` and formula clocks `D`: `tt`, `ff`, `∧`, `∨`, the action modalities
`⟨a⟩`/`[a]`, the delay quantifiers `∃∃`/`∀∀`, the reset `x in F`, and atomic
clock constraints `g ∈ B(D)`. -/
inductive Mt (Act D : Type*)
  | tt : Mt Act D
  | ff : Mt Act D
  | and : Mt Act D → Mt Act D → Mt Act D
  | or : Mt Act D → Mt Act D → Mt Act D
  | dia : Act → Mt Act D → Mt Act D
  | box : Act → Mt Act D → Mt Act D
  | existsDelay : Mt Act D → Mt Act D
  | forallDelay : Mt Act D → Mt Act D
  | reset : D → Mt Act D → Mt Act D
  | guard : ClockConstraint D → Mt Act D

namespace TLTS

variable {Proc Act D : Type*}

/-- **Definition 12.2.** Satisfaction of an `Mt` formula at an extended state
`(p, u)` — process `p` with formula-clock valuation `u`. Action modalities range
over `a`-transitions; the delay quantifiers range over time steps and advance the
formula clocks `u` by the same delay; `x in F` resets `x` to zero; `g` holds when
`u` satisfies the constraint. -/
def MtSat (T : TLTS Proc Act) (p : Proc) (u : Valuation D) : Mt Act D → Prop
  | .tt => True
  | .ff => False
  | .and F G => MtSat T p u F ∧ MtSat T p u G
  | .or F G => MtSat T p u F ∨ MtSat T p u G
  | .dia a F => ∃ p', T.act p a p' ∧ MtSat T p' u F
  | .box a F => ∀ p', T.act p a p' → MtSat T p' u F
  | .existsDelay F => ∃ d p', T.delay p d p' ∧ MtSat T p' (u.add d) F
  | .forallDelay F => ∀ d p', T.delay p d p' → MtSat T p' (u.add d) F
  | .reset x F => MtSat T p (Valuation.reset {x} u) F
  | .guard g => satisfies u g

/-- **Definition 12.3.** A process state satisfies `F` when the extended state
with every formula clock zero satisfies it: `(p, u₀) ⊨ F` with `u₀ ≡ 0`. -/
def MtSatState (T : TLTS Proc Act) (p : Proc) (F : Mt Act D) : Prop :=
  MtSat T p (fun _ => 0) F

/-- Two `Mt` formulae are equivalent when satisfied by the same extended states
in every TLTS. -/
def MtEquiv (F G : Mt Act D) : Prop :=
  ∀ {Q : Type*} (T : TLTS Q Act) (p : Q) (u : Valuation D), MtSat T p u F ↔ MtSat T p u G

/-- Timed-bisimilar states satisfy the same `Mt` formula under every
formula-clock valuation (one implication). The reset and guard cases touch only
the formula clocks, so they transfer for free; the modal cases use timed
bisimilarity. -/
theorem timedBisimilar_mtSat {T : TLTS Proc Act} (F : Mt Act D) :
    ∀ {p q} (u : Valuation D), TimedBisimilar T p q → MtSat T p u F → MtSat T q u F := by
  induction F with
  | tt => exact fun _ _ _ => trivial
  | ff => exact fun _ _ h => h
  | and F G ihF ihG => exact fun u hb hp => ⟨ihF u hb hp.1, ihG u hb hp.2⟩
  | or F G ihF ihG => exact fun u hb hp => hp.imp (ihF u hb) (ihG u hb)
  | dia a F ihF =>
      intro p q u hb hp
      obtain ⟨p', hstep, hsat⟩ := hp
      obtain ⟨q', hq', hb'⟩ := ((timedBisimilar_iff T p q).mp hb).1 a p' hstep
      exact ⟨q', hq', ihF u hb' hsat⟩
  | box a F ihF =>
      intro p q u hb hp q' hq'
      obtain ⟨p', hp', hb'⟩ := ((timedBisimilar_iff T p q).mp hb).2.1 a q' hq'
      exact ihF u hb' (hp p' hp')
  | existsDelay F ihF =>
      intro p q u hb hp
      obtain ⟨d, p', hstep, hsat⟩ := hp
      obtain ⟨q', hq', hb'⟩ := ((timedBisimilar_iff T p q).mp hb).2.2.1 d p' hstep
      exact ⟨d, q', hq', ihF (u.add d) hb' hsat⟩
  | forallDelay F ihF =>
      intro p q u hb hp d q' hq'
      obtain ⟨p', hp', hb'⟩ := ((timedBisimilar_iff T p q).mp hb).2.2.2 d q' hq'
      exact ihF (u.add d) hb' (hp d p' hp')
  | reset x F ihF => exact fun u hb hp => ihF (Valuation.reset {x} u) hb hp
  | guard g => exact fun _ _ hp => hp

/-- **Soundness for `Mt`** (§12.1). Timed-bisimilar states satisfy the same `Mt`
formulae at every formula-clock valuation. -/
theorem timedBisimilar_mtIff {T : TLTS Proc Act} {p q : Proc}
    (h : TimedBisimilar T p q) (u : Valuation D) (F : Mt Act D) :
    MtSat T p u F ↔ MtSat T q u F :=
  ⟨timedBisimilar_mtSat F u h, timedBisimilar_mtSat F u h.symm⟩

/-- **Soundness for `Mt`** at the state level (Definition 12.3): timed-bisimilar
states satisfy the same `Mt` formulae. -/
theorem timedBisimilar_mtSatState {T : TLTS Proc Act} {p q : Proc}
    (h : TimedBisimilar T p q) (F : Mt Act D) :
    MtSatState T p F ↔ MtSatState T q F :=
  timedBisimilar_mtIff h (fun _ => 0) F

/-- The book's example formula (p.225) `y in ∃∃(y > 1 ∧ ⟨a⟩tt)`: it is possible
to delay for more than one time unit and then perform an `a`-action. -/
example (a : Act) : Mt Act Unit :=
  .reset () (.existsDelay (.and (.guard (.atom () .gt 1)) (.dia a .tt)))

end TLTS

/-- **Definition 12.4.** A timed automaton `A` satisfies a formula `F ∈ Mt` when
its initial extended state — initial location with all automaton clocks zero, and
all formula clocks zero — satisfies `F`. -/
noncomputable def TimedAutomaton.SatisfiesMt {Loc Act C D : Type*}
    (A : TimedAutomaton Loc Act C) (F : Mt Act D) : Prop :=
  A.tlts.MtSatState (A.initial, fun _ => 0) F

end DeepWiki.ReactiveSystems
