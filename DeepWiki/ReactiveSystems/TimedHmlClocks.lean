import DeepWiki.ReactiveSystems.TimedAutomata

/-! # Hennessy–Milner logic with time and formula clocks (`Mt`)
The full timed logic `Mt` adds to the action and delay
modalities two constructs over a set of *formula clocks* `D` (disjoint from the
automaton's own clocks): a reset `x in F` (evaluate `F` after setting clock `x`
to zero) and an atomic clock constraint `g ∈ B(D)` (the formula-clock valuation
must satisfy `g`). Formulae are interpreted over *extended states* `(p, u)` — a
process state `p` together with a formula-clock valuation `u` — and time-delay
steps advance `u` alongside the process. Timed-bisimilar states
satisfy the same `Mt` formulae under every formula-clock valuation, the soundness
half of the timed Hennessy–Milner theorem for the full logic. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- Hennessy–Milner formulae with time, `Mt`, over actions
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

/-- Satisfaction of an `Mt` formula at an extended state
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

/-- **Definition 12.2** (denotational form). The set `⟦F⟧ ⊆ ES(Proc)` of extended states that
satisfy `F`, defined compositionally with the book's action/delay set operators (`⟨a·⟩`/`[a·]`
for actions, `⟨ε·⟩`/`[ε·]` for delays). This is the book's primary semantics of `Mt`; `MtSat` is
its structural-relation presentation (p.228). -/
def denotMt (T : TLTS Proc Act) : Mt Act D → Set (Proc × Valuation D)
  | .tt => Set.univ
  | .ff => ∅
  | .and F G => denotMt T F ∩ denotMt T G
  | .or F G => denotMt T F ∪ denotMt T G
  | .dia a F => {q | ∃ p', T.act q.1 a p' ∧ (p', q.2) ∈ denotMt T F}
  | .box a F => {q | ∀ p', T.act q.1 a p' → (p', q.2) ∈ denotMt T F}
  | .existsDelay F => {q | ∃ d p', T.delay q.1 d p' ∧ (p', q.2.add d) ∈ denotMt T F}
  | .forallDelay F => {q | ∀ d p', T.delay q.1 d p' → (p', q.2.add d) ∈ denotMt T F}
  | .reset x F => {q | (q.1, Valuation.reset {x} q.2) ∈ denotMt T F}
  | .guard g => {q | satisfies q.2 g}

/-- **Exercise 12.4** (§12.1, p.228). The denotational semantics `⟦F⟧` (Definition 12.2) and the
structural satisfaction relation `MtSat` agree: `(p, u) ∈ ⟦F⟧ ↔ (p, u) ⊨ F`. Proved by induction
on `F` — the two presentations of `Mt`'s satisfaction relation are equivalent. -/
theorem mem_denotMt_iff_mtSat (T : TLTS Proc Act) (F : Mt Act D) (p : Proc) (u : Valuation D) :
    (p, u) ∈ denotMt T F ↔ MtSat T p u F := by
  induction F generalizing p u with
  | tt => simp [denotMt, MtSat]
  | ff => simp [denotMt, MtSat]
  | and F G ihF ihG => simp [denotMt, MtSat, ihF, ihG]
  | or F G ihF ihG => simp [denotMt, MtSat, ihF, ihG]
  | dia a F ihF => simp [denotMt, MtSat, ihF]
  | box a F ihF => simp [denotMt, MtSat, ihF]
  | existsDelay F ihF => simp [denotMt, MtSat, ihF]
  | forallDelay F ihF => simp [denotMt, MtSat, ihF]
  | reset x F ihF => simp [denotMt, MtSat, ihF]
  | guard g => simp [denotMt, MtSat]

/-- A process state satisfies `F` when the extended state
with every formula clock zero satisfies it: `(p, u₀) ⊨ F` with `u₀ ≡ 0`. -/
def MtSatState (T : TLTS Proc Act) (p : Proc) (F : Mt Act D) : Prop :=
  MtSat T p (fun _ => 0) F

/-- Two `Mt` formulae are equivalent when satisfied by the same extended states
in every TLTS. -/
def MtEquiv (F G : Mt Act D) : Prop :=
  ∀ {Q : Type*} (T : TLTS Q Act) (p : Q) (u : Valuation D), MtSat T p u F ↔ MtSat T p u G

/-- `≡` is reflexive: `F ≡ F`. -/
@[refl] theorem MtEquiv.refl (F : Mt Act D) : MtEquiv F F := fun _ _ _ => Iff.rfl

/-- `R` is an **`Mt`-bisimulation** on extended states `(p, u)`: the valuations agree
on every guard and survive a clock reset, action moves are matched (valuation
unchanged), and delay moves are matched by *some* delay (each side advancing its own
valuation). This is the back-and-forth that preserves `Mt` satisfaction; unlike timed
bisimilarity it lets the two sides delay by *different* amounts — matching the logic's
`∃∃`/`∀∀`, which never measure a duration directly. -/
def IsMtBisimulation (T : TLTS Proc Act)
    (R : Proc → Valuation D → Proc → Valuation D → Prop) : Prop :=
  ∀ ⦃p u q u'⦄, R p u q u' →
    (∀ g : ClockConstraint D, satisfies u g ↔ satisfies u' g) ∧
    (∀ x, R p (Valuation.reset {x} u) q (Valuation.reset {x} u')) ∧
    (∀ a p', T.act p a p' → ∃ q', T.act q a q' ∧ R p' u q' u') ∧
    (∀ a q', T.act q a q' → ∃ p', T.act p a p' ∧ R p' u q' u') ∧
    (∀ d p', T.delay p d p' → ∃ d' q', T.delay q d' q' ∧ R p' (u.add d) q' (u'.add d')) ∧
    (∀ d q', T.delay q d q' → ∃ d' p', T.delay p d' p' ∧ R p' (u.add d') q' (u'.add d))

/-- **`Mt`-bisimulation soundness.** Extended states related by an `Mt`-bisimulation
satisfy exactly the same `Mt` formulae. -/
theorem IsMtBisimulation.mtSat {T : TLTS Proc Act}
    {R : Proc → Valuation D → Proc → Valuation D → Prop} (hR : IsMtBisimulation T R) :
    ∀ (F : Mt Act D) {p u q u'}, R p u q u' → (MtSat T p u F ↔ MtSat T q u' F) := by
  intro F
  induction F with
  | tt => intro _ _ _ _ _; exact Iff.rfl
  | ff => intro _ _ _ _ _; exact Iff.rfl
  | and F G ihF ihG => intro _ _ _ _ h; exact and_congr (ihF h) (ihG h)
  | or F G ihF ihG => intro _ _ _ _ h; exact or_congr (ihF h) (ihG h)
  | guard g => intro _ _ _ _ h; exact (hR h).1 g
  | reset x F ihF => intro _ _ _ _ h; exact ihF ((hR h).2.1 x)
  | dia a F ihF =>
      intro _ _ _ _ h
      refine ⟨fun hp => ?_, fun hq => ?_⟩
      · obtain ⟨p', hstep, hsat⟩ := hp
        obtain ⟨q', hq', hr⟩ := (hR h).2.2.1 a p' hstep
        exact ⟨q', hq', (ihF hr).mp hsat⟩
      · obtain ⟨q', hstep, hsat⟩ := hq
        obtain ⟨p', hp', hr⟩ := (hR h).2.2.2.1 a q' hstep
        exact ⟨p', hp', (ihF hr).mpr hsat⟩
  | box a F ihF =>
      intro _ _ _ _ h
      refine ⟨fun hp q' hq' => ?_, fun hq p' hp' => ?_⟩
      · obtain ⟨p', hp', hr⟩ := (hR h).2.2.2.1 a q' hq'
        exact (ihF hr).mp (hp p' hp')
      · obtain ⟨q', hq', hr⟩ := (hR h).2.2.1 a p' hp'
        exact (ihF hr).mpr (hq q' hq')
  | existsDelay F ihF =>
      intro _ _ _ _ h
      refine ⟨fun hp => ?_, fun hq => ?_⟩
      · obtain ⟨d, p', hstep, hsat⟩ := hp
        obtain ⟨d', q', hq', hr⟩ := (hR h).2.2.2.2.1 d p' hstep
        exact ⟨d', q', hq', (ihF hr).mp hsat⟩
      · obtain ⟨d, q', hstep, hsat⟩ := hq
        obtain ⟨d', p', hp', hr⟩ := (hR h).2.2.2.2.2 d q' hstep
        exact ⟨d', p', hp', (ihF hr).mpr hsat⟩
  | forallDelay F ihF =>
      intro _ _ _ _ h
      refine ⟨fun hp d q' hq' => ?_, fun hq d p' hp' => ?_⟩
      · obtain ⟨d', p', hp', hr⟩ := (hR h).2.2.2.2.2 d q' hq'
        exact (ihF hr).mp (hp d' p' hp')
      · obtain ⟨d', q', hq', hr⟩ := (hR h).2.2.2.2.1 d p' hp'
        exact (ihF hr).mpr (hq d' q' hq')

/-- Timed bisimilarity (with equal formula valuations) is an `Mt`-bisimulation. -/
theorem timedBisimilar_isMtBisimulation (T : TLTS Proc Act) :
    IsMtBisimulation T
      (fun (p : Proc) (u : Valuation D) (q : Proc) (u' : Valuation D) =>
        TimedBisimilar T p q ∧ u = u') := by
  rintro p u q u' ⟨hb, rfl⟩
  obtain ⟨ha1, ha2, hd1, hd2⟩ := (timedBisimilar_iff T p q).mp hb
  refine ⟨fun _ => Iff.rfl, fun _ => ⟨hb, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro a p' hstep; obtain ⟨q', hq', hb'⟩ := ha1 a p' hstep; exact ⟨q', hq', hb', rfl⟩
  · intro a q' hstep; obtain ⟨p', hp', hb'⟩ := ha2 a q' hstep; exact ⟨p', hp', hb', rfl⟩
  · intro d p' hstep; obtain ⟨q', hq', hb'⟩ := hd1 d p' hstep; exact ⟨d, q', hq', hb', rfl⟩
  · intro d q' hstep; obtain ⟨p', hp', hb'⟩ := hd2 d q' hstep; exact ⟨d, p', hp', hb', rfl⟩

/-- **Soundness for `Mt`**. Timed-bisimilar states satisfy the same `Mt`
formulae at every formula-clock valuation (via `Mt`-bisimulation soundness). -/
theorem timedBisimilar_mtIff {T : TLTS Proc Act} {p q : Proc}
    (h : TimedBisimilar T p q) (u : Valuation D) (F : Mt Act D) :
    MtSat T p u F ↔ MtSat T q u F :=
  (timedBisimilar_isMtBisimulation T).mtSat F ⟨h, rfl⟩

/-- **Soundness for `Mt`** at the state level: timed-bisimilar
states satisfy the same `Mt` formulae. -/
theorem timedBisimilar_mtSatState {T : TLTS Proc Act} {p q : Proc}
    (h : TimedBisimilar T p q) (F : Mt Act D) :
    MtSatState T p F ↔ MtSatState T q F :=
  timedBisimilar_mtIff h (fun _ => 0) F

/-- The book's example formula `y in ∃∃(y > 1 ∧ ⟨a⟩tt)`: it is possible
to delay for more than one time unit and then perform an `a`-action. -/
example (a : Act) : Mt Act Unit :=
  .reset () (.existsDelay (.and (.guard (.atom () .gt 1)) (.dia a .tt)))

end TLTS

/-- A timed automaton `A` satisfies a formula `F ∈ Mt` when
its initial extended state — initial location with all automaton clocks zero, and
all formula clocks zero — satisfies `F`. -/
noncomputable def TimedAutomaton.SatisfiesMt {Loc Act C D : Type*}
    (A : TimedAutomaton Loc Act C) (F : Mt Act D) : Prop :=
  A.tlts.MtSatState (A.initial, fun _ => 0) F

end DeepWiki.ReactiveSystems
