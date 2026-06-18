import DeepWiki.ReactiveSystems.TimedBisimulationUntimed
import DeepWiki.ReactiveSystems.BisimulationWeak

/-! # Time-abstracted bisimilarity
Replace every time-delay step of a TLTS by the silent action `τ` and take *weak*
bisimilarity of the result: this is **time-abstracted bisimilarity**. The
delays-as-`τ` LTS is exactly the untimed LTS `T.untimedLTS` (delays already become
the single silent label `none`), so time-abstracted bisimilarity is weak
bisimilarity on `T.untimedLTS` with `τ = none`.

It is **not** the same as untimed bisimilarity (which is *strong* bisimilarity on
the same LTS): strong bisimilarity refines weak, so untimed bisimilarity implies
time-abstracted bisimilarity, but the converse fails — weak bisimilarity absorbs a
delay into a deadlock (`s →delay→ stop ≈ stop`) that strong bisimilarity
distinguishes. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Proc Act : Type*}

/-- **Time-abstracted bisimilarity**: weak bisimilarity on the untimed LTS, where
every time-delay step is the silent action `none`. -/
def TimeAbstractedBisimilar (T : TLTS Proc Act) (p q : Proc) : Prop :=
  T.untimedLTS.WeaklyBisimilar none p q

/-- Time-abstracted bisimilarity is an equivalence relation (inherited from weak
bisimilarity). -/
theorem timeAbstractedBisimilar_equivalence (T : TLTS Proc Act) :
    Equivalence T.TimeAbstractedBisimilar :=
  LTS.equivalence_weaklyBisimilar

/-- **Untimed bisimilarity implies time-abstracted bisimilarity**: strong
bisimilarity (delays matched by *some* delay) refines weak bisimilarity (delays as
`τ`). -/
theorem UntimedBisimilar.timeAbstractedBisimilar {T : TLTS Proc Act} {p q : Proc}
    (h : T.UntimedBisimilar p q) : T.TimeAbstractedBisimilar p q :=
  LTS.Bisimilar.weaklyBisimilar h

end TLTS

/-! ## The converse fails: a delay into a deadlock -/

namespace AbstractedDelay

/-- A state `s` that can delay to the deadlock `stop`. -/
inductive St | s | stop
  deriving DecidableEq

/-- The only transition: `s` delays to `stop` (becomes a silent step in the untimed
LTS). -/
inductive Step : St → (Unit ⊕ ℝ≥0) → St → Prop
  | delay : Step .s (.inr 1) .stop

/-- The TLTS built from `Step`. -/
def tlts : TLTS St Unit := ⟨Step⟩

/-- The relating relation: pair `s` and the deadlock with `stop`. -/
def rel : St → St → Prop := fun x y => (x = .s ∧ y = .stop) ∨ (x = .stop ∧ y = .stop)

/-- `rel` is a weak bisimulation on the untimed LTS: `s`'s delay (a `τ`) is matched
by `stop` staying put. -/
theorem isWeakBisimulation_rel : LTS.IsWeakBisimulation tlts.untimedLTS none rel := by
  rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · refine ⟨fun α x' hstep => ?_, fun α y' hstep => ?_⟩
    · cases α with
      | none =>
          obtain ⟨d, hd⟩ := hstep
          have hd' : Step .s (.inr d) x' := hd
          cases hd'
          exact ⟨.stop, Or.inl ⟨rfl, LTS.tauStar_refl _ _ _⟩, Or.inr ⟨rfl, rfl⟩⟩
      | some u =>
          cases u
          have h' : Step .s (.inl ()) x' := hstep
          cases h'
    · cases α with
      | none =>
          obtain ⟨d, hd⟩ := hstep
          have hd' : Step .stop (.inr d) y' := hd
          cases hd'
      | some u =>
          cases u
          have h' : Step .stop (.inl ()) y' := hstep
          cases h'
  · refine ⟨fun α x' hstep => ?_, fun α y' hstep => ?_⟩ <;>
      cases α with
      | none =>
          obtain ⟨d, hd⟩ := hstep
          have hd' : Step .stop (.inr d) _ := hd
          cases hd'
      | some u =>
          cases u
          have h' : Step .stop (.inl ()) _ := hstep
          cases h'

/-- `s` and `stop` are time-abstracted bisimilar (the delay is a silent step). -/
theorem s_timeAbstractedBisimilar_stop : tlts.TimeAbstractedBisimilar .s .stop :=
  isWeakBisimulation_rel.le_weaklyBisimilar (Or.inl ⟨rfl, rfl⟩)

/-- But `s` is not untimed bisimilar to `stop`: `s`'s delay step has no match from
the deadlock `stop`. -/
theorem s_not_untimedBisimilar_stop : ¬ tlts.UntimedBisimilar .s .stop := by
  intro h
  rw [TLTS.untimedBisimilar_iff] at h
  obtain ⟨d', q', hq', -⟩ := h.2.2.1 1 .stop Step.delay
  have hq'' : Step .stop (.inr d') q' := hq'
  cases hq''

end AbstractedDelay

/-- **Time-abstracted bisimilarity does not imply untimed bisimilarity** — so the
two notions are *not* equivalent (the answer to the exercise is "no"). The witness
`s →delay→ stop` is time-abstracted bisimilar to `stop` (the delay is silent) but
not untimed bisimilar to it. -/
theorem timeAbstracted_not_imp_untimedBisimilar :
    ∃ (Q : Type) (T : TLTS Q Unit) (p q : Q),
      T.TimeAbstractedBisimilar p q ∧ ¬ T.UntimedBisimilar p q :=
  ⟨AbstractedDelay.St, AbstractedDelay.tlts, .s, .stop,
    AbstractedDelay.s_timeAbstractedBisimilar_stop, AbstractedDelay.s_not_untimedBisimilar_stop⟩

end DeepWiki.ReactiveSystems
