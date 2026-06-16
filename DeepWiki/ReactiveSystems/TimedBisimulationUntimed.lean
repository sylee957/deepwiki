import DeepWiki.ReactiveSystems.Bisimulation
import DeepWiki.ReactiveSystems.TimedTransitionSystems

/-! # Untimed (time-abstract) bisimilarity (§11.2)
Untimed bisimilarity abstracts from the *durations* of delays: a delay step is
matched by *some* delay step (of possibly different duration), while action steps
are matched exactly (Definition 11.7). Equivalently, it is strong bisimilarity on
the *untimed* LTS obtained by relabelling every time-delay transition with a
single silent action `ε`. We take this second, equivalent route, so the whole
strong-bisimilarity theory (Theorem 3.1) transfers for free. Timed bisimilarity
refines untimed bisimilarity (`TimedBisimilar.untimedBisimilar`); the converse
fails, as durations are forgotten. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Proc Act : Type*}

/-- The **untimed LTS** of a TLTS (§11.2): action transitions are kept, and every
time-delay transition is abstracted to a single silent action `ε` (here `none`),
forgetting its duration. -/
def untimedLTS (T : TLTS Proc Act) : LTS Proc (Option Act) where
  step p a q := match a with
    | some act => T.act p act q
    | none => ∃ d, T.delay p d q

/-- **Definition 11.7.** Untimed (time-abstract) bisimilarity `p ∼u q`: strong
bisimilarity on the untimed LTS — actions matched exactly, delays matched by
*some* delay of possibly different duration. -/
def UntimedBisimilar (T : TLTS Proc Act) (p q : Proc) : Prop :=
  LTS.Bisimilar T.untimedLTS p q

/-- Untimed bisimilarity is an equivalence relation (inherited from strong
bisimilarity, Theorem 3.1). -/
theorem untimedBisimilar_equivalence (T : TLTS Proc Act) :
    Equivalence T.UntimedBisimilar :=
  LTS.equivalence_bisimilar

/-- **Definition 11.7**, transfer form: untimed bisimilarity matches each action
transition exactly and each delay transition by *some* delay. -/
theorem untimedBisimilar_iff (T : TLTS Proc Act) (p q : Proc) :
    T.UntimedBisimilar p q ↔
      (∀ a p', T.act p a p' → ∃ q', T.act q a q' ∧ T.UntimedBisimilar p' q') ∧
      (∀ a q', T.act q a q' → ∃ p', T.act p a p' ∧ T.UntimedBisimilar p' q') ∧
      (∀ d p', T.delay p d p' → ∃ d' q', T.delay q d' q' ∧ T.UntimedBisimilar p' q') ∧
      (∀ d q', T.delay q d q' → ∃ d' p', T.delay p d' p' ∧ T.UntimedBisimilar p' q') := by
  simp only [UntimedBisimilar]
  rw [LTS.bisimilar_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a p' hp => h1 (some a) p' hp, fun a q' hq => h2 (some a) q' hq, ?_, ?_⟩
    · intro d p' hp
      obtain ⟨q', ⟨d', hd'⟩, hb⟩ := h1 none p' ⟨d, hp⟩
      exact ⟨d', q', hd', hb⟩
    · intro d q' hq
      obtain ⟨p', ⟨d', hd'⟩, hb⟩ := h2 none q' ⟨d, hq⟩
      exact ⟨d', p', hd', hb⟩
  · rintro ⟨ha1, ha2, hd1, hd2⟩
    refine ⟨fun a p' hp => ?_, fun a q' hq => ?_⟩
    · match a with
      | some act => exact ha1 act p' hp
      | none =>
          obtain ⟨d, hd⟩ := hp
          obtain ⟨d', q', hq', hb⟩ := hd1 d p' hd
          exact ⟨q', ⟨d', hq'⟩, hb⟩
    · match a with
      | some act => exact ha2 act q' hq
      | none =>
          obtain ⟨d, hd⟩ := hq
          obtain ⟨d', p', hp', hb⟩ := hd2 d q' hd
          exact ⟨p', ⟨d', hp'⟩, hb⟩

/-- Timed bisimilarity is an untimed bisimulation: matching a delay `d` with the
*same* `d` is a special case of matching it with *some* delay. -/
theorem isBisimulation_untimedLTS_timedBisimilar (T : TLTS Proc Act) :
    LTS.IsBisimulation T.untimedLTS T.TimedBisimilar := by
  rintro p q h
  obtain ⟨ha1, ha2, hd1, hd2⟩ := (timedBisimilar_iff T p q).mp h
  refine ⟨fun a p' hp => ?_, fun a q' hq => ?_⟩
  · match a with
    | some act => exact ha1 act p' hp
    | none =>
        obtain ⟨d, hd⟩ := hp
        obtain ⟨q', hq', hb⟩ := hd1 d p' hd
        exact ⟨q', ⟨d, hq'⟩, hb⟩
  · match a with
    | some act => exact ha2 act q' hq
    | none =>
        obtain ⟨d, hd⟩ := hq
        obtain ⟨p', hp', hb⟩ := hd2 d q' hd
        exact ⟨p', ⟨d, hp'⟩, hb⟩

/-- **Timed bisimilarity refines untimed bisimilarity** (§11.2): timed-bisimilar
states are untimed bisimilar. -/
theorem TimedBisimilar.untimedBisimilar {T : TLTS Proc Act} {p q : Proc}
    (h : T.TimedBisimilar p q) : T.UntimedBisimilar p q :=
  (isBisimulation_untimedLTS_timedBisimilar T).le_bisimilar h

end TLTS

end DeepWiki.ReactiveSystems
