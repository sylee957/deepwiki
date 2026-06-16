import DeepWiki.ReactiveSystems.TimedBisimulationUntimed

/-! # Weak timed bisimilarity (§11.3)
The *weak* timed equivalence abstracts from the silent action `τ` while keeping
the time-delays observable. The weak timed transitions (Definition 11.8): `=τ⇒`
is a chain of `τ`-actions, `=a⇒` (visible `a`) is `τ*·a·τ*`, and `=d⇒` (delay
`d`) is a run of `τ`-actions and delays whose durations sum to `d`. A *weak timed
bisimulation* matches each concrete action/delay step by a weak timed transition
(Definition 11.9), and `≈` (weak timed bisimilarity) is the existence of one
(Definition 11.10). Timed bisimilarity refines it (Exercise 11.8): a concrete step
is a one-step weak transition. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Proc Act : Type*}

/-- `τ*`: the reflexive-transitive closure of silent (`τ`-action) steps. -/
def wtau (T : TLTS Proc Act) (tau : Act) : Proc → Proc → Prop :=
  Relation.ReflTransGen (fun s t => T.act s tau t)

theorem wtau_refl (T : TLTS Proc Act) (tau : Act) (s : Proc) : wtau T tau s s :=
  Relation.ReflTransGen.refl

theorem wtau_single {T : TLTS Proc Act} {tau : Act} {s t : Proc} (h : T.act s tau t) :
    wtau T tau s t := Relation.ReflTransGen.single h

theorem wtau_trans {T : TLTS Proc Act} {tau : Act} {s u t : Proc}
    (h₁ : wtau T tau s u) (h₂ : wtau T tau u t) : wtau T tau s t :=
  Relation.ReflTransGen.trans h₁ h₂

/-- **Definition 11.8**, weak action transition `s =a⇒ t`: for `a = τ` a chain of
silent steps, for visible `a` silent steps around one `a`-step. -/
def wact (T : TLTS Proc Act) (tau : Act) (s : Proc) (a : Act) (t : Proc) : Prop :=
  (a = tau ∧ wtau T tau s t) ∨
  (a ≠ tau ∧ ∃ s₁ s₂, wtau T tau s s₁ ∧ T.act s₁ a s₂ ∧ wtau T tau s₂ t)

/-- A concrete action step is a one-step weak action transition. -/
theorem act_wact {T : TLTS Proc Act} {tau : Act} {s : Proc} {a : Act} {t : Proc}
    (h : T.act s a t) : wact T tau s a t := by
  by_cases ha : a = tau
  · exact Or.inl ⟨ha, ha ▸ wtau_single h⟩
  · exact Or.inr ⟨ha, s, t, wtau_refl T tau s, h, wtau_refl T tau t⟩

/-- **Definition 11.8**, weak delay transition `s =d⇒ t`: a run of `τ`-actions and
delays whose durations sum to `d` (`=0⇒` is just `τ*`). -/
inductive wdelay (T : TLTS Proc Act) (tau : Act) : Proc → ℝ≥0 → Proc → Prop
  /-- `τ*` alone is a weak delay of `0`. -/
  | refl {s t : Proc} (h : wtau T tau s t) : wdelay T tau s 0 t
  /-- Extend a weak delay by one real delay followed by `τ*`. -/
  | cons {s : Proc} {d : ℝ≥0} {u v t : Proc} {d' : ℝ≥0}
      (h : wdelay T tau s d u) (hd : T.delay u d' v) (hτ : wtau T tau v t) :
      wdelay T tau s (d + d') t

/-- A concrete delay step is a one-step weak delay transition. -/
theorem delay_wdelay {T : TLTS Proc Act} {tau : Act} {s : Proc} {d : ℝ≥0} {t : Proc}
    (h : T.delay s d t) : wdelay T tau s d t := by
  have : wdelay T tau s (0 + d) t :=
    wdelay.cons (wdelay.refl (wtau_refl T tau s)) h (wtau_refl T tau t)
  rwa [zero_add] at this

/-- **Definition 11.9.** A *weak timed bisimulation*: each concrete action step is
matched by a weak action transition, and each concrete delay step by a weak delay
transition, on both sides. -/
def IsWeakTimedBisimulation (T : TLTS Proc Act) (tau : Act) (R : Proc → Proc → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, R s₁ s₂ →
    (∀ a s₁', T.act s₁ a s₁' → ∃ s₂', wact T tau s₂ a s₂' ∧ R s₁' s₂') ∧
    (∀ d s₁', T.delay s₁ d s₁' → ∃ s₂', wdelay T tau s₂ d s₂' ∧ R s₁' s₂') ∧
    (∀ a s₂', T.act s₂ a s₂' → ∃ s₁', wact T tau s₁ a s₁' ∧ R s₁' s₂') ∧
    (∀ d s₂', T.delay s₂ d s₂' → ∃ s₁', wdelay T tau s₁ d s₁' ∧ R s₁' s₂')

/-- **Definition 11.10.** `s ≈ s'`: *weakly timed bisimilar* — some weak timed
bisimulation relates them. -/
def WeaklyTimedBisimilar (T : TLTS Proc Act) (tau : Act) (s s' : Proc) : Prop :=
  ∃ R, IsWeakTimedBisimulation T tau R ∧ R s s'

/-- A timed bisimulation is a weak timed bisimulation (concrete steps are one-step
weak transitions). -/
theorem isWeakTimedBisimulation_of_timedBisimilar (T : TLTS Proc Act) (tau : Act) :
    IsWeakTimedBisimulation T tau (TimedBisimilar T) := by
  intro s₁ s₂ h
  obtain ⟨ha1, ha2, hd1, hd2⟩ := (timedBisimilar_iff T s₁ s₂).mp h
  refine ⟨fun a s₁' hs => ?_, fun d s₁' hs => ?_, fun a s₂' hs => ?_, fun d s₂' hs => ?_⟩
  · obtain ⟨s₂', hs₂', hb⟩ := ha1 a s₁' hs; exact ⟨s₂', act_wact hs₂', hb⟩
  · obtain ⟨s₂', hs₂', hb⟩ := hd1 d s₁' hs; exact ⟨s₂', delay_wdelay hs₂', hb⟩
  · obtain ⟨s₁', hs₁', hb⟩ := ha2 a s₂' hs; exact ⟨s₁', act_wact hs₁', hb⟩
  · obtain ⟨s₁', hs₁', hb⟩ := hd2 d s₂' hs; exact ⟨s₁', delay_wdelay hs₁', hb⟩

/-- **Exercise 11.8** (§11.3). Timed bisimilarity refines weak timed bisimilarity:
`s ~ s'` implies `s ≈ s'`. -/
theorem TimedBisimilar.weaklyTimedBisimilar {T : TLTS Proc Act} {tau : Act} {s s' : Proc}
    (h : TimedBisimilar T s s') : WeaklyTimedBisimilar T tau s s' :=
  ⟨TimedBisimilar T, isWeakTimedBisimulation_of_timedBisimilar T tau, h⟩

end TLTS

end DeepWiki.ReactiveSystems
