import DeepWiki.ReactiveSystems.TimedBisimulationUntimed

/-! # Weak timed bisimilarity
The *weak* timed equivalence abstracts from the silent action `τ` while keeping
the time-delays observable. The weak timed transitions: `=τ⇒`
is a chain of `τ`-actions, `=a⇒` (visible `a`) is `τ*·a·τ*`, and `=d⇒` (delay
`d`) is a run of `τ`-actions and delays whose durations sum to `d`. A *weak timed
bisimulation* matches each concrete action/delay step by a weak timed transition,
and `≈` (weak timed bisimilarity) is the existence of one.
Timed bisimilarity refines it: a concrete step
is a one-step weak transition. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Proc Act : Type*}

/-- `τ*`: the reflexive-transitive closure of silent (`τ`-action) steps. -/
def wtau (T : TLTS Proc Act) (tau : Act) : Proc → Proc → Prop :=
  Relation.ReflTransGen (fun s t => T.act s tau t)

/-- `τ*` is reflexive: `wtau T tau s s`. -/
theorem wtau_refl (T : TLTS Proc Act) (tau : Act) (s : Proc) : wtau T tau s s :=
  Relation.ReflTransGen.refl

/-- A single `τ`-step is a `τ*` reachability. -/
theorem wtau_single {T : TLTS Proc Act} {tau : Act} {s t : Proc} (h : T.act s tau t) :
    wtau T tau s t := Relation.ReflTransGen.single h

/-- `τ*` is transitive: compose `wtau T tau s u` and `wtau T tau u t`. -/
theorem wtau_trans {T : TLTS Proc Act} {tau : Act} {s u t : Proc}
    (h₁ : wtau T tau s u) (h₂ : wtau T tau u t) : wtau T tau s t :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Weak action transition `s =a⇒ t`: for `a = τ` a chain of
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

/-- Weak delay transition `s =d⇒ t`: a run of `τ`-actions and
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

/-- A *weak timed bisimulation*: each concrete action step is
matched by a weak action transition, and each concrete delay step by a weak delay
transition, on both sides. -/
def IsWeakTimedBisimulation (T : TLTS Proc Act) (tau : Act) (R : Proc → Proc → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, R s₁ s₂ →
    (∀ a s₁', T.act s₁ a s₁' → ∃ s₂', wact T tau s₂ a s₂' ∧ R s₁' s₂') ∧
    (∀ d s₁', T.delay s₁ d s₁' → ∃ s₂', wdelay T tau s₂ d s₂' ∧ R s₁' s₂') ∧
    (∀ a s₂', T.act s₂ a s₂' → ∃ s₁', wact T tau s₁ a s₁' ∧ R s₁' s₂') ∧
    (∀ d s₂', T.delay s₂ d s₂' → ∃ s₁', wdelay T tau s₁ d s₁' ∧ R s₁' s₂')

/-- `s ≈ s'`: *weakly timed bisimilar* — some weak timed
bisimulation relates them. -/
def WeaklyTimedBisimilar (T : TLTS Proc Act) (tau : Act) (s s' : Proc) : Prop :=
  ∃ R, IsWeakTimedBisimulation T tau R ∧ R s s'

/-- The identity relation is a weak timed bisimulation. -/
theorem isWeakTimedBisimulation_eq (T : TLTS Proc Act) (tau : Act) :
    IsWeakTimedBisimulation T tau (· = ·) := by
  rintro s _ rfl
  exact ⟨fun a s' h => ⟨s', act_wact h, rfl⟩, fun d s' h => ⟨s', delay_wdelay h, rfl⟩,
         fun a s' h => ⟨s', act_wact h, rfl⟩, fun d s' h => ⟨s', delay_wdelay h, rfl⟩⟩

/-- The converse of a weak timed bisimulation is a weak timed bisimulation. -/
theorem IsWeakTimedBisimulation.symm {T : TLTS Proc Act} {tau : Act} {R : Proc → Proc → Prop}
    (h : IsWeakTimedBisimulation T tau R) : IsWeakTimedBisimulation T tau (fun s t => R t s) := by
  intro s₁ s₂ hr
  obtain ⟨ha1, hd1, ha2, hd2⟩ := h hr
  exact ⟨ha2, hd2, ha1, hd1⟩

/-- Weak timed bisimilarity is reflexive: `s ≈ s`. -/
theorem weaklyTimedBisimilar_refl (T : TLTS Proc Act) (tau : Act) (s : Proc) :
    WeaklyTimedBisimilar T tau s s :=
  ⟨(· = ·), isWeakTimedBisimulation_eq T tau, rfl⟩

/-- Weak timed bisimilarity is symmetric: `s ≈ s' → s' ≈ s`. -/
theorem WeaklyTimedBisimilar.symm {T : TLTS Proc Act} {tau : Act} {s s' : Proc}
    (h : WeaklyTimedBisimilar T tau s s') : WeaklyTimedBisimilar T tau s' s :=
  let ⟨_, hR, hr⟩ := h; ⟨_, hR.symm, hr⟩

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

/-- Timed bisimilarity refines weak timed bisimilarity:
`s ~ s'` implies `s ≈ s'`. -/
theorem TimedBisimilar.weaklyTimedBisimilar {T : TLTS Proc Act} {tau : Act} {s s' : Proc}
    (h : TimedBisimilar T s s') : WeaklyTimedBisimilar T tau s s' :=
  ⟨TimedBisimilar T, isWeakTimedBisimulation_of_timedBisimilar T tau, h⟩

end TLTS

end DeepWiki.ReactiveSystems
