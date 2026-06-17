import DeepWiki.ReactiveSystems.Ccs
import DeepWiki.ReactiveSystems.Bisimulation

/-! # Strong bisimilarity is a congruence for CCS
Strong bisimilarity over the CCS transition system is preserved by every process
operator: prefixing, choice, parallel composition, restriction and relabelling.
Each proof exhibits a bisimulation built from the contextualised pairs (closed
under the relevant SOS rules) using the transition inversion lemmas. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Name K : Type*} {defn : K → CCS Name K}

/-- Congruence for action prefixing: `P ~ P' → a.P ~ a.P'`. -/
theorem bisimilar_pre {a : Act Name} {P P' : CCS Name K}
    (h : Bisimilar (ccsLTS defn) P P') :
    Bisimilar (ccsLTS defn) (CCS.pre a P) (CCS.pre a P') := by
  refine ⟨fun x y => (x = CCS.pre a P ∧ y = CCS.pre a P') ∨ Bisimilar (ccsLTS defn) x y,
    ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro x y (⟨rfl, rfl⟩ | hb)
  · constructor
    · intro α x' hstep
      rw [ccsLTS_step, step_pre_iff] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨P', Step.act _ _, Or.inr h⟩
    · intro α y' hstep
      rw [ccsLTS_step, step_pre_iff] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨P, Step.act _ _, Or.inr h⟩
  · obtain ⟨h1, h2⟩ := isBisimulation_bisimilar hb
    exact ⟨fun α x' hs => (h1 α x' hs).imp fun _ hy => ⟨hy.1, Or.inr hy.2⟩,
           fun α y' hs => (h2 α y' hs).imp fun _ hx => ⟨hx.1, Or.inr hx.2⟩⟩

/-- Congruence for choice: `P ~ P' → Q ~ Q' → P + Q ~ P' + Q'`. -/
theorem bisimilar_choice {P P' Q Q' : CCS Name K}
    (hP : Bisimilar (ccsLTS defn) P P') (hQ : Bisimilar (ccsLTS defn) Q Q') :
    Bisimilar (ccsLTS defn) (CCS.choice P Q) (CCS.choice P' Q') := by
  refine ⟨fun x y => (x = CCS.choice P Q ∧ y = CCS.choice P' Q') ∨ Bisimilar (ccsLTS defn) x y,
    ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro x y (⟨rfl, rfl⟩ | hb)
  · constructor
    · intro α x' hstep
      rw [ccsLTS_step, step_choice_iff] at hstep
      rcases hstep with h1 | h1
      · obtain ⟨y', hy', hb⟩ := ((bisimilar_iff P P').mp hP).1 α x' h1
        exact ⟨y', Step.suml hy', Or.inr hb⟩
      · obtain ⟨y', hy', hb⟩ := ((bisimilar_iff Q Q').mp hQ).1 α x' h1
        exact ⟨y', Step.sumr hy', Or.inr hb⟩
    · intro α y' hstep
      rw [ccsLTS_step, step_choice_iff] at hstep
      rcases hstep with h1 | h1
      · obtain ⟨x', hx', hb⟩ := ((bisimilar_iff P P').mp hP).2 α y' h1
        exact ⟨x', Step.suml hx', Or.inr hb⟩
      · obtain ⟨x', hx', hb⟩ := ((bisimilar_iff Q Q').mp hQ).2 α y' h1
        exact ⟨x', Step.sumr hx', Or.inr hb⟩
  · obtain ⟨h1, h2⟩ := isBisimulation_bisimilar hb
    exact ⟨fun α x' hs => (h1 α x' hs).imp fun _ hy => ⟨hy.1, Or.inr hy.2⟩,
           fun α y' hs => (h2 α y' hs).imp fun _ hx => ⟨hx.1, Or.inr hx.2⟩⟩

/-- Congruence for parallel composition: `P ~ P' → Q ~ Q' → P ∣ Q ~ P' ∣ Q'`. -/
theorem bisimilar_par {P P' Q Q' : CCS Name K}
    (hP : Bisimilar (ccsLTS defn) P P') (hQ : Bisimilar (ccsLTS defn) Q Q') :
    Bisimilar (ccsLTS defn) (CCS.par P Q) (CCS.par P' Q') := by
  refine ⟨fun x y => ∃ A A' B B', x = CCS.par A B ∧ y = CCS.par A' B' ∧
      Bisimilar (ccsLTS defn) A A' ∧ Bisimilar (ccsLTS defn) B B',
    ?_, ⟨P, P', Q, Q', rfl, rfl, hP, hQ⟩⟩
  rintro x y ⟨A, A', B, B', rfl, rfl, hA, hB⟩
  constructor
  · intro α x' hstep
    rw [ccsLTS_step, step_par_iff] at hstep
    rcases hstep with ⟨A1, hsA, rfl⟩ | ⟨B1, hsB, rfl⟩ | ⟨ℓ, A1, B1, rfl, hℓ, hsA, hsB, rfl⟩
    · obtain ⟨A1', hA', hb⟩ := ((bisimilar_iff A A').mp hA).1 α A1 hsA
      exact ⟨CCS.par A1' B', Step.com1 hA', A1, A1', B, B', rfl, rfl, hb, hB⟩
    · obtain ⟨B1', hB', hb⟩ := ((bisimilar_iff B B').mp hB).1 α B1 hsB
      exact ⟨CCS.par A' B1', Step.com2 hB', A, A', B1, B1', rfl, rfl, hA, hb⟩
    · obtain ⟨A1', hA', hbA⟩ := ((bisimilar_iff A A').mp hA).1 ℓ A1 hsA
      obtain ⟨B1', hB', hbB⟩ := ((bisimilar_iff B B').mp hB).1 ℓ.co B1 hsB
      exact ⟨CCS.par A1' B1', Step.com3 hℓ hA' hB', A1, A1', B1, B1', rfl, rfl, hbA, hbB⟩
  · intro α y' hstep
    rw [ccsLTS_step, step_par_iff] at hstep
    rcases hstep with ⟨A1', hsA', rfl⟩ | ⟨B1', hsB', rfl⟩ | ⟨ℓ, A1', B1', rfl, hℓ, hsA', hsB', rfl⟩
    · obtain ⟨A1, hA1, hb⟩ := ((bisimilar_iff A A').mp hA).2 α A1' hsA'
      exact ⟨CCS.par A1 B, Step.com1 hA1, A1, A1', B, B', rfl, rfl, hb, hB⟩
    · obtain ⟨B1, hB1, hb⟩ := ((bisimilar_iff B B').mp hB).2 α B1' hsB'
      exact ⟨CCS.par A B1, Step.com2 hB1, A, A', B1, B1', rfl, rfl, hA, hb⟩
    · obtain ⟨A1, hA1, hbA⟩ := ((bisimilar_iff A A').mp hA).2 ℓ A1' hsA'
      obtain ⟨B1, hB1, hbB⟩ := ((bisimilar_iff B B').mp hB).2 ℓ.co B1' hsB'
      exact ⟨CCS.par A1 B1, Step.com3 hℓ hA1 hB1, A1, A1', B1, B1', rfl, rfl, hbA, hbB⟩

/-- Congruence for restriction: `P ~ P' → P ∖ L ~ P' ∖ L`. -/
theorem bisimilar_restrict {P P' : CCS Name K} (Lr : Set (Act Name))
    (h : Bisimilar (ccsLTS defn) P P') :
    Bisimilar (ccsLTS defn) (CCS.restrict P Lr) (CCS.restrict P' Lr) := by
  refine ⟨fun x y => ∃ A A', x = CCS.restrict A Lr ∧ y = CCS.restrict A' Lr ∧
      Bisimilar (ccsLTS defn) A A', ?_, ⟨P, P', rfl, rfl, h⟩⟩
  rintro x y ⟨A, A', rfl, rfl, hA⟩
  constructor
  · intro α x' hstep
    rw [ccsLTS_step, step_restrict_iff] at hstep
    obtain ⟨A1, h1, h2, hsA, rfl⟩ := hstep
    obtain ⟨A1', hA', hb⟩ := ((bisimilar_iff A A').mp hA).1 α A1 hsA
    exact ⟨CCS.restrict A1' Lr, Step.res h1 h2 hA', A1, A1', rfl, rfl, hb⟩
  · intro α y' hstep
    rw [ccsLTS_step, step_restrict_iff] at hstep
    obtain ⟨A1', h1, h2, hsA', rfl⟩ := hstep
    obtain ⟨A1, hA1, hb⟩ := ((bisimilar_iff A A').mp hA).2 α A1' hsA'
    exact ⟨CCS.restrict A1 Lr, Step.res h1 h2 hA1, A1, A1', rfl, rfl, hb⟩

/-- Congruence for relabelling: `P ~ P' → P[f] ~ P'[f]`. -/
theorem bisimilar_relabel {P P' : CCS Name K} (f : Act Name → Act Name)
    (h : Bisimilar (ccsLTS defn) P P') :
    Bisimilar (ccsLTS defn) (CCS.relabel P f) (CCS.relabel P' f) := by
  refine ⟨fun x y => ∃ A A', x = CCS.relabel A f ∧ y = CCS.relabel A' f ∧
      Bisimilar (ccsLTS defn) A A', ?_, ⟨P, P', rfl, rfl, h⟩⟩
  rintro x y ⟨A, A', rfl, rfl, hA⟩
  constructor
  · intro β x' hstep
    rw [ccsLTS_step, step_relabel_iff] at hstep
    obtain ⟨α, A1, rfl, hsA, rfl⟩ := hstep
    obtain ⟨A1', hA', hb⟩ := ((bisimilar_iff A A').mp hA).1 α A1 hsA
    exact ⟨CCS.relabel A1' f, Step.rel hA', A1, A1', rfl, rfl, hb⟩
  · intro β y' hstep
    rw [ccsLTS_step, step_relabel_iff] at hstep
    obtain ⟨α, A1', rfl, hsA', rfl⟩ := hstep
    obtain ⟨A1, hA1, hb⟩ := ((bisimilar_iff A A').mp hA).2 α A1' hsA'
    exact ⟨CCS.relabel A1 f, Step.rel hA1, A1, A1', rfl, rfl, hb⟩

end LTS

end DeepWiki.ReactiveSystems
