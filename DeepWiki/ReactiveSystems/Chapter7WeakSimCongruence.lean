import DeepWiki.ReactiveSystems.SimulationWeak
import DeepWiki.ReactiveSystems.Ccs

/-! # Exercise 7.10 — choice congruence of the weak-simulation preorder
If `Q` weakly simulates `P`, then `Q + R` weakly simulates both `P` and `P + R`,
for every CCS process `R`. The witnessing weak simulations extend the given one
`S` (with `S P Q`) by relating to `Q + R` everything `S`-related to `Q` — this
absorbs the case where `Q` answers a move by an *empty* `τ`-transition (staying
put), which `Q + R` can only match by staying at `Q + R` — and, for `P + R`, by
the identity (to answer the `R`-summand's own moves). -/

namespace DeepWiki.ReactiveSystems

open LTS

variable {Name K : Type*} {defn : K → CCS Name K}

/-- A move of `Q` lifts to the same move of the choice `Q + R` (the SUM₁ rule). -/
theorem step_choiceL {Q R Z : CCS Name K} {β : Act Name}
    (h : (ccsLTS defn) ⊢ Q ⟶[β] Z) : (ccsLTS defn) ⊢ (CCS.choice Q R) ⟶[β] Z :=
  Step.suml h

/-- A move of `R` lifts to the same move of the choice `Q + R` (the SUM₂ rule). -/
theorem step_choiceR {Q R Z : CCS Name K} {β : Act Name}
    (h : (ccsLTS defn) ⊢ R ⟶[β] Z) : (ccsLTS defn) ⊢ (CCS.choice Q R) ⟶[β] Z :=
  Step.sumr h

/-- A weak transition of `Q` is either the trivial empty `τ`-transition, or it lifts
to a weak transition of `Q + R` (whose first step is taken on the `Q`-summand). -/
theorem weakStep_choiceL_or (R : CCS Name K) {Q Q' : CCS Name K} {α : Act Name}
    (h : (ccsLTS defn) ⊢ Q =[α]⇒[Act.tau] Q') :
    (α = Act.tau ∧ Q' = Q) ∨ (ccsLTS defn) ⊢ (CCS.choice Q R) =[α]⇒[Act.tau] Q' := by
  rcases h with ⟨rfl, hts⟩ | ⟨hα, Q₁, Q₂, h1, hstep, h2⟩
  · -- `α = τ`, `Q ⟶τ* Q'`
    rcases Relation.ReflTransGen.cases_head hts with rfl | ⟨Z, hQZ, hZQ'⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, Relation.ReflTransGen.head (step_choiceL hQZ) hZQ'⟩)
  · -- `α ≠ τ`, a visible weak step `Q ⟶τ* Q₁ ⟶α Q₂ ⟶τ* Q'`
    refine Or.inr (Or.inr ⟨hα, ?_⟩)
    rcases Relation.ReflTransGen.cases_head h1 with rfl | ⟨Z, hQZ, hZQ₁⟩
    · -- empty leading `τ`: the visible step is from `Q` itself
      exact ⟨CCS.choice Q R, Q₂, Relation.ReflTransGen.refl, step_choiceL hstep, h2⟩
    · -- nonempty leading `τ`: lift its first step onto the `Q`-summand
      exact ⟨Q₁, Q₂, Relation.ReflTransGen.head (step_choiceL hQZ) hZQ₁, hstep, h2⟩

/-- **Exercise 7.10** (§7.3, p.152), first part. If `Q` weakly simulates `P` then
`Q + R` weakly simulates `P`. -/
theorem weaklySimulates_choiceL {P Q R : CCS Name K}
    (h : WeaklySimulates (ccsLTS defn) Act.tau Q P) :
    WeaklySimulates (ccsLTS defn) Act.tau (CCS.choice Q R) P := by
  obtain ⟨S, hSweak, hSPQ⟩ := h
  refine ⟨fun s₁ s₂ => (s₂ = CCS.choice Q R ∧ S s₁ Q) ∨ S s₁ s₂, ?_, Or.inl ⟨rfl, hSPQ⟩⟩
  rintro s₁ s₂ (⟨rfl, hSs₁Q⟩ | hS) α s₁' hstep
  · obtain ⟨Q', hQw, hS'⟩ := hSweak hSs₁Q α s₁' hstep
    rcases weakStep_choiceL_or R hQw with ⟨rfl, hQeq⟩ | hCw
    · exact ⟨CCS.choice Q R, weakStep_tau_of_tauStar (tauStar_refl _ _ _),
        Or.inl ⟨rfl, hQeq ▸ hS'⟩⟩
    · exact ⟨Q', hCw, Or.inr hS'⟩
  · obtain ⟨s₂', hw, hS2⟩ := hSweak hS α s₁' hstep
    exact ⟨s₂', hw, Or.inr hS2⟩

/-- **Exercise 7.10** (§7.3, p.152), second part. If `Q` weakly simulates `P` then
`Q + R` weakly simulates `P + R`. -/
theorem weaklySimulates_choiceLR {P Q R : CCS Name K}
    (h : WeaklySimulates (ccsLTS defn) Act.tau Q P) :
    WeaklySimulates (ccsLTS defn) Act.tau (CCS.choice Q R) (CCS.choice P R) := by
  obtain ⟨S, hSweak, hSPQ⟩ := h
  refine ⟨fun s₁ s₂ =>
    (s₁ = CCS.choice P R ∧ s₂ = CCS.choice Q R) ∨ (s₂ = CCS.choice Q R ∧ S s₁ Q) ∨
      S s₁ s₂ ∨ s₁ = s₂, ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro s₁ s₂ (⟨rfl, rfl⟩ | ⟨rfl, hSs₁Q⟩ | hS | rfl) α s₁' hstep
  · -- `(P + R) ⟶α s₁'` is a move of `P` or of `R`
    rw [ccsLTS_step, step_choice_iff] at hstep
    rcases hstep with hP | hR
    · obtain ⟨Q', hQw, hS'⟩ := hSweak hSPQ α s₁' hP
      rcases weakStep_choiceL_or R hQw with ⟨rfl, hQeq⟩ | hCw
      · exact ⟨CCS.choice Q R, weakStep_tau_of_tauStar (tauStar_refl _ _ _),
          Or.inr (Or.inl ⟨rfl, hQeq ▸ hS'⟩)⟩
      · exact ⟨Q', hCw, Or.inr (Or.inr (Or.inl hS'))⟩
    · exact ⟨s₁', step_weakStep (step_choiceR hR), Or.inr (Or.inr (Or.inr rfl))⟩
  · obtain ⟨Q', hQw, hS'⟩ := hSweak hSs₁Q α s₁' hstep
    rcases weakStep_choiceL_or R hQw with ⟨rfl, hQeq⟩ | hCw
    · exact ⟨CCS.choice Q R, weakStep_tau_of_tauStar (tauStar_refl _ _ _),
        Or.inr (Or.inl ⟨rfl, hQeq ▸ hS'⟩)⟩
    · exact ⟨Q', hCw, Or.inr (Or.inr (Or.inl hS'))⟩
  · obtain ⟨s₂', hw, hS2⟩ := hSweak hS α s₁' hstep
    exact ⟨s₂', hw, Or.inr (Or.inr (Or.inl hS2))⟩
  · exact ⟨s₁', step_weakStep hstep, Or.inr (Or.inr (Or.inr rfl))⟩

end DeepWiki.ReactiveSystems
