import DeepWiki.ReactiveSystems.BisimulationWeak
import DeepWiki.ReactiveSystems.Ccs

/-! # Weak bisimilarity is a congruence
Observational equivalence `≈` is a congruence for prefixing, parallel
composition, relabelling and restriction (but *not* for choice). Each
case lifts a weak transition through the operator: `tauStar`/`WeakStep` lift
through `par`, `relabel` (for a genuine relabelling, fixing `τ`) and `restrict`
(when `τ` is not restricted), and the weak bisimulation is the operator applied to
the `≈`-related pair. The parallel case's synchronisation (`com3`) is the subtle
one: a weak `ℓ`-transition of one component synchronises with a single `ℓ̄`-step of
the other into a weak `τ`-move. -/

namespace DeepWiki.ReactiveSystems

open LTS

variable {Name K : Type*} (defn : K → CCS Name K)

/-! ### tauStar / WeakStep lifting helpers through par-left -/

theorem tauStar_par_left {P P' : CCS Name K} (R : CCS Name K)
    (h : tauStar (ccsLTS defn) Act.tau P P') :
    tauStar (ccsLTS defn) Act.tau (CCS.par P R) (CCS.par P' R) := by
  induction h with
  | refl => exact tauStar_refl _ _ _
  | @tail b c _hchain hstep ih =>
      exact tauStar_trans ih (tauStar_single (by
        rw [ccsLTS_step] at hstep ⊢; exact Step.com1 hstep))

theorem tauStar_par_right {P P' : CCS Name K} (R : CCS Name K)
    (h : tauStar (ccsLTS defn) Act.tau P P') :
    tauStar (ccsLTS defn) Act.tau (CCS.par R P) (CCS.par R P') := by
  induction h with
  | refl => exact tauStar_refl _ _ _
  | @tail b c _hchain hstep ih =>
      exact tauStar_trans ih (tauStar_single (by
        rw [ccsLTS_step] at hstep ⊢; exact Step.com2 hstep))

theorem weakStep_par_left {P : CCS Name K} {α : Act Name} {P' : CCS Name K} (R : CCS Name K)
    (h : (ccsLTS defn) ⊢ P =[α]⇒[Act.tau] P') :
    (ccsLTS defn) ⊢ CCS.par P R =[α]⇒[Act.tau] CCS.par P' R := by
  rcases h with ⟨hα, hts⟩ | ⟨hα, p₁, p₂, h₁, hstep, h₂⟩
  · exact Or.inl ⟨hα, tauStar_par_left defn R hts⟩
  · refine Or.inr ⟨hα, CCS.par p₁ R, CCS.par p₂ R, tauStar_par_left defn R h₁, ?_,
      tauStar_par_left defn R h₂⟩
    rw [ccsLTS_step] at hstep ⊢; exact Step.com1 hstep

theorem weakStep_par_right {P : CCS Name K} {α : Act Name} {P' : CCS Name K} (R : CCS Name K)
    (h : (ccsLTS defn) ⊢ P =[α]⇒[Act.tau] P') :
    (ccsLTS defn) ⊢ CCS.par R P =[α]⇒[Act.tau] CCS.par R P' := by
  rcases h with ⟨hα, hts⟩ | ⟨hα, p₁, p₂, h₁, hstep, h₂⟩
  · exact Or.inl ⟨hα, tauStar_par_right defn R hts⟩
  · refine Or.inr ⟨hα, CCS.par R p₁, CCS.par R p₂, tauStar_par_right defn R h₁, ?_,
      tauStar_par_right defn R h₂⟩
    rw [ccsLTS_step] at hstep ⊢; exact Step.com2 hstep

/-! ### tauStar / WeakStep lifting helpers through relabel -/

theorem tauStar_relabel {P P' : CCS Name K} (f : Act Name → Act Name)
    (hf : IsRelabelling f) (h : tauStar (ccsLTS defn) Act.tau P P') :
    tauStar (ccsLTS defn) Act.tau (CCS.relabel P f) (CCS.relabel P' f) := by
  induction h with
  | refl => exact tauStar_refl _ _ _
  | @tail b c _hchain hstep ih =>
      refine tauStar_trans ih (tauStar_single ?_)
      rw [ccsLTS_step] at hstep ⊢
      have : f Act.tau = Act.tau := hf.map_tau
      rw [← this]; exact Step.rel hstep

theorem weakStep_relabel {P : CCS Name K} {α : Act Name} {P' : CCS Name K}
    (f : Act Name → Act Name) (hf : IsRelabelling f)
    (h : (ccsLTS defn) ⊢ P =[α]⇒[Act.tau] P') :
    (ccsLTS defn) ⊢ CCS.relabel P f =[f α]⇒[Act.tau] CCS.relabel P' f := by
  rcases h with ⟨hα, hts⟩ | ⟨hα, p₁, p₂, h₁, hstep, h₂⟩
  · subst hα; rw [hf.map_tau]; exact Or.inl ⟨rfl, tauStar_relabel defn f hf hts⟩
  · rw [ccsLTS_step] at hstep
    by_cases hfα : f α = Act.tau
    · -- the relabelled visible step collapses to a τ-move
      rw [hfα]
      refine Or.inl ⟨rfl, ?_⟩
      refine tauStar_trans (tauStar_relabel defn f hf h₁) ?_
      refine tauStar_trans (tauStar_single ?_) (tauStar_relabel defn f hf h₂)
      rw [ccsLTS_step, ← hfα]; exact Step.rel hstep
    · refine Or.inr ⟨hfα, CCS.relabel p₁ f, CCS.relabel p₂ f,
        tauStar_relabel defn f hf h₁, ?_, tauStar_relabel defn f hf h₂⟩
      rw [ccsLTS_step]; exact Step.rel hstep

/-! ### tauStar / WeakStep lifting helpers through restrict -/

theorem tauStar_restrict {P P' : CCS Name K} (Lr : Set (Act Name))
    (htau : Act.tau ∉ Lr) (h : tauStar (ccsLTS defn) Act.tau P P') :
    tauStar (ccsLTS defn) Act.tau (CCS.restrict P Lr) (CCS.restrict P' Lr) := by
  induction h with
  | refl => exact tauStar_refl _ _ _
  | @tail b c _hchain hstep ih =>
      refine tauStar_trans ih (tauStar_single ?_)
      rw [ccsLTS_step] at hstep ⊢
      exact Step.res htau (by rw [Act.co_tau]; exact htau) hstep

theorem weakStep_restrict {P : CCS Name K} {α : Act Name} {P' : CCS Name K} (Lr : Set (Act Name))
    (htau : Act.tau ∉ Lr) (hαL : α ∉ Lr) (hαcoL : α.co ∉ Lr)
    (h : (ccsLTS defn) ⊢ P =[α]⇒[Act.tau] P') :
    (ccsLTS defn) ⊢ CCS.restrict P Lr =[α]⇒[Act.tau] CCS.restrict P' Lr := by
  rcases h with ⟨hα, hts⟩ | ⟨hα, p₁, p₂, h₁, hstep, h₂⟩
  · exact Or.inl ⟨hα, tauStar_restrict defn Lr htau hts⟩
  · refine Or.inr ⟨hα, CCS.restrict p₁ Lr, CCS.restrict p₂ Lr,
      tauStar_restrict defn Lr htau h₁, ?_, tauStar_restrict defn Lr htau h₂⟩
    rw [ccsLTS_step] at hstep ⊢; exact Step.res hαL hαcoL hstep

/-! ### Weak bisimilarity is a congruence (not for choice) -/

theorem weak_cong_pre {a : Act Name} {P Q : CCS Name K}
    (h : P ≈[ccsLTS defn, Act.tau] Q) : CCS.pre a P ≈[ccsLTS defn, Act.tau] CCS.pre a Q := by
  refine IsWeakBisimulation.le_weaklyBisimilar
    (R := fun x y => (x = CCS.pre a P ∧ y = CCS.pre a Q) ∨ x ≈[ccsLTS defn, Act.tau] y)
    ?_ (Or.inl ⟨rfl, rfl⟩)
  rintro x y (⟨rfl, rfl⟩ | hb)
  · constructor
    · intro α x' hstep
      rw [ccsLTS_step, step_pre_iff] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨Q, step_weakStep (Step.act _ _), Or.inr h⟩
    · intro α y' hstep
      rw [ccsLTS_step, step_pre_iff] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨P, step_weakStep (Step.act _ _), Or.inr h⟩
  · obtain ⟨h1, h2⟩ := isWeakBisimulation_weaklyBisimilar hb
    exact ⟨fun α x' hs => (h1 α x' hs).imp fun _ hy => ⟨hy.1, Or.inr hy.2⟩,
           fun α y' hs => (h2 α y' hs).imp fun _ hx => ⟨hx.1, Or.inr hx.2⟩⟩

theorem weak_cong_par_left {P Q : CCS Name K} (R : CCS Name K)
    (h : P ≈[ccsLTS defn, Act.tau] Q) :
    CCS.par P R ≈[ccsLTS defn, Act.tau] CCS.par Q R := by
  refine IsWeakBisimulation.le_weaklyBisimilar
    (R := fun x y => ∃ A B S, x = CCS.par A S ∧ y = CCS.par B S ∧
      A ≈[ccsLTS defn, Act.tau] B)
    ?_ ⟨P, Q, R, rfl, rfl, h⟩
  rintro x y ⟨A, B, S, rfl, rfl, hAB⟩
  obtain ⟨hf, hb⟩ := isWeakBisimulation_weaklyBisimilar hAB
  constructor
  · intro α x' hstep
    rw [ccsLTS_step, step_par_iff] at hstep
    rcases hstep with ⟨A', hsA, rfl⟩ | ⟨S', hsS, rfl⟩
        | ⟨ℓ, A', S', rfl, hℓ, hsA, hsS, rfl⟩
    · obtain ⟨B', hwB, hb'⟩ := hf α A' hsA
      exact ⟨CCS.par B' S, weakStep_par_left defn S hwB, A', B', S, rfl, rfl, hb'⟩
    · refine ⟨CCS.par B S', step_weakStep (Step.com2 hsS), A, B, S', rfl, rfl, hAB⟩
    · obtain ⟨B', hwB, hb'⟩ := hf ℓ A' hsA
      rcases hwB with ⟨hτ, _⟩ | ⟨_, b₁, b₂, hB1, hBstep, hB2⟩
      · exact absurd hτ hℓ
      · refine ⟨CCS.par B' S', ?_, A', B', S', rfl, rfl, hb'⟩
        refine Or.inl ⟨rfl, ?_⟩
        refine tauStar_trans (tauStar_par_left defn S hB1) ?_
        refine tauStar_trans (tauStar_single ?_) (tauStar_par_left defn S' hB2)
        rw [ccsLTS_step]; exact Step.com3 hℓ hBstep hsS
  · intro α y' hstep
    rw [ccsLTS_step, step_par_iff] at hstep
    rcases hstep with ⟨B', hsB, rfl⟩ | ⟨S', hsS, rfl⟩
        | ⟨ℓ, B', S', rfl, hℓ, hsB, hsS, rfl⟩
    · obtain ⟨A', hwA, hb'⟩ := hb α B' hsB
      exact ⟨CCS.par A' S, weakStep_par_left defn S hwA, A', B', S, rfl, rfl, hb'⟩
    · refine ⟨CCS.par A S', step_weakStep (Step.com2 hsS), A, B, S', rfl, rfl, hAB⟩
    · obtain ⟨A', hwA, hb'⟩ := hb ℓ B' hsB
      rcases hwA with ⟨hτ, _⟩ | ⟨_, a₁, a₂, hA1, hAstep, hA2⟩
      · exact absurd hτ hℓ
      · refine ⟨CCS.par A' S', ?_, A', B', S', rfl, rfl, hb'⟩
        refine Or.inl ⟨rfl, ?_⟩
        refine tauStar_trans (tauStar_par_left defn S hA1) ?_
        refine tauStar_trans (tauStar_single ?_) (tauStar_par_left defn S' hA2)
        rw [ccsLTS_step]; exact Step.com3 hℓ hAstep hsS

theorem weak_cong_par_right {P Q : CCS Name K} (R : CCS Name K)
    (h : P ≈[ccsLTS defn, Act.tau] Q) :
    CCS.par R P ≈[ccsLTS defn, Act.tau] CCS.par R Q := by
  refine IsWeakBisimulation.le_weaklyBisimilar
    (R := fun x y => ∃ S A B, x = CCS.par S A ∧ y = CCS.par S B ∧
      A ≈[ccsLTS defn, Act.tau] B)
    ?_ ⟨R, P, Q, rfl, rfl, h⟩
  rintro x y ⟨S, A, B, rfl, rfl, hAB⟩
  obtain ⟨hf, hb⟩ := isWeakBisimulation_weaklyBisimilar hAB
  constructor
  · intro α x' hstep
    rw [ccsLTS_step, step_par_iff] at hstep
    rcases hstep with ⟨S', hsS, rfl⟩ | ⟨A', hsA, rfl⟩
        | ⟨ℓ, S', A', rfl, hℓ, hsS, hsA, rfl⟩
    · refine ⟨CCS.par S' B, step_weakStep (Step.com1 hsS), S', A, B, rfl, rfl, hAB⟩
    · obtain ⟨B', hwB, hb'⟩ := hf α A' hsA
      exact ⟨CCS.par S B', weakStep_par_right defn S hwB, S, A', B', rfl, rfl, hb'⟩
    · obtain ⟨B', hwB, hb'⟩ := hf ℓ.co A' hsA
      rcases hwB with ⟨hτ, _⟩ | ⟨_, b₁, b₂, hB1, hBstep, hB2⟩
      · exact absurd hτ hℓ.co
      · refine ⟨CCS.par S' B', ?_, S', A', B', rfl, rfl, hb'⟩
        refine Or.inl ⟨rfl, ?_⟩
        refine tauStar_trans (tauStar_par_right defn S hB1) ?_
        refine tauStar_trans (tauStar_single ?_) (tauStar_par_right defn S' hB2)
        rw [ccsLTS_step]; exact Step.com3 hℓ hsS hBstep
  · intro α y' hstep
    rw [ccsLTS_step, step_par_iff] at hstep
    rcases hstep with ⟨S', hsS, rfl⟩ | ⟨B', hsB, rfl⟩
        | ⟨ℓ, S', B', rfl, hℓ, hsS, hsB, rfl⟩
    · refine ⟨CCS.par S' A, step_weakStep (Step.com1 hsS), S', A, B, rfl, rfl, hAB⟩
    · obtain ⟨A', hwA, hb'⟩ := hb α B' hsB
      exact ⟨CCS.par S A', weakStep_par_right defn S hwA, S, A', B', rfl, rfl, hb'⟩
    · obtain ⟨A', hwA, hb'⟩ := hb ℓ.co B' hsB
      rcases hwA with ⟨hτ, _⟩ | ⟨_, a₁, a₂, hA1, hAstep, hA2⟩
      · exact absurd hτ hℓ.co
      · refine ⟨CCS.par S' A', ?_, S', A', B', rfl, rfl, hb'⟩
        refine Or.inl ⟨rfl, ?_⟩
        refine tauStar_trans (tauStar_par_right defn S hA1) ?_
        refine tauStar_trans (tauStar_single ?_) (tauStar_par_right defn S' hA2)
        rw [ccsLTS_step]; exact Step.com3 hℓ hsS hAstep

theorem weak_cong_relabel {P Q : CCS Name K} (f : Act Name → Act Name)
    (hf : IsRelabelling f) (h : P ≈[ccsLTS defn, Act.tau] Q) :
    CCS.relabel P f ≈[ccsLTS defn, Act.tau] CCS.relabel Q f := by
  refine IsWeakBisimulation.le_weaklyBisimilar
    (R := fun x y => ∃ A B, x = CCS.relabel A f ∧ y = CCS.relabel B f ∧
      A ≈[ccsLTS defn, Act.tau] B)
    ?_ ⟨P, Q, rfl, rfl, h⟩
  rintro x y ⟨A, B, rfl, rfl, hAB⟩
  obtain ⟨hfwd, hbwd⟩ := isWeakBisimulation_weaklyBisimilar hAB
  constructor
  · intro β x' hstep
    rw [ccsLTS_step, step_relabel_iff] at hstep
    obtain ⟨α, A', rfl, hsA, rfl⟩ := hstep
    obtain ⟨B', hwB, hb'⟩ := hfwd α A' hsA
    exact ⟨CCS.relabel B' f, weakStep_relabel defn f hf hwB, A', B', rfl, rfl, hb'⟩
  · intro β y' hstep
    rw [ccsLTS_step, step_relabel_iff] at hstep
    obtain ⟨α, B', rfl, hsB, rfl⟩ := hstep
    obtain ⟨A', hwA, hb'⟩ := hbwd α B' hsB
    exact ⟨CCS.relabel A' f, weakStep_relabel defn f hf hwA, A', B', rfl, rfl, hb'⟩

theorem weak_cong_restrict {P Q : CCS Name K} (Lr : Set (Act Name)) (htau : Act.tau ∉ Lr)
    (h : P ≈[ccsLTS defn, Act.tau] Q) :
    CCS.restrict P Lr ≈[ccsLTS defn, Act.tau] CCS.restrict Q Lr := by
  refine IsWeakBisimulation.le_weaklyBisimilar
    (R := fun x y => ∃ A B, x = CCS.restrict A Lr ∧ y = CCS.restrict B Lr ∧
      A ≈[ccsLTS defn, Act.tau] B)
    ?_ ⟨P, Q, rfl, rfl, h⟩
  rintro x y ⟨A, B, rfl, rfl, hAB⟩
  obtain ⟨hfwd, hbwd⟩ := isWeakBisimulation_weaklyBisimilar hAB
  constructor
  · intro α x' hstep
    rw [ccsLTS_step, step_restrict_iff] at hstep
    obtain ⟨A', hαL, hαcoL, hsA, rfl⟩ := hstep
    obtain ⟨B', hwB, hb'⟩ := hfwd α A' hsA
    exact ⟨CCS.restrict B' Lr, weakStep_restrict defn Lr htau hαL hαcoL hwB,
      A', B', rfl, rfl, hb'⟩
  · intro α y' hstep
    rw [ccsLTS_step, step_restrict_iff] at hstep
    obtain ⟨B', hαL, hαcoL, hsB, rfl⟩ := hstep
    obtain ⟨A', hwA, hb'⟩ := hbwd α B' hsB
    exact ⟨CCS.restrict A' Lr, weakStep_restrict defn Lr htau hαL hαcoL hwA,
      A', B', rfl, rfl, hb'⟩

end DeepWiki.ReactiveSystems
