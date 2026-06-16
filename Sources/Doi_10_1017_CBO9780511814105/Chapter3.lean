import DeepWiki.ReactiveSystems.Bisimulation
import DeepWiki.ReactiveSystems.BisimulationWeak
import DeepWiki.ReactiveSystems.Traces
import DeepWiki.ReactiveSystems.Simulation
import DeepWiki.ReactiveSystems.Ccs
import DeepWiki.ReactiveSystems.CcsCongruence
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 3: Behavioural equivalences
Book-numbered restatements for Chapter 3 (trace equivalence, strong and weak
bisimilarity), discharged by the `DeepWiki.ReactiveSystems` library, with solved
exercises. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems
open DeepWiki.ReactiveSystems.LTS

variable {Proc Act : Type*}

/-! ## §3.1 Criteria for good behavioural equivalence -/

/-- **Definition 3.1** (§3.1, p.32). An equivalence relation: reflexive,
symmetric and transitive. Reuses Mathlib's `Equivalence`. -/
abbrev def_3_1 := @Equivalence

/-- **Definition 3.1** (§3.1, p.32), preorder: a reflexive and transitive
relation. Reuses Mathlib's `Preorder`. -/
abbrev def_3_1_preorder := @Preorder

/-! ## §3.2 Trace equivalence -/

/-- **§3.2** (p.34), the trace set of a process: the action sequences it can
perform. The library's `LTS.Traces`. -/
abbrev traces := @LTS.Traces

/-- **§3.2** (p.35, eq. 3.1). Trace equivalence: equal trace sets. (This is the
unnumbered equation 3.1 of §3.2 — *not* book Definition 3.1.) The library's
`LTS.TraceEquiv`. -/
abbrev traceEquiv := @LTS.TraceEquiv

/-- **§3.2** (p.34–36). Strong bisimilarity implies trace equivalence (the
converse fails). -/
theorem bisimilar_traceEquiv (L : LTS Proc Act) {p q : Proc} (h : p ~[L] q) :
    TraceEquiv L p q := h.traceEquiv

/-! ## §3.3 Strong bisimilarity -/

/-- **Definition 3.2** (§3.3, p.37). A strong bisimulation `R`: whenever `R p q`,
every `a`-move of `p` is matched by an `a`-move of `q` into `R`, and
symmetrically. The library's `LTS.IsBisimulation`. -/
abbrev def_3_2 := @LTS.IsBisimulation

/-- **Definition 3.2** (§3.3, p.37), strong bisimilarity `~`: `p ~ q` iff some
strong bisimulation relates `p` and `q`. The library's `LTS.Bisimilar`. -/
abbrev def_3_2_bisimilar := @LTS.Bisimilar

/-- **Theorem 3.1**, part 1 (§3.3, p.42). For any LTS, `~` is an equivalence
relation. Discharged by `LTS.equivalence_bisimilar`. -/
theorem thm_3_1_equivalence (L : LTS Proc Act) : Equivalence (LTS.Bisimilar L) :=
  LTS.equivalence_bisimilar

/-- **Theorem 3.1**, part 2 (§3.3, p.42). `~` is the largest strong bisimulation:
it is itself a strong bisimulation, and contains every strong bisimulation. -/
theorem thm_3_1_largest (L : LTS Proc Act) :
    LTS.IsBisimulation L (LTS.Bisimilar L) ∧
      ∀ R, LTS.IsBisimulation L R → ∀ ⦃p q⦄, R p q → (p ~[L] q) :=
  ⟨LTS.isBisimulation_bisimilar, fun _ hR => hR.le_bisimilar⟩

/-- **Theorem 3.1**, part 3 (§3.3, p.42, eq. 3.3). `~` satisfies the
bisimulation transfer property. Discharged by `LTS.bisimilar_iff`. -/
theorem thm_3_1_transfer (L : LTS Proc Act) (p q : Proc) :
    (p ~[L] q) ↔
      (∀ a p', (L ⊢ p ⟶[a] p') → ∃ q', (L ⊢ q ⟶[a] q') ∧ (p' ~[L] q')) ∧
      (∀ a q', (L ⊢ q ⟶[a] q') → ∃ p', (L ⊢ p ⟶[a] p') ∧ (p' ~[L] q')) :=
  LTS.bisimilar_iff p q

/-! ## §3.3 Strong bisimilarity is a congruence (Theorem 3.2) -/

/-- **Theorem 3.2** (§3.3), prefix congruence: `P ~ P' → a.P ~ a.P'`. -/
theorem thm_3_2_pre {Name K : Type*} {defn : K → CCS Name K} {a}
    {P P' : CCS Name K} (h : P ~[ccsLTS defn] P') :
    (CCS.pre a P) ~[ccsLTS defn] (CCS.pre a P') := LTS.bisimilar_pre h

/-- **Theorem 3.2** (§3.3), choice congruence: `P ~ P' → Q ~ Q' → P+Q ~ P'+Q'`. -/
theorem thm_3_2_choice {Name K : Type*} {defn : K → CCS Name K} {P P' Q Q' : CCS Name K}
    (hP : P ~[ccsLTS defn] P') (hQ : Q ~[ccsLTS defn] Q') :
    (CCS.choice P Q) ~[ccsLTS defn] (CCS.choice P' Q') := LTS.bisimilar_choice hP hQ

/-- **Theorem 3.2** (§3.3), parallel congruence: `P ~ P' → Q ~ Q' → P∣Q ~ P'∣Q'`
(the hard case, via the SOS synchronisation rule). -/
theorem thm_3_2_par {Name K : Type*} {defn : K → CCS Name K} {P P' Q Q' : CCS Name K}
    (hP : P ~[ccsLTS defn] P') (hQ : Q ~[ccsLTS defn] Q') :
    (CCS.par P Q) ~[ccsLTS defn] (CCS.par P' Q') := LTS.bisimilar_par hP hQ

/-- **Theorem 3.2** (§3.3), restriction congruence: `P ~ P' → P∖L ~ P'∖L`. -/
theorem thm_3_2_restrict {Name K : Type*} {defn : K → CCS Name K} {Lr}
    {P P' : CCS Name K} (h : P ~[ccsLTS defn] P') :
    (CCS.restrict P Lr) ~[ccsLTS defn] (CCS.restrict P' Lr) := LTS.bisimilar_restrict Lr h

/-- **Theorem 3.2** (§3.3), relabelling congruence: `P ~ P' → P[f] ~ P'[f]`. -/
theorem thm_3_2_relabel {Name K : Type*} {defn : K → CCS Name K} {f}
    {P P' : CCS Name K} (h : P ~[ccsLTS defn] P') :
    (CCS.relabel P f) ~[ccsLTS defn] (CCS.relabel P' f) := LTS.bisimilar_relabel f h

/-! ## §3.3 Simulation and the simulation preorder (Exercises 3.17–3.18) -/

/-- **Exercise 3.17** (§3.3). A simulation: a one-sided bisimulation. The
library's `LTS.IsSimulation`. -/
abbrev simulation := @LTS.IsSimulation

/-- **Exercise 3.17** (§3.3), the simulation preorder `⊑`. The library's
`LTS.Simulated`. -/
abbrev simulationPreorder := @LTS.Simulated

/-- **Exercise 3.17** (§3.3). The simulation preorder is a preorder (reflexive
and transitive), and strong bisimilarity refines it (`p ~ q → p ⊑ q`). -/
theorem ex_3_17 (L : LTS Proc Act) :
    ((∀ p, p ⊑[L] p) ∧ (∀ p q r, (p ⊑[L] q) → (q ⊑[L] r) → (p ⊑[L] r))) ∧
      (∀ p q, p ~[L] q → p ⊑[L] q) :=
  ⟨LTS.simulated_preorder L, fun _ _ h => h.simulated⟩

/-- **Exercise 3.18** (§3.3), ready simulation: a simulation that also preserves
ready sets. The library's `LTS.IsReadySimulation`. -/
abbrev ex_3_18 := @LTS.IsReadySimulation

/-- **Exercise 3.6** (§3.3). The identity relation, the inverse of a strong
bisimulation, and the composition of two strong bisimulations are all strong
bisimulations. -/
theorem ex_3_6 (L : LTS Proc Act) :
    LTS.IsBisimulation L (· = ·) ∧
      (∀ {R}, LTS.IsBisimulation L R → LTS.IsBisimulation L (fun p q => R q p)) ∧
      (∀ {R S}, LTS.IsBisimulation L R → LTS.IsBisimulation L S →
        LTS.IsBisimulation L (fun p r => ∃ q, R p q ∧ S q r)) :=
  ⟨LTS.isBisimulation_eq, fun h => h.inv, fun hR hS => hR.comp hS⟩

/-- **Exercise 3.7** (§3.3). The union of all strong bisimulations — strong
bisimilarity — is itself a strong bisimulation. -/
theorem ex_3_7 (L : LTS Proc Act) : LTS.IsBisimulation L (LTS.Bisimilar L) :=
  LTS.isBisimulation_bisimilar

/-! ## §3.4 Weak bisimilarity -/

/-- **Definition 3.3** (§3.4, p.56), weak transition `p =α⇒ q`: silent steps
around an observable `α` (or just silent steps when `α = τ`). The library's
`LTS.WeakStep`. -/
abbrev def_3_3 := @LTS.WeakStep

/-- **Definition 3.4** (§3.4, p.57). A weak bisimulation matches each concrete
move by a weak transition. The library's `LTS.IsWeakBisimulation`. -/
abbrev def_3_4 := @LTS.IsWeakBisimulation

/-- **Definition 3.4** (§3.4, p.57), weak bisimilarity / observational
equivalence `≈`. The library's `LTS.WeaklyBisimilar`. -/
abbrev def_3_4_weaklyBisimilar := @LTS.WeaklyBisimilar

/-- **§3.4** (p.57). Weak bisimilarity is an equivalence relation. -/
theorem weaklyBisimilar_equivalence (L : LTS Proc Act) (tau : Act) :
    Equivalence (LTS.WeaklyBisimilar L tau) := LTS.equivalence_weaklyBisimilar

/-- **§3.4** (p.57). Strong bisimilarity refines weak bisimilarity: `~ ⊆ ≈`. -/
theorem bisimilar_weaklyBisimilar (L : LTS Proc Act) (tau : Act) {p q : Proc}
    (h : p ~[L] q) : p ≈[L, tau] q := h.weaklyBisimilar

/-- **Theorem 3.3 / Exercise 3.30** (§3.4). Observational equivalence `≈` is the
largest weak bisimulation: it is itself a weak bisimulation and contains every
weak bisimulation. -/
theorem thm_3_3_largest (L : LTS Proc Act) (tau : Act) :
    LTS.IsWeakBisimulation L tau (LTS.WeaklyBisimilar L tau) ∧
      ∀ R, LTS.IsWeakBisimulation L tau R → ∀ ⦃p q⦄, R p q → p ≈[L, tau] q :=
  ⟨LTS.isWeakBisimulation_weaklyBisimilar, fun _ hR => hR.le_weaklyBisimilar⟩

/-! ## Solved exercises

Channel names `a, b, c` for the worked CCS exercises. -/

/-- Channel names `a, b, c` for the Chapter 3 CCS exercises. -/
inductive Chan | a | b | c
  deriving DecidableEq

/-- Empty definition environment (no process constants). -/
def noDefs : Empty → CCS Chan Empty := fun e => e.elim

/-- `a.(b.0 + c.0)` — process `P` of Exercise 3.4. -/
def ex34P : CCS Chan Empty := ⟪ (.name .a) ▸ ((.name .b) ▸ 𝟬 + (.name .c) ▸ 𝟬) ⟫

/-- `a.b.0 + a.c.0` — process `Q` of Exercise 3.4. -/
def ex34Q : CCS Chan Empty :=
  ⟪ (.name .a) ▸ (.name .b) ▸ 𝟬 + (.name .a) ▸ (.name .c) ▸ 𝟬 ⟫

/-- **Exercise 3.4** (§3.3, p.41). `a.(b.0+c.0)` and `a.b.0+a.c.0` are *not*
strongly bisimilar: after the common `a`, one side can still do both `b` and
`c`, the other has already committed. -/
theorem ex_3_4 : ¬ (ex34P ~[ccsLTS noDefs] ex34Q) := by
  intro h
  have hPa : (ccsLTS noDefs) ⊢ ex34P ⟶[.name .a] ⟪ (.name .b) ▸ 𝟬 + (.name .c) ▸ 𝟬 ⟫ :=
    Step.act _ _
  obtain ⟨Q', hQ', hbis⟩ := ((bisimilar_iff _ _).mp h).1 (.name .a) _ hPa
  simp only [ccsLTS_step, ex34Q, step_choice_iff, step_pre_iff] at hQ'
  rcases hQ' with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · have hc : (ccsLTS noDefs) ⊢ ⟪ (.name .b) ▸ 𝟬 + (.name .c) ▸ 𝟬 ⟫ ⟶[.name .c]
        (⟪ 𝟬 ⟫ : CCS Chan Empty) := Step.sumr (Step.act _ _)
    obtain ⟨q'', hq'', _⟩ := ((bisimilar_iff _ _).mp hbis).1 (.name .c) _ hc
    simp only [ccsLTS_step, step_pre_iff] at hq''
    exact absurd hq''.1 (by decide)
  · have hb : (ccsLTS noDefs) ⊢ ⟪ (.name .b) ▸ 𝟬 + (.name .c) ▸ 𝟬 ⟫ ⟶[.name .b]
        (⟪ 𝟬 ⟫ : CCS Chan Empty) := Step.suml (Step.act _ _)
    obtain ⟨q'', hq'', _⟩ := ((bisimilar_iff _ _).mp hbis).1 (.name .b) _ hb
    simp only [ccsLTS_step, step_pre_iff] at hq''
    exact absurd hq''.1 (by decide)

/-- Process constants for Exercise 3.3. -/
inductive Ex33K | P | P₁ | Q | Q₁ | Q₂ | Q₃
  deriving DecidableEq

/-- The recursive process definitions of Exercise 3.3: `P ≝ a.P₁`,
`P₁ ≝ b.P + c.P`, `Q ≝ a.Q₁`, `Q₁ ≝ b.Q₂ + c.Q`, `Q₂ ≝ a.Q₃`,
`Q₃ ≝ b.Q + c.Q₂`. -/
def ex33defn : Ex33K → CCS Chan Ex33K
  | .P => ⟪ (.name .a) ▸ ‹.const .P₁› ⟫
  | .P₁ => ⟪ (.name .b) ▸ ‹.const .P› + (.name .c) ▸ ‹.const .P› ⟫
  | .Q => ⟪ (.name .a) ▸ ‹.const .Q₁› ⟫
  | .Q₁ => ⟪ (.name .b) ▸ ‹.const .Q₂› + (.name .c) ▸ ‹.const .Q› ⟫
  | .Q₂ => ⟪ (.name .a) ▸ ‹.const .Q₃› ⟫
  | .Q₃ => ⟪ (.name .b) ▸ ‹.const .Q› + (.name .c) ▸ ‹.const .Q₂› ⟫

/-- A strong bisimulation witnessing `P ~ Q` for Exercise 3.3. -/
def ex33R : CCS Chan Ex33K → CCS Chan Ex33K → Prop := fun p q =>
  (p = .const .P ∧ q = .const .Q) ∨ (p = .const .P ∧ q = .const .Q₂) ∨
  (p = .const .P₁ ∧ q = .const .Q₁) ∨ (p = .const .P₁ ∧ q = .const .Q₃)

/-- **Exercise 3.3** (§3.3, p.41). The processes `P ≝ a.P₁`, `P₁ ≝ b.P + c.P`
and `Q ≝ a.Q₁`, `Q₁ ≝ b.Q₂ + c.Q`, `Q₂ ≝ a.Q₃`, `Q₃ ≝ b.Q + c.Q₂` are strongly
bisimilar, witnessed by `ex33R = {(P,Q),(P,Q₂),(P₁,Q₁),(P₁,Q₃)}`. -/
theorem ex_3_3 : (CCS.const Ex33K.P) ~[ccsLTS ex33defn] (CCS.const Ex33K.Q) := by
  refine ⟨ex33R, ?_, Or.inl ⟨rfl, rfl⟩⟩
  intro p q hpq
  simp only [ex33R] at hpq
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨fun α p' hstep => ?_, fun α q' hstep => ?_⟩
    · simp only [ccsLTS_step, step_const_iff, ex33defn, step_pre_iff] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨.const Ex33K.Q₁, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩
    · simp only [ccsLTS_step, step_const_iff, ex33defn, step_pre_iff] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨.const Ex33K.P₁, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩
  · refine ⟨fun α p' hstep => ?_, fun α q' hstep => ?_⟩
    · simp only [ccsLTS_step, step_const_iff, ex33defn, step_pre_iff] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨.const Ex33K.Q₃, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩
    · simp only [ccsLTS_step, step_const_iff, ex33defn, step_pre_iff] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨.const Ex33K.P₁, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩
  · refine ⟨fun α p' hstep => ?_, fun α q' hstep => ?_⟩
    · simp only [ccsLTS_step, step_const_iff, ex33defn, step_choice_iff, step_pre_iff] at hstep
      rcases hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.const Ex33K.Q₂, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩
      · exact ⟨.const Ex33K.Q, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩
    · simp only [ccsLTS_step, step_const_iff, ex33defn, step_choice_iff, step_pre_iff] at hstep
      rcases hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.const Ex33K.P, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩
      · exact ⟨.const Ex33K.P, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩
  · refine ⟨fun α p' hstep => ?_, fun α q' hstep => ?_⟩
    · simp only [ccsLTS_step, step_const_iff, ex33defn, step_choice_iff, step_pre_iff] at hstep
      rcases hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.const Ex33K.Q, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩
      · exact ⟨.const Ex33K.Q₂, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩
    · simp only [ccsLTS_step, step_const_iff, ex33defn, step_choice_iff, step_pre_iff] at hstep
      rcases hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.const Ex33K.P, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩
      · exact ⟨.const Ex33K.P, by simp [step_const_iff, ex33defn], by simp [ex33R]⟩

end DeepWiki.Rs
