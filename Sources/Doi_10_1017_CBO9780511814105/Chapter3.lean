import DeepWiki.ReactiveSystems.Bisimulation
import DeepWiki.ReactiveSystems.BisimulationWeak
import DeepWiki.ReactiveSystems.Traces
import DeepWiki.ReactiveSystems.Simulation
import DeepWiki.ReactiveSystems.BisimulationGame
import DeepWiki.ReactiveSystems.Ccs
import DeepWiki.ReactiveSystems.CcsCongruence
import DeepWiki.ReactiveSystems.CcsWeakCongruence
import DeepWiki.ReactiveSystems.CcsBufferTwo
import DeepWiki.ReactiveSystems.CcsCounter
import DeepWiki.ReactiveSystems.CcsBufferN
import DeepWiki.ReactiveSystems.CcsTauLaws
import DeepWiki.ReactiveSystems.CcsStructuralLaws
import DeepWiki.ReactiveSystems.CcsRestrictionLaws
import DeepWiki.ReactiveSystems.StringBisimulation
import DeepWiki.ReactiveSystems.Chapter3Examples
import DeepWiki.ReactiveSystems.Chapter3WeakBisim
import DeepWiki.ReactiveSystems.Chapter3SmUniSpec
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

/-- **Exercise 3.2** (§3.2), completed traces: traces ending in a deadlocked
state. The library's `LTS.CompletedTraces` / `LTS.CompletedTraceEquiv`. -/
abbrev ex_3_2 := @LTS.CompletedTraces

/-- **Exercise 3.2** (§3.2). Strong bisimilarity implies completed-trace
equivalence (a finer equivalence than ordinary trace equivalence). -/
theorem ex_3_2_bisimilar (L : LTS Proc Act) {p q : Proc} (h : p ~[L] q) :
    LTS.CompletedTraceEquiv L p q := h.completedTraceEquiv

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

/-- **Exercise 3.27** (§3.4). Mutually `τ`-reachable states are weakly bisimilar:
`p ⇒ q` and `q ⇒ p` imply `p ≈ q`. -/
theorem ex_3_27 (L : LTS Proc Act) (tau : Act) {p q : Proc}
    (hpq : LTS.tauStar L tau p q) (hqp : LTS.tauStar L tau q p) : p ≈[L, tau] q :=
  LTS.weaklyBisimilar_of_tauStar hpq hqp

/-! ## §3.5 The bisimulation game (Definitions 3.5–3.6, Propositions 3.3–3.4) -/

/-- **Definition 3.5** (§3.5, p.65). A defender winning strategy in the strong
bisimulation game: an invariant set of configurations in which every attacker
challenge can be answered. The library's `LTS.DefenderStrategy`. -/
abbrev def_3_5 := @LTS.DefenderStrategy

/-- **Definition 3.6** (§3.5). A defender winning strategy in the weak
bisimulation game (answers by weak transitions). The library's
`LTS.DefenderStrategyWeak`. -/
abbrev def_3_6 := @LTS.DefenderStrategyWeak

/-- **Proposition 3.3 / Exercise 3.38** (§3.5, p.66). The defender has a winning
strategy in the strong bisimulation game from `(p, q)` iff `p ~ q` (and, by
determinacy, the attacker has one iff `p ≁ q`). -/
theorem prop_3_3 (L : LTS Proc Act) (p q : Proc) :
    LTS.DefenderWins L p q ↔ (p ~[L] q) := LTS.defenderWins_iff_bisimilar L p q

/-- **Proposition 3.4** (§3.5). The defender has a winning strategy in the weak
bisimulation game from `(p, q)` iff `p ≈ q`. -/
theorem prop_3_4 (L : LTS Proc Act) (tau : Act) (p q : Proc) :
    LTS.DefenderWinsWeak L tau p q ↔ (p ≈[L, tau] q) :=
  LTS.defenderWinsWeak_iff_weaklyBisimilar L tau p q

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

/-- **Proposition 3.1** (§3.3, p.50). The relating relation of the unbounded
counter (the book's `R`, pairing `C ∣ Πᵢ Pᵢ` with `Counterₙ` when exactly `n` of
the `Pᵢ` are `down.0`) is a strong bisimulation. Discharged by the library's
`isBisimulation_counterRel`. -/
theorem prop_3_1 :
    DeepWiki.ReactiveSystems.LTS.IsBisimulation (ccsLTS DeepWiki.ReactiveSystems.ctrDefn)
      DeepWiki.ReactiveSystems.counterRel :=
  DeepWiki.ReactiveSystems.isBisimulation_counterRel

/-- **Proposition 3.1 / §3.3** (p.49). The headline consequence: the unbounded
counter `C = up.(C ∣ down.0)` is strongly bisimilar to its specification
`Counter₀`. Discharged by the library's `counter_bisim`. -/
theorem prop_3_1_bisim :
    (CCS.const DeepWiki.ReactiveSystems.CtrK.impl) ~[ccsLTS DeepWiki.ReactiveSystems.ctrDefn]
      (CCS.const (DeepWiki.ReactiveSystems.CtrK.counter 0)) :=
  DeepWiki.ReactiveSystems.counter_bisim

/-- **Figure 3.2 / Proposition 3.2** (§3.3, p.51), the `n = 2` case. A two-place
buffer is strongly bisimilar to two one-place buffers in parallel:
`B²₀ ~ B¹₀ ∣ B¹₀`. (The general `n`-buffer statement `Bⁿ₀ ~ (B¹₀)ⁿ` is a
parallel-bag bisimulation over `n` components.) Discharged by the library's
`buffer_two`. -/
theorem prop_3_2_two :
    (CCS.const DeepWiki.ReactiveSystems.BufK.Two0) ~[ccsLTS DeepWiki.ReactiveSystems.bufDefn]
      (CCS.par (CCS.const DeepWiki.ReactiveSystems.BufK.One0)
        (CCS.const DeepWiki.ReactiveSystems.BufK.One0)) :=
  DeepWiki.ReactiveSystems.buffer_two

/-- **Proposition 3.2** (§3.3, p.51). For every `n`, a capacity-`n` buffer is
strongly bisimilar to `n` one-place buffers composed in parallel:
`Bⁿ₀ ~ B¹₀ ∣ ⋯ ∣ B¹₀` (`n` copies, written as the bag over `replicate n false`).
Discharged by the library's `bufN_bisim`. -/
theorem prop_3_2 (n : ℕ) :
    (CCS.const (DeepWiki.ReactiveSystems.BufNK.nbuf n 0)) ~[ccsLTS
      DeepWiki.ReactiveSystems.bufNDefn]
      (DeepWiki.ReactiveSystems.bufBag (List.replicate n false)) :=
  DeepWiki.ReactiveSystems.bufN_bisim n

/-! ## Exercise 3.26: Milner's τ-laws

(The CCS action type is written `RsAct` below — a local alias for
`DeepWiki.ReactiveSystems.Act` — because the chapter's section variable `Act`
shadows the inductive.) -/

/-- Local alias for the CCS action type, since the section variable `Act` shadows
the inductive `DeepWiki.ReactiveSystems.Act`. -/
abbrev RsAct := @DeepWiki.ReactiveSystems.Act

/-- **Exercise 3.26** (3.9, §3.4, p.61). `α.τ.P ≈ α.P`: a silent step guarded by
an action is unobservable. -/
theorem ex_3_26_1 {Name K : Type*} (defn : K → CCS Name K) {α : RsAct Name} (P : CCS Name K) :
    CCS.pre α (CCS.pre DeepWiki.ReactiveSystems.Act.tau P) ≈[ccsLTS defn,
      DeepWiki.ReactiveSystems.Act.tau] CCS.pre α P :=
  tau_law_1 defn P

/-- **Exercise 3.26** (3.10, §3.4, p.61). `P + τ.P ≈ τ.P`. -/
theorem ex_3_26_2 {Name K : Type*} (defn : K → CCS Name K) (P : CCS Name K) :
    CCS.choice P (CCS.pre DeepWiki.ReactiveSystems.Act.tau P) ≈[ccsLTS defn,
      DeepWiki.ReactiveSystems.Act.tau] CCS.pre DeepWiki.ReactiveSystems.Act.tau P :=
  tau_law_2 defn P

/-- **Exercise 3.26** (3.11, §3.4, p.61). `α.(P + τ.Q) ≈ α.(P + τ.Q) + α.Q`. -/
theorem ex_3_26_3 {Name K : Type*} (defn : K → CCS Name K) {α : RsAct Name} (P Q : CCS Name K) :
    CCS.pre α (CCS.choice P (CCS.pre DeepWiki.ReactiveSystems.Act.tau Q)) ≈[ccsLTS defn,
      DeepWiki.ReactiveSystems.Act.tau]
      CCS.choice (CCS.pre α (CCS.choice P (CCS.pre DeepWiki.ReactiveSystems.Act.tau Q)))
        (CCS.pre α Q) :=
  tau_law_3 defn P Q

/-! ## §3.4 Weak bisimilarity is a congruence (Theorem 3.4)

Observational equivalence `≈` is preserved by prefixing, parallel composition,
relabelling and restriction (but *not* by choice — `0 ≈ τ.0` yet
`a.0 + 0 ≉ a.0 + τ.0`). Discharged by the library's `weak_cong_*`. -/

/-- **Theorem 3.4** (§3.4, p.62), prefix congruence: `P ≈ Q → α.P ≈ α.Q`. -/
theorem thm_3_4_pre {Name K : Type*} (defn : K → CCS Name K) {a : RsAct Name}
    {P Q : CCS Name K} (h : P ≈[ccsLTS defn, DeepWiki.ReactiveSystems.Act.tau] Q) :
    CCS.pre a P ≈[ccsLTS defn, DeepWiki.ReactiveSystems.Act.tau] CCS.pre a Q :=
  DeepWiki.ReactiveSystems.weak_cong_pre defn h

/-- **Theorem 3.4** (§3.4, p.62), parallel congruence on the left: `P ≈ Q →
P∣R ≈ Q∣R` (the hard case — a weak visible move synchronises with a single
complementary step into a weak `τ`-move). -/
theorem thm_3_4_par_left {Name K : Type*} (defn : K → CCS Name K) {P Q : CCS Name K}
    (R : CCS Name K) (h : P ≈[ccsLTS defn, DeepWiki.ReactiveSystems.Act.tau] Q) :
    CCS.par P R ≈[ccsLTS defn, DeepWiki.ReactiveSystems.Act.tau] CCS.par Q R :=
  DeepWiki.ReactiveSystems.weak_cong_par_left defn R h

/-- **Theorem 3.4** (§3.4, p.62), parallel congruence on the right: `P ≈ Q →
R∣P ≈ R∣Q`. -/
theorem thm_3_4_par_right {Name K : Type*} (defn : K → CCS Name K) {P Q : CCS Name K}
    (R : CCS Name K) (h : P ≈[ccsLTS defn, DeepWiki.ReactiveSystems.Act.tau] Q) :
    CCS.par R P ≈[ccsLTS defn, DeepWiki.ReactiveSystems.Act.tau] CCS.par R Q :=
  DeepWiki.ReactiveSystems.weak_cong_par_right defn R h

/-- **Theorem 3.4** (§3.4, p.62), relabelling congruence: `P ≈ Q → P[f] ≈ Q[f]`
for a genuine relabelling `f` (which fixes `τ`). -/
theorem thm_3_4_relabel {Name K : Type*} (defn : K → CCS Name K) {P Q : CCS Name K}
    (f : RsAct Name → RsAct Name) (hf : IsRelabelling f)
    (h : P ≈[ccsLTS defn, DeepWiki.ReactiveSystems.Act.tau] Q) :
    CCS.relabel P f ≈[ccsLTS defn, DeepWiki.ReactiveSystems.Act.tau] CCS.relabel Q f :=
  DeepWiki.ReactiveSystems.weak_cong_relabel defn f hf h

/-- **Theorem 3.4** (§3.4, p.62), restriction congruence: `P ≈ Q → P∖L ≈ Q∖L`
when `τ` is not restricted. -/
theorem thm_3_4_restrict {Name K : Type*} (defn : K → CCS Name K) {P Q : CCS Name K}
    (Lr : Set (RsAct Name)) (htau : DeepWiki.ReactiveSystems.Act.tau ∉ Lr)
    (h : P ≈[ccsLTS defn, DeepWiki.ReactiveSystems.Act.tau] Q) :
    CCS.restrict P Lr ≈[ccsLTS defn, DeepWiki.ReactiveSystems.Act.tau] CCS.restrict Q Lr :=
  DeepWiki.ReactiveSystems.weak_cong_restrict defn Lr htau h

/-! ## §3.3 Structural laws of CCS up to `~` (Exercises 3.10, 3.12) -/

/-- **Exercise 3.10** (§3.3, p.45). A constant is strongly bisimilar to its
defining body: if `K ≝ P` then `K ~ P`. The library's `const_bisim_body`. -/
theorem ex_3_10 {Name K : Type*} (defn : K → CCS Name K) (K0 : K) :
    (CCS.const K0) ~[ccsLTS defn] (defn K0) :=
  DeepWiki.ReactiveSystems.const_bisim_body K0

/-- **Exercise 3.12** (§3.3, p.46, eq. 3.4). Parallel composition is commutative:
`P ∣ Q ~ Q ∣ P`. The library's `par_comm`. -/
theorem ex_3_12_comm {Name K : Type*} (defn : K → CCS Name K) (P Q : CCS Name K) :
    (CCS.par P Q) ~[ccsLTS defn] (CCS.par Q P) :=
  DeepWiki.ReactiveSystems.par_comm P Q

/-- **Exercise 3.12** (§3.3, p.46, eq. 3.5). `0` is a unit for parallel
composition: `P ∣ 0 ~ P`. The library's `par_unit`. -/
theorem ex_3_12_unit {Name K : Type*} (defn : K → CCS Name K) (P : CCS Name K) :
    (CCS.par P CCS.nil) ~[ccsLTS defn] P :=
  DeepWiki.ReactiveSystems.par_unit P

/-- **Exercise 3.12** (§3.3, p.46, eq. 3.6). Parallel composition is associative:
`(P ∣ Q) ∣ R ~ P ∣ (Q ∣ R)`. The library's `par_assoc`. -/
theorem ex_3_12_assoc {Name K : Type*} (defn : K → CCS Name K) (P Q R : CCS Name K) :
    (CCS.par (CCS.par P Q) R) ~[ccsLTS defn] (CCS.par P (CCS.par Q R)) :=
  DeepWiki.ReactiveSystems.par_assoc P Q R

/-- **Exercise 3.12** (§3.3, p.46). A witness that `+` distributes over `∣` in a
degenerate case: `(0 + 0) ∣ 0 ~ (0 ∣ 0) + (0 ∣ 0)` (both deadlocked). The
library's `par_choice_distrib_nil`. -/
theorem ex_3_12_distrib {Name : Type*} :
    (CCS.par (CCS.choice CCS.nil CCS.nil) CCS.nil)
      ~[ccsLTS (DeepWiki.ReactiveSystems.noDefs (Name := Name))]
      (CCS.choice (CCS.par CCS.nil CCS.nil) (CCS.par CCS.nil CCS.nil)) :=
  DeepWiki.ReactiveSystems.par_choice_distrib_nil

/-- **Exercise 3.13** (§3.3, p.46). Restriction does **not** distribute over
parallel composition — `(a.0 ∣ ā.0) ∖ {a}` synchronises (`τ`) but
`(a.0 ∖ {a}) ∣ (ā.0 ∖ {a})` is deadlocked. The `¬∀` form, discharged by the
library's `not_restrict_distrib_par`. (Relabelling, being a homomorphism on
labels, *does* distribute.) -/
theorem ex_3_13 :
    ¬ ∀ (P Q : CCS DeepWiki.ReactiveSystems.RChan Empty),
      (CCS.restrict (CCS.par P Q) DeepWiki.ReactiveSystems.rcRestrict)
        ~[ccsLTS DeepWiki.ReactiveSystems.noDefs]
        (CCS.par (CCS.restrict P DeepWiki.ReactiveSystems.rcRestrict)
          (CCS.restrict Q DeepWiki.ReactiveSystems.rcRestrict)) :=
  DeepWiki.ReactiveSystems.not_restrict_distrib_par

/-- **Exercise 3.29** (§3.4, p.61). Restricting away every observable action makes
a process observationally equivalent to `0`: `P ∖ (Act ∖ {τ}) ≈ 0`. The library's
`restrict_observable_weaklyBisimilar_nil`. -/
theorem ex_3_29_weak {Name K : Type*} (defn : K → CCS Name K) (P : CCS Name K) :
    (CCS.restrict P (DeepWiki.ReactiveSystems.observable Name))
      ≈[ccsLTS defn, DeepWiki.ReactiveSystems.Act.tau] CCS.nil :=
  DeepWiki.ReactiveSystems.restrict_observable_weaklyBisimilar_nil defn P

/-- **Exercise 3.29** (§3.4, p.61). The same fails up to *strong* bisimilarity:
`(τ.0) ∖ (Act ∖ {τ}) ≁ 0` (a surviving `τ`-step). The library's
`not_restrict_observable_bisimilar_nil`. -/
theorem ex_3_29_not_strong {Name : Type*} :
    ¬ (CCS.restrict (CCS.pre DeepWiki.ReactiveSystems.Act.tau CCS.nil)
        (DeepWiki.ReactiveSystems.observable Name))
      ~[ccsLTS DeepWiki.ReactiveSystems.noDefs] CCS.nil :=
  DeepWiki.ReactiveSystems.not_restrict_observable_bisimilar_nil

/-- **Exercise 3.9** (§3.3, p.45). String bisimilarity (matching whole action
sequences) coincides with strong bisimilarity. The library's
`LTS.stringBisimilar_iff_bisimilar`. -/
theorem ex_3_9 {Proc Act : Type*} (L : LTS Proc Act) (p q : Proc) :
    LTS.StringBisimilar L p q ↔ LTS.Bisimilar L p q :=
  LTS.stringBisimilar_iff_bisimilar p q

/-- **Exercise 3.31** (§3.4, p.61). Weak string bisimilarity (matching observable
sequences via `⇒`) coincides with weak bisimilarity `≈`. The library's
`LTS.weaklyStringBisimilar_iff_weaklyBisimilar`. -/
theorem ex_3_31 {Proc Act : Type*} (L : LTS Proc Act) (tau : Act) (p q : Proc) :
    LTS.WeaklyStringBisimilar L tau p q ↔ LTS.WeaklyBisimilar L tau p q :=
  LTS.weaklyStringBisimilar_iff_weaklyBisimilar p q

/-- **Exercise 3.5** (§3.3, p.42). The states `s, t` of the given two LTSs are
strongly bisimilar, `s ~ t`, witnessed by the explicit relation `R35`. The
library's `ex_3_5_bisim`. -/
theorem ex_3_5 :
    (DeepWiki.ReactiveSystems.S35.s) ~[DeepWiki.ReactiveSystems.lts35]
      (DeepWiki.ReactiveSystems.S35.t) :=
  DeepWiki.ReactiveSystems.ex_3_5_bisim

/-- **Exercise 3.8** (§3.3, p.44). A strong bisimulation need not be reflexive,
symmetric, or transitive — three counterexamples (over transition-free LTSs). The
library's `ex_3_8_not_reflexive`/`_not_symmetric`/`_not_transitive`. -/
theorem ex_3_8 :
    (∃ R : Bool → Bool → Prop,
      LTS.IsBisimulation (DeepWiki.ReactiveSystems.emptyLTS Bool Unit) R ∧ ¬ (∀ x, R x x)) ∧
    (∃ R : Bool → Bool → Prop,
      LTS.IsBisimulation (DeepWiki.ReactiveSystems.emptyLTS Bool Unit) R ∧
        ¬ (∀ x y, R x y → R y x)) ∧
    (∃ R : Fin 3 → Fin 3 → Prop,
      LTS.IsBisimulation (DeepWiki.ReactiveSystems.emptyLTS (Fin 3) Unit) R ∧
        ¬ (∀ x y z, R x y → R y z → R x z)) :=
  ⟨DeepWiki.ReactiveSystems.ex_3_8_not_reflexive,
   DeepWiki.ReactiveSystems.ex_3_8_not_symmetric,
   DeepWiki.ReactiveSystems.ex_3_8_not_transitive⟩

/-- **Exercise 3.37** (§3.4, p.69). For the four LTSs: `s ≁ t`, `s ~ u`, `s ≁ v`.
The positive case `s ~ u` has an explicit bisimulation; the negatives are refuted
by a two-move attacker strategy (reach a `{a,b}`-enabling state the defender
cannot match). The library's `ex_3_37_s_bisim_u`/`_s_not_bisim_t`/`_s_not_bisim_v`. -/
theorem ex_3_37 :
    ¬ ((DeepWiki.ReactiveSystems.S37.s) ~[DeepWiki.ReactiveSystems.lts37]
        (DeepWiki.ReactiveSystems.S37.t)) ∧
    ((DeepWiki.ReactiveSystems.S37.s) ~[DeepWiki.ReactiveSystems.lts37]
        (DeepWiki.ReactiveSystems.S37.u)) ∧
    ¬ ((DeepWiki.ReactiveSystems.S37.s) ~[DeepWiki.ReactiveSystems.lts37]
        (DeepWiki.ReactiveSystems.S37.v)) :=
  ⟨DeepWiki.ReactiveSystems.ex_3_37_s_not_bisim_t,
   DeepWiki.ReactiveSystems.ex_3_37_s_bisim_u,
   DeepWiki.ReactiveSystems.ex_3_37_s_not_bisim_v⟩

/-- **Exercise 3.20** (§3.4, p.58), the headline claim `a.0 ≈ a.τ.0`: a leading
silent step is unobservable (an instance of τ-law (3.9), `tau_law_1`, symmetrised).
The companion SmUni ≈ Spec / Start ≉ Spec claims rest on the Figure 3.3 model. -/
theorem ex_3_20 {Name K : Type*} (defn : K → CCS Name K) (a₀ : Name) :
    CCS.pre (DeepWiki.ReactiveSystems.Act.name a₀) CCS.nil ≈[ccsLTS defn,
        DeepWiki.ReactiveSystems.Act.tau]
      CCS.pre (DeepWiki.ReactiveSystems.Act.name a₀) (CCS.pre DeepWiki.ReactiveSystems.Act.tau CCS.nil) :=
  (DeepWiki.ReactiveSystems.tau_law_1 defn CCS.nil).symm

/-- **Exercise 3.20** (§3.4, p.58), the `SmUni ≈ Spec` claim: the Small University
`(CM ∣ CS) ∖ {coin, coffee}` is observationally equivalent to `Spec ≝ pub.Spec`
(its two internal handshakes are unobservable). The library's `ex_3_20_smuni`. -/
theorem ex_3_20_smuni :
    DeepWiki.ReactiveSystems.smUni ≈[ccsLTS DeepWiki.ReactiveSystems.smuniDefn,
      DeepWiki.ReactiveSystems.Act.tau] DeepWiki.ReactiveSystems.smSpec :=
  DeepWiki.ReactiveSystems.ex_3_20_smuni

/-- **Exercise 3.25** (§3.4, p.60). `s ≈ t`, witnessed by the weak bisimulation
`{(s,t),(s₁,t),(s₂,t),(s₃,t₂),(s₄,t₃),(s₅,t₁)}`. The library's `ex_3_25`. -/
theorem ex_3_25 :
    DeepWiki.ReactiveSystems.St325.s ≈[DeepWiki.ReactiveSystems.lts325,
      DeepWiki.ReactiveSystems.A325.tau] DeepWiki.ReactiveSystems.St325.t :=
  DeepWiki.ReactiveSystems.ex_3_25

end DeepWiki.Rs
