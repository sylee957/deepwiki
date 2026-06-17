import Mathlib.Data.Set.Insert
import DeepWiki.ReactiveSystems.BisimulationWeak
import DeepWiki.ReactiveSystems.SimulationWeak
import DeepWiki.ReactiveSystems.CcsWeakCongruence

/-! # The mutual-exclusion monitor `MutexTest` (soundness)
The monitor process watches the `enter`/`exit` actions of a process and
performs the distinguished reject action `bad` precisely when it sees two `enter`s
with no intervening `exit` — a mutual-exclusion violation:
`MutexTest = enter₁.MutexTest₁ + enter₂.MutexTest₂`,
`MutexTest₁ = exit₁.MutexTest + enter₂.bad.0`,
`MutexTest₂ = exit₂.MutexTest + enter₁.bad.0`.
The monitored system is `(P ∣ MutexTest) \ L` with `L = {enter₁,enter₂,exit₁,exit₂}`
(the monitor inputs `enterᵢ`/`exitᵢ` on names; `P` outputs them on co-names, and the
restriction forces them to synchronise; `bad ∉ L` survives). The monitor's correctness
is a biconditional; here we formalise the **soundness** ("if") direction — the one that
makes the monitor a sound verification tool: every well-matched run of `P` ending
in two consecutive `enter`s drives the system to a `bad`-transition. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- The monitor's channels: the observable `enterᵢ`/`exitᵢ` and the reject channel
`bad` (`bad ∉ L`, so it is observable through the restriction). -/
inductive MtChan | enter1 | exit1 | enter2 | exit2 | bad
  deriving DecidableEq

/-- The monitor's process constants. -/
inductive MtK | MutexTest | MutexTest1 | MutexTest2 | Bad0
  deriving DecidableEq

open MtChan MtK

/-- The monitor environment. `MutexTest` returns to its initial
state on a matched `enterᵢ.exitᵢ`, and reaches `bad.0` on `enterᵢ` then `enterⱼ`
(`j ≠ i`). The monitor *inputs* (names) the observed actions. -/
def mtDefn : MtK → CCS MtChan MtK
  | MutexTest => .choice (.pre (.name enter1) (.const MutexTest1))
      (.pre (.name enter2) (.const MutexTest2))
  | MutexTest1 => .choice (.pre (.name exit1) (.const MutexTest))
      (.pre (.name enter2) (.const Bad0))
  | MutexTest2 => .choice (.pre (.name exit2) (.const MutexTest))
      (.pre (.name enter1) (.const Bad0))
  | Bad0 => .pre (.name bad) .nil

/-- The restricted channel set `L = {enter₁,enter₂,exit₁,exit₂}` (as names; a
co-name is blocked through the `α.co ∉ L` side of the RES rule, while `bad` and
`τ` pass). -/
def mtRestrict : Set (Act MtChan) :=
  {Act.name enter1, Act.name enter2, Act.name exit1, Act.name exit2}

/-- `MutexTest`, monitored alongside `P` under the restriction. -/
def monitored (P : CCS MtChan MtK) (M : MtK) : CCS MtChan MtK :=
  .restrict (.par P (.const M)) mtRestrict

/-- A weak co-name move of `P` synchronises with a single name-`a` step of the
monitor component into a weak `τ`-move of the monitored system. -/
theorem sync_step {a : MtChan} {P P' : CCS MtChan MtK} {M M' : MtK}
    (h : (ccsLTS mtDefn) ⊢ P =[Act.coname a]⇒[Act.tau] P')
    (hM : Step mtDefn (.const M) (Act.name a) (.const M')) :
    tauStar (ccsLTS mtDefn) Act.tau (monitored P M) (monitored P' M') := by
  rcases h with ⟨hc, _⟩ | ⟨_, p₁, p₂, h₁, hstep, h₂⟩
  · exact absurd hc (by simp)
  · have hmid : Step mtDefn (CCS.restrict (CCS.par p₁ (.const M)) mtRestrict) Act.tau
        (CCS.restrict (CCS.par p₂ (.const M')) mtRestrict) :=
      Step.res (by simp [mtRestrict]) (by simp [mtRestrict])
        (Step.com3 (by simp [Act.IsLabel]) hstep (by simpa using hM))
    refine tauStar_trans ?_ (tauStar_trans (tauStar_single hmid) ?_)
    · exact tauStar_restrict mtDefn mtRestrict (by simp [mtRestrict])
        (tauStar_par_left mtDefn (.const M) h₁)
    · exact tauStar_restrict mtDefn mtRestrict (by simp [mtRestrict])
        (tauStar_par_left mtDefn (.const M') h₂)

/-! ### The monitor's concrete transitions -/

theorem mt_enter1 : Step mtDefn (.const MutexTest) (Act.name enter1) (.const MutexTest1) :=
  Step.con (Step.suml (Step.act _ _))

/-- `MutexTest --enter₂--> MutexTest₂`: an `enter₂` input enters the second round. -/
theorem mt_enter2 : Step mtDefn (.const MutexTest) (Act.name enter2) (.const MutexTest2) :=
  Step.con (Step.sumr (Step.act _ _))

/-- `MutexTest₁ --exit₁--> MutexTest`: a matching `exit₁` closes the first round, returning
to the initial state. -/
theorem mt1_exit1 : Step mtDefn (.const MutexTest1) (Act.name exit1) (.const MutexTest) :=
  Step.con (Step.suml (Step.act _ _))

/-- `MutexTest₁ --enter₂--> Bad0`: a second `enter` (here `enter₂`) with no intervening `exit₁`
is a mutual-exclusion violation, driving to `Bad0`. -/
theorem mt1_enter2 : Step mtDefn (.const MutexTest1) (Act.name enter2) (.const Bad0) :=
  Step.con (Step.sumr (Step.act _ _))

/-- `MutexTest₂ --exit₂--> MutexTest`: a matching `exit₂` closes the second round, returning
to the initial state. -/
theorem mt2_exit2 : Step mtDefn (.const MutexTest2) (Act.name exit2) (.const MutexTest) :=
  Step.con (Step.suml (Step.act _ _))

/-- `MutexTest₂ --enter₁--> Bad0`: a second `enter` (here `enter₁`) with no intervening `exit₂`
is a mutual-exclusion violation, driving to `Bad0`. -/
theorem mt2_enter1 : Step mtDefn (.const MutexTest2) (Act.name enter1) (.const Bad0) :=
  Step.con (Step.sumr (Step.act _ _))

/-- From `Bad0` the system performs the observable reject action `bad`. -/
theorem monitored_bad (P : CCS MtChan MtK) :
    Step mtDefn (monitored P Bad0) (Act.name bad) (.restrict (.par P .nil) mtRestrict) :=
  Step.res (by simp [mtRestrict]) (by simp [mtRestrict])
    (Step.com2 (Step.con (Step.act _ _)))

/-! ### The regular language `(enter₁ exit₁ + enter₂ exit₂)*` -/

/-- A sequence of `P`'s observable (co-name) actions in the regular language
`(enter₁ exit₁ + enter₂ exit₂)*`: matched `enterᵢ`/`exitᵢ` rounds. -/
inductive WellMatched : List (Act MtChan) → Prop
  | nil : WellMatched []
  | round1 {w} : WellMatched w →
      WellMatched (Act.coname enter1 :: Act.coname exit1 :: w)
  | round2 {w} : WellMatched w →
      WellMatched (Act.coname enter2 :: Act.coname exit2 :: w)

/-- A matched `enterᵢ.exitᵢ` round leaves the monitor back in its initial state,
observed as a sequence of `τ`-steps of the system. -/
theorem mutex_round1 {P P₁ P₂ : CCS MtChan MtK}
    (h1 : (ccsLTS mtDefn) ⊢ P =[Act.coname enter1]⇒[Act.tau] P₁)
    (h2 : (ccsLTS mtDefn) ⊢ P₁ =[Act.coname exit1]⇒[Act.tau] P₂) :
    tauStar (ccsLTS mtDefn) Act.tau (monitored P MutexTest) (monitored P₂ MutexTest) :=
  tauStar_trans (sync_step h1 mt_enter1) (sync_step h2 mt1_exit1)

/-- A matched `enter₂.exit₂` round leaves the monitor back in its initial state,
observed as a sequence of `τ`-steps of the system. -/
theorem mutex_round2 {P P₁ P₂ : CCS MtChan MtK}
    (h1 : (ccsLTS mtDefn) ⊢ P =[Act.coname enter2]⇒[Act.tau] P₁)
    (h2 : (ccsLTS mtDefn) ⊢ P₁ =[Act.coname exit2]⇒[Act.tau] P₂) :
    tauStar (ccsLTS mtDefn) Act.tau (monitored P MutexTest) (monitored P₂ MutexTest) :=
  tauStar_trans (sync_step h1 mt_enter2) (sync_step h2 mt2_exit2)

/-- A well-matched run of `P` (a `σ ∈ (enter₁ exit₁ + enter₂ exit₂)*`) leaves the
monitored system in its initial monitor state via `τ`-steps only. -/
theorem monitored_wellMatched {σ : List (Act MtChan)} (hσ : WellMatched σ) :
    ∀ {P Q : CCS MtChan MtK}, WeakPath (ccsLTS mtDefn) Act.tau P σ Q →
      tauStar (ccsLTS mtDefn) Act.tau (monitored P MutexTest) (monitored Q MutexTest) := by
  induction hσ with
  | nil =>
    intro P Q hpath
    exact tauStar_restrict mtDefn mtRestrict (by simp [mtRestrict])
      (tauStar_par_left mtDefn _ hpath)
  | round1 _ ih =>
    intro P Q hpath
    obtain ⟨_, P', hPP', _, P'', hP'P'', hpathw⟩ := hpath
    exact tauStar_trans (mutex_round1 hPP' hP'P'') (ih hpathw)
  | round2 _ ih =>
    intro P Q hpath
    obtain ⟨_, P', hPP', _, P'', hP'P'', hpathw⟩ := hpath
    exact tauStar_trans (mutex_round2 hPP' hP'P'') (ih hpathw)

/-- Soundness direction. If `P`, after a
well-matched run `σ`, can perform `enter₁` then `enter₂` (or `enter₂` then
`enter₁`), then the monitored system `(P ∣ MutexTest) \ L` can perform the reject
action `bad`. Thus the monitor detects every mutual-exclusion violation. -/
theorem monitored_bad_of_wellMatched_violation {σ : List (Act MtChan)} {P P₁ P₂ P₃ : CCS MtChan MtK}
    (hσ : WellMatched σ) (hpath : WeakPath (ccsLTS mtDefn) Act.tau P σ P₁)
    (hviol :
      ((ccsLTS mtDefn) ⊢ P₁ =[Act.coname enter1]⇒[Act.tau] P₂ ∧
        (ccsLTS mtDefn) ⊢ P₂ =[Act.coname enter2]⇒[Act.tau] P₃) ∨
      ((ccsLTS mtDefn) ⊢ P₁ =[Act.coname enter2]⇒[Act.tau] P₂ ∧
        (ccsLTS mtDefn) ⊢ P₂ =[Act.coname enter1]⇒[Act.tau] P₃)) :
    ∃ Q, (ccsLTS mtDefn) ⊢ monitored P MutexTest =[Act.name bad]⇒[Act.tau] Q := by
  have hpre := monitored_wellMatched hσ hpath
  refine ⟨.restrict (.par P₃ .nil) mtRestrict,
    Or.inr ⟨by simp, monitored P₃ Bad0, _, ?_, monitored_bad P₃, tauStar_refl _ _ _⟩⟩
  rcases hviol with ⟨he1, he2⟩ | ⟨he2, he1⟩
  · -- enter₁ then enter₂: MutexTest → MutexTest₁ → Bad0
    exact tauStar_trans hpre
      (tauStar_trans (sync_step he1 mt_enter1) (sync_step he2 mt1_enter2))
  · -- enter₂ then enter₁: MutexTest → MutexTest₂ → Bad0
    exact tauStar_trans hpre
      (tauStar_trans (sync_step he2 mt_enter2) (sync_step he1 mt2_enter1))

/-! ### Completeness core: the monitor flags `bad` only on a genuine violation -/

/-- The monitor performs only *name* actions (it inputs the observed channels); it
never does `τ` or a co-name. -/
theorem monitor_action_name {M : MtK} {α : Act MtChan} {X : CCS MtChan MtK}
    (h : Step mtDefn (.const M) α X) : ∃ a, α = Act.name a := by
  rw [step_const_iff] at h
  cases M with
  | MutexTest =>
      simp only [mtDefn] at h
      rcases step_choice_iff.mp h with h | h <;> (rw [step_pre_iff] at h; exact ⟨_, h.1⟩)
  | MutexTest1 =>
      simp only [mtDefn] at h
      rcases step_choice_iff.mp h with h | h <;> (rw [step_pre_iff] at h; exact ⟨_, h.1⟩)
  | MutexTest2 =>
      simp only [mtDefn] at h
      rcases step_choice_iff.mp h with h | h <;> (rw [step_pre_iff] at h; exact ⟨_, h.1⟩)
  | Bad0 =>
      simp only [mtDefn] at h
      rw [step_pre_iff] at h; exact ⟨_, h.1⟩

/-- A `name bad` move of the monitor comes only from its `Bad0` state. -/
theorem monitor_bad_step {M : MtK} {X : CCS MtChan MtK}
    (h : Step mtDefn (.const M) (Act.name bad) X) : M = Bad0 := by
  rw [step_const_iff] at h
  cases M with
  | MutexTest =>
      simp only [mtDefn] at h
      rcases step_choice_iff.mp h with h | h <;> (rw [step_pre_iff] at h; simp at h)
  | MutexTest1 =>
      simp only [mtDefn] at h
      rcases step_choice_iff.mp h with h | h <;> (rw [step_pre_iff] at h; simp at h)
  | MutexTest2 =>
      simp only [mtDefn] at h
      rcases step_choice_iff.mp h with h | h <;> (rw [step_pre_iff] at h; simp at h)
  | Bad0 => rfl

/-- The monitor enters `Bad0` only on a *second* `enter` on the channel opposite to
the one in progress — `MutexTest₁ —enter₂→ Bad0` or `MutexTest₂ —enter₁→ Bad0` — a
genuine mutual-exclusion violation (two `enter`s with no intervening matching `exit`). -/
theorem monitor_into_Bad0 {M : MtK} {α : Act MtChan}
    (h : Step mtDefn (.const M) α (.const Bad0)) :
    (M = MutexTest1 ∧ α = Act.name enter2) ∨ (M = MutexTest2 ∧ α = Act.name enter1) := by
  rw [step_const_iff] at h
  cases M with
  | MutexTest =>
      simp only [mtDefn] at h
      rcases step_choice_iff.mp h with h | h <;> (rw [step_pre_iff] at h; simp at h)
  | MutexTest1 =>
      simp only [mtDefn] at h
      rcases step_choice_iff.mp h with h | h
      · rw [step_pre_iff] at h; simp at h
      · rw [step_pre_iff] at h; exact Or.inl ⟨rfl, h.1⟩
  | MutexTest2 =>
      simp only [mtDefn] at h
      rcases step_choice_iff.mp h with h | h
      · rw [step_pre_iff] at h; simp at h
      · rw [step_pre_iff] at h; exact Or.inr ⟨rfl, h.1⟩
  | Bad0 =>
      simp only [mtDefn] at h
      rw [step_pre_iff] at h; simp at h

/-- A `bad`-transition of the monitored system is either `P`'s own `bad` action or
the monitor (in `Bad0`) firing — the monitor never synchronises a `bad`. -/
theorem monitored_bad_inv {P : CCS MtChan MtK} {M : MtK} {X : CCS MtChan MtK}
    (h : Step mtDefn (monitored P M) (Act.name bad) X) :
    (∃ P', Step mtDefn P (Act.name bad) P') ∨ M = Bad0 := by
  unfold monitored at h
  rw [step_restrict_iff] at h
  obtain ⟨R, _, _, hpar, rfl⟩ := h
  rw [step_par_iff] at hpar
  rcases hpar with ⟨P', hP, rfl⟩ | ⟨Q', hQ, rfl⟩ | ⟨ℓ, P', Q', hτ, _, _, _, rfl⟩
  · exact Or.inl ⟨P', hP⟩
  · exact Or.inr (monitor_bad_step hQ)
  · simp at hτ

/-- **Completeness core (no false alarms).** A process `P` that never itself performs
the reject action `bad` drives the monitored system to a `bad`-transition only when the
monitor is in its `Bad0` state — which (by `monitor_into_Bad0`) is reached only on a
genuine mutual-exclusion violation. So the monitor never raises a false alarm. -/
theorem monitored_bad_imp_Bad0 {P : CCS MtChan MtK} {M : MtK} {X : CCS MtChan MtK}
    (hP : ∀ P', ¬ Step mtDefn P (Act.name bad) P')
    (h : Step mtDefn (monitored P M) (Act.name bad) X) : M = Bad0 :=
  (monitored_bad_inv h).resolve_left (fun ⟨P', hP'⟩ => hP P' hP')

/-- Faithfulness: the bare violation `enter₁` then `enter₂` (no preceding run) is
detected — `MutexTest ⟶enter₁⟶ MutexTest₁ ⟶enter₂⟶ Bad0 ⟶bad⟶`. -/
example :
    Step mtDefn (.const MutexTest) (Act.name enter1) (.const MutexTest1) ∧
    Step mtDefn (.const MutexTest1) (Act.name enter2) (.const Bad0) ∧
    Step mtDefn (.const Bad0) (Act.name bad) .nil :=
  ⟨mt_enter1, mt1_enter2, Step.con (Step.act _ _)⟩

end DeepWiki.ReactiveSystems
