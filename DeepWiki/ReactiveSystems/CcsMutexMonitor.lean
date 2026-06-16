import Mathlib.Data.Set.Insert
import DeepWiki.ReactiveSystems.BisimulationWeak
import DeepWiki.ReactiveSystems.SimulationWeak
import DeepWiki.ReactiveSystems.CcsWeakCongruence

/-! # The mutual-exclusion monitor `MutexTest` (Proposition 7.2, soundness)
The monitor process of §7.3 watches the `enter`/`exit` actions of a process and
performs the distinguished reject action `bad` precisely when it sees two `enter`s
with no intervening `exit` — a mutual-exclusion violation:
`MutexTest = enter₁.MutexTest₁ + enter₂.MutexTest₂`,
`MutexTest₁ = exit₁.MutexTest + enter₂.bad.0`,
`MutexTest₂ = exit₂.MutexTest + enter₁.bad.0`.
The monitored system is `(P ∣ MutexTest) \ L` with `L = {enter₁,enter₂,exit₁,exit₂}`
(the monitor inputs `enterᵢ`/`exitᵢ` on names; `P` outputs them on co-names, and the
restriction forces them to synchronise; `bad ∉ L` survives). Proposition 7.2 is a
biconditional; here we formalise the **soundness** ("if") direction — the one that
makes the monitor a sound verification tool: every well-matched run of `P` ending
in two consecutive `enter`s drives the system to a `bad`-transition. The
completeness direction is the book's Exercise 7.12. -/

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

/-- The monitor environment (§7.3, p.153). `MutexTest` returns to its initial
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

theorem mt_enter2 : Step mtDefn (.const MutexTest) (Act.name enter2) (.const MutexTest2) :=
  Step.con (Step.sumr (Step.act _ _))

theorem mt1_exit1 : Step mtDefn (.const MutexTest1) (Act.name exit1) (.const MutexTest) :=
  Step.con (Step.suml (Step.act _ _))

theorem mt1_enter2 : Step mtDefn (.const MutexTest1) (Act.name enter2) (.const Bad0) :=
  Step.con (Step.sumr (Step.act _ _))

theorem mt2_exit2 : Step mtDefn (.const MutexTest2) (Act.name exit2) (.const MutexTest) :=
  Step.con (Step.suml (Step.act _ _))

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

/-- **Proposition 7.2** (§7.3, p.153), soundness direction. If `P`, after a
well-matched run `σ`, can perform `enter₁` then `enter₂` (or `enter₂` then
`enter₁`), then the monitored system `(P ∣ MutexTest) \ L` can perform the reject
action `bad`. Thus the monitor detects every mutual-exclusion violation. -/
theorem prop_7_2_if {σ : List (Act MtChan)} {P P₁ P₂ P₃ : CCS MtChan MtK}
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

/-- Faithfulness: the bare violation `enter₁` then `enter₂` (no preceding run) is
detected — `MutexTest ⟶enter₁⟶ MutexTest₁ ⟶enter₂⟶ Bad0 ⟶bad⟶`. -/
example :
    Step mtDefn (.const MutexTest) (Act.name enter1) (.const MutexTest1) ∧
    Step mtDefn (.const MutexTest1) (Act.name enter2) (.const Bad0) ∧
    Step mtDefn (.const Bad0) (Act.name bad) .nil :=
  ⟨mt_enter1, mt1_enter2, Step.con (Step.act _ _)⟩

end DeepWiki.ReactiveSystems
