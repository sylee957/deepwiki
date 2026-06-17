import DeepWiki.ReactiveSystems.Chapter2Examples
import DeepWiki.ReactiveSystems.BisimulationWeak
import Mathlib.Data.Set.Insert

/-! # Exercise 3.20 — `Start ≉ Spec`
With a *faulty* coffee machine `CMb ≝ coin.coffeē.CMb + coin.CMb` (it may pocket the
coin without delivering coffee), the process `Start = (CMb ∣ CS) ∖ {coin, coffee}`
can, after publishing once, silently reach the **deadlocked** state
`Bad = (CMb ∣ CS₂) ∖ {coin, coffee}` (machine awaiting a coin, student awaiting
coffee). `Spec ≝ pub̄.Spec` never deadlocks, so `Start ≉ Spec`: a silent move to a
state that refuses `pub̄` cannot be matched by `Spec`. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- Constants of the faulty-machine model: bad machine `CMb`, student `CS`/`CS₁`/`CS₂`,
and the specification `BSpec ≝ pub̄.BSpec`. -/
inductive BadK | CMb | CS | CS1 | CS2 | BSpec
  deriving DecidableEq

/-- `CMb ≝ coin.c̄offee.CMb + coin.CMb` (faulty); `CS ≝ p̄ub.CS₁`, `CS₁ ≝ c̄oin.CS₂`,
`CS₂ ≝ coffee.CS`; `BSpec ≝ p̄ub.BSpec`. -/
def badDefn : BadK → CCS SmuniName BadK
  | .CMb => .choice (.pre (.name .coin) (.pre (.coname .coffee) (.const .CMb)))
      (.pre (.name .coin) (.const .CMb))
  | .CS => .pre (.coname .pub) (.const .CS1)
  | .CS1 => .pre (.coname .coin) (.const .CS2)
  | .CS2 => .pre (.name .coffee) (.const .CS)
  | .BSpec => .pre (.coname .pub) (.const .BSpec)

/-- `Start = (CMb ∣ CS) ∖ {coin, coffee}`. -/
abbrev badStart : CCS SmuniName BadK :=
  .restrict (.par (.const .CMb) (.const .CS)) smuniRestrict
/-- `M = (CMb ∣ CS₁) ∖ L`, reached after the first `pub̄`. -/
abbrev badM : CCS SmuniName BadK :=
  .restrict (.par (.const .CMb) (.const .CS1)) smuniRestrict
/-- `Bad = (CMb ∣ CS₂) ∖ L`, the deadlock (machine kept the coin, student waits). -/
abbrev badBad : CCS SmuniName BadK :=
  .restrict (.par (.const .CMb) (.const .CS2)) smuniRestrict
/-- `BSpec ≝ pub̄.BSpec`. -/
abbrev badSpec : CCS SmuniName BadK := .const .BSpec

/-! ## The transitions we need, and the deadlock / determinism facts -/

/-- `Start —pub̄→ M`. -/
theorem badStart_pub : (ccsLTS badDefn).step badStart (Act.coname SmuniName.pub) badM :=
  Step.res (by simp [smuniRestrict]) (by simp [smuniRestrict]) (Step.com2 (Step.con (Step.act _ _)))

/-- `M —τ→ Bad`: the machine takes the coin via its faulty branch and keeps it. -/
theorem badM_tau : (ccsLTS badDefn).step badM Act.tau badBad :=
  Step.res (by simp [smuniRestrict]) (by simp [smuniRestrict])
    (Step.com3 (by rintro ⟨⟩) (Step.con (Step.sumr (Step.act _ _))) (Step.con (Step.act _ _)))

/-- `BSpec`'s only transition: `pub̄` back to itself. -/
theorem badSpec_step_iff {α : Act SmuniName} {P' : CCS SmuniName BadK} :
    (ccsLTS badDefn).step badSpec α P' ↔ (α = Act.coname SmuniName.pub ∧ P' = badSpec) := by
  rw [ccsLTS_step, step_const_iff]
  simp only [badDefn, step_pre_iff]

/-- `BSpec` cannot perform `τ`. -/
theorem badSpec_no_tau {P' : CCS SmuniName BadK} : ¬ (ccsLTS badDefn).step badSpec Act.tau P' :=
  fun h => absurd (badSpec_step_iff.mp h).1 (by decide)

/-- `BSpec ⟶τ* q` forces `q = BSpec` (`BSpec` is `τ`-free). -/
theorem tauStar_badSpec {q : CCS SmuniName BadK}
    (h : tauStar (ccsLTS badDefn) Act.tau badSpec q) : q = badSpec := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨_, hZ, _⟩
  · exact heq.symm
  · exact absurd hZ badSpec_no_tau

/-- `BSpec =pub̄⇒ q` forces `q = BSpec` (`BSpec` is deterministic and `τ`-free). -/
theorem badSpec_weak_pub {q : CCS SmuniName BadK}
    (h : (ccsLTS badDefn) ⊢ badSpec =[Act.coname SmuniName.pub]⇒[Act.tau] q) : q = badSpec := by
  rcases h with ⟨hα, _⟩ | ⟨_, p1, p2, h1, hstep, h2⟩
  · exact absurd hα (by decide)
  · obtain rfl := tauStar_badSpec h1
    obtain ⟨_, rfl⟩ := badSpec_step_iff.mp hstep
    exact tauStar_badSpec h2

/-- `BSpec =τ⇒ q` forces `q = BSpec`. -/
theorem badSpec_weak_tau {q : CCS SmuniName BadK}
    (h : (ccsLTS badDefn) ⊢ badSpec =[Act.tau]⇒[Act.tau] q) : q = badSpec := by
  rcases h with ⟨_, h1⟩ | ⟨hα, _⟩
  · exact tauStar_badSpec h1
  · exact absurd rfl hα

/-- `Bad` is deadlocked: it affords no transition (the `coin`/`coffee` handshake
cannot complete, and the individual actions are restricted). -/
theorem badBad_no_step {α : Act SmuniName} {P' : CCS SmuniName BadK} :
    ¬ (ccsLTS badDefn).step badBad α P' := by
  intro h
  rw [ccsLTS_step, step_restrict_iff] at h
  obtain ⟨P, hαL, hαcoL, hpar, rfl⟩ := h
  rw [step_par_iff] at hpar
  rcases hpar with ⟨CM', hCM, rfl⟩ | ⟨CS', hCS, rfl⟩ | ⟨ℓ, A', B', rfl, _, hA, hB, rfl⟩
  · rw [step_const_iff] at hCM; simp only [badDefn] at hCM; rw [step_choice_iff] at hCM
    rcases hCM with h1 | h2
    · rw [step_pre_iff] at h1; obtain ⟨rfl, _⟩ := h1
      exact absurd (show Act.name SmuniName.coin ∈ smuniRestrict by simp [smuniRestrict]) hαL
    · rw [step_pre_iff] at h2; obtain ⟨rfl, _⟩ := h2
      exact absurd (show Act.name SmuniName.coin ∈ smuniRestrict by simp [smuniRestrict]) hαL
  · rw [step_const_iff] at hCS; simp only [badDefn, step_pre_iff] at hCS
    obtain ⟨rfl, _⟩ := hCS
    exact absurd (show Act.name SmuniName.coffee ∈ smuniRestrict by simp [smuniRestrict]) hαL
  · rw [step_const_iff] at hA; simp only [badDefn] at hA; rw [step_choice_iff] at hA
    rw [step_const_iff] at hB; simp only [badDefn, step_pre_iff] at hB
    have hℓ : ℓ = Act.name SmuniName.coin := by
      rcases hA with h1 | h2
      · exact (step_pre_iff.mp h1).1
      · exact (step_pre_iff.mp h2).1
    rw [hℓ] at hB
    exact absurd hB.1 (by decide)

/-- `Bad ⟶τ* q` forces `q = Bad` (`Bad` is deadlocked). -/
theorem tauStar_badBad {q : CCS SmuniName BadK}
    (h : tauStar (ccsLTS badDefn) Act.tau badBad q) : q = badBad := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨_, hZ, _⟩
  · exact heq.symm
  · exact absurd hZ badBad_no_step

/-- `Bad` affords no weak `pub̄`: it deadlocks. -/
theorem badBad_no_weak_pub :
    ¬ ∃ q, (ccsLTS badDefn) ⊢ badBad =[Act.coname SmuniName.pub]⇒[Act.tau] q := by
  rintro ⟨q, ⟨hα, _⟩ | ⟨_, p1, p2, h1, hstep, _⟩⟩
  · exact absurd hα (by decide)
  · obtain rfl := tauStar_badBad h1
    exact badBad_no_step hstep

/-- **Exercise 3.20** (§3.4, p.58). `Start ≉ Spec`: `Start` can publish and then
silently reach the deadlocked `Bad`, which (unlike `Spec`) refuses `pub̄`, so no weak
bisimulation relates `Start` and `Spec`. -/
theorem badStart_not_weakBisim_badSpec : ¬ (badStart ≈[ccsLTS badDefn, Act.tau] badSpec) := by
  intro h
  -- Start —pub̄→ M is matched by BSpec =pub̄⇒ BSpec, giving M ≈ BSpec.
  obtain ⟨q1, hq1, hM⟩ :=
    (isWeakBisimulation_weaklyBisimilar h).1 (Act.coname SmuniName.pub) badM badStart_pub
  obtain rfl := badSpec_weak_pub hq1
  -- M —τ→ Bad is matched by BSpec =τ⇒ BSpec, giving Bad ≈ BSpec.
  obtain ⟨q2, hq2, hBad⟩ := (isWeakBisimulation_weaklyBisimilar hM).1 Act.tau badBad badM_tau
  obtain rfl := badSpec_weak_tau hq2
  -- BSpec —pub̄→ BSpec must be matched by Bad =pub̄⇒ …, but Bad deadlocks.
  obtain ⟨q3, hq3, _⟩ :=
    (isWeakBisimulation_weaklyBisimilar hBad).2 (Act.coname SmuniName.pub) badSpec
      (badSpec_step_iff.mpr ⟨rfl, rfl⟩)
  exact badBad_no_weak_pub ⟨q3, hq3⟩

end DeepWiki.ReactiveSystems
