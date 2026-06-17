import DeepWiki.ReactiveSystems.Chapter2Examples
import DeepWiki.ReactiveSystems.BisimulationWeak
import Mathlib.Data.Set.Insert

/-! # Exercise 3.20 — `SmUni ≈ Spec`
The Small University `SmUni = (CM ∣ CS) ∖ {coin, coffee}` is observationally
equivalent to `Spec ≝ pub.Spec`. Restriction blocks the `coin`/`coffee`
handshakes, so each of the three reachable states has exactly one transition:
`SmUni —pub→ (CM∣CS₁)∖L —τ→ (CM₁∣CS₂)∖L —τ→ SmUni`. Hiding the two silent steps,
`SmUni` just publishes repeatedly, like `Spec`; the relation
`{(SmUni, Spec), ((CM∣CS₁)∖L, Spec), ((CM₁∣CS₂)∖L, Spec)}` is a weak bisimulation. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- `(CM ∣ CS₁) ∖ L`, reached after the first `pub`. -/
abbrev smB : CCS SmuniName SmuniK :=
  .restrict (.par (.const .CM) (.const .CS1)) smuniRestrict
/-- `(CM₁ ∣ CS₂) ∖ L`, reached after the `coin` handshake. -/
abbrev smC : CCS SmuniName SmuniK :=
  .restrict (.par (.const .CM1) (.const .CS2)) smuniRestrict
/-- `Spec ≝ pub.Spec`. -/
abbrev smSpec : CCS SmuniName SmuniK := .const .Spec

/-! ## Each reachable state has exactly one transition -/

theorem smUni_step_iff {α : Act SmuniName} {P' : CCS SmuniName SmuniK} :
    (ccsLTS smuniDefn).step smUni α P' ↔ (α = Act.name SmuniName.pub ∧ P' = smB) := by
  constructor
  · intro h
    rw [ccsLTS_step, smUni, step_restrict_iff] at h
    obtain ⟨P, hαL, hαcoL, hpar, rfl⟩ := h
    rw [step_par_iff] at hpar
    rcases hpar with ⟨CM', hCM, rfl⟩ | ⟨CS', hCS, rfl⟩ | ⟨ℓ, A', B', rfl, _, hA, hB, rfl⟩
    · rw [step_const_iff] at hCM; simp only [smuniDefn, step_pre_iff] at hCM
      obtain ⟨rfl, rfl⟩ := hCM
      exact absurd (show Act.name SmuniName.coin ∈ smuniRestrict by simp [smuniRestrict]) hαL
    · rw [step_const_iff] at hCS; simp only [smuniDefn, step_pre_iff] at hCS
      obtain ⟨rfl, rfl⟩ := hCS
      exact ⟨rfl, rfl⟩
    · rw [step_const_iff] at hA; simp only [smuniDefn, step_pre_iff] at hA
      obtain ⟨rfl, _⟩ := hA
      rw [step_const_iff] at hB; simp only [smuniDefn, step_pre_iff] at hB
      exact absurd hB.1 (by decide)
  · rintro ⟨rfl, rfl⟩
    rw [ccsLTS_step, smUni]
    exact Step.res (by simp [smuniRestrict]) (by simp [smuniRestrict])
      (Step.com2 (Step.con (Step.act _ _)))

theorem smB_step_iff {α : Act SmuniName} {P' : CCS SmuniName SmuniK} :
    (ccsLTS smuniDefn).step smB α P' ↔ (α = Act.tau ∧ P' = smC) := by
  constructor
  · intro h
    rw [ccsLTS_step, step_restrict_iff] at h
    obtain ⟨P, hαL, hαcoL, hpar, rfl⟩ := h
    rw [step_par_iff] at hpar
    rcases hpar with ⟨CM', hCM, rfl⟩ | ⟨CS', hCS, rfl⟩ | ⟨ℓ, A', B', rfl, _, hA, hB, rfl⟩
    · rw [step_const_iff] at hCM; simp only [smuniDefn, step_pre_iff] at hCM
      obtain ⟨rfl, rfl⟩ := hCM
      exact absurd (show Act.name SmuniName.coin ∈ smuniRestrict by simp [smuniRestrict]) hαL
    · rw [step_const_iff] at hCS; simp only [smuniDefn, step_pre_iff] at hCS
      obtain ⟨rfl, rfl⟩ := hCS
      exact absurd (show (Act.coname SmuniName.coin).co ∈ smuniRestrict by simp [smuniRestrict]) hαcoL
    · rw [step_const_iff] at hA; simp only [smuniDefn, step_pre_iff] at hA
      obtain ⟨rfl, rfl⟩ := hA
      rw [step_const_iff] at hB; simp only [smuniDefn, step_pre_iff] at hB
      obtain ⟨_, rfl⟩ := hB
      exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rw [ccsLTS_step]
    exact Step.res (by simp [smuniRestrict]) (by simp [smuniRestrict])
      (Step.com3 (by rintro ⟨⟩) (Step.con (Step.act _ _)) (Step.con (Step.act _ _)))

theorem smC_step_iff {α : Act SmuniName} {P' : CCS SmuniName SmuniK} :
    (ccsLTS smuniDefn).step smC α P' ↔ (α = Act.tau ∧ P' = smUni) := by
  constructor
  · intro h
    rw [ccsLTS_step, step_restrict_iff] at h
    obtain ⟨P, hαL, hαcoL, hpar, rfl⟩ := h
    rw [step_par_iff] at hpar
    rcases hpar with ⟨CM', hCM, rfl⟩ | ⟨CS', hCS, rfl⟩ | ⟨ℓ, A', B', rfl, _, hA, hB, rfl⟩
    · rw [step_const_iff] at hCM; simp only [smuniDefn, step_pre_iff] at hCM
      obtain ⟨rfl, rfl⟩ := hCM
      exact absurd (show (Act.coname SmuniName.coffee).co ∈ smuniRestrict by simp [smuniRestrict])
        hαcoL
    · rw [step_const_iff] at hCS; simp only [smuniDefn, step_pre_iff] at hCS
      obtain ⟨rfl, rfl⟩ := hCS
      exact absurd (show Act.name SmuniName.coffee ∈ smuniRestrict by simp [smuniRestrict]) hαL
    · rw [step_const_iff] at hA; simp only [smuniDefn, step_pre_iff] at hA
      obtain ⟨rfl, rfl⟩ := hA
      rw [step_const_iff] at hB; simp only [smuniDefn, step_pre_iff] at hB
      obtain ⟨_, rfl⟩ := hB
      exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rw [ccsLTS_step, smUni]
    exact Step.res (by simp [smuniRestrict]) (by simp [smuniRestrict])
      (Step.com3 (by rintro ⟨⟩) (Step.con (Step.act _ _)) (Step.con (Step.act _ _)))

theorem smSpec_step_iff {α : Act SmuniName} {P' : CCS SmuniName SmuniK} :
    (ccsLTS smuniDefn).step smSpec α P' ↔ (α = Act.name SmuniName.pub ∧ P' = smSpec) := by
  rw [ccsLTS_step, step_const_iff]
  simp only [smuniDefn, step_pre_iff]

/-! ## The weak bisimulation -/

/-- The candidate weak bisimulation: each of the three reachable `SmUni`-states
relates to `Spec`. -/
def smRel : CCS SmuniName SmuniK → CCS SmuniName SmuniK → Prop := fun x y =>
  (x = smUni ∨ x = smB ∨ x = smC) ∧ y = smSpec

theorem isWeakBisimulation_smRel : IsWeakBisimulation (ccsLTS smuniDefn) Act.tau smRel := by
  have hAB : (ccsLTS smuniDefn).step smUni (Act.name SmuniName.pub) smB := smUni_step_iff.mpr ⟨rfl, rfl⟩
  have hBC : (ccsLTS smuniDefn).step smB Act.tau smC := smB_step_iff.mpr ⟨rfl, rfl⟩
  have hCA : (ccsLTS smuniDefn).step smC Act.tau smUni := smC_step_iff.mpr ⟨rfl, rfl⟩
  have hSpec : (ccsLTS smuniDefn).step smSpec (Act.name SmuniName.pub) smSpec :=
    smSpec_step_iff.mpr ⟨rfl, rfl⟩
  intro p q hR
  obtain ⟨hx, rfl⟩ := hR
  rcases hx with rfl | rfl | rfl
  · -- (SmUni, Spec)
    refine ⟨fun α p' hstep => ?_, fun α q' hstep => ?_⟩
    · rw [smUni_step_iff] at hstep; obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨smSpec, step_weakStep hSpec, ⟨Or.inr (Or.inl rfl), rfl⟩⟩
    · rw [smSpec_step_iff] at hstep; obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨smB, step_weakStep hAB, ⟨Or.inr (Or.inl rfl), rfl⟩⟩
  · -- ((CM∣CS₁)∖L, Spec)
    refine ⟨fun α p' hstep => ?_, fun α q' hstep => ?_⟩
    · rw [smB_step_iff] at hstep; obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨smSpec, weakStep_tau_of_tauStar (tauStar_refl _ _ _), ⟨Or.inr (Or.inr rfl), rfl⟩⟩
    · rw [smSpec_step_iff] at hstep; obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨smB, Or.inr ⟨by decide, smUni, smB, tauStar_trans (tauStar_single hBC)
        (tauStar_single hCA), hAB, tauStar_refl _ _ _⟩, ⟨Or.inr (Or.inl rfl), rfl⟩⟩
  · -- ((CM₁∣CS₂)∖L, Spec)
    refine ⟨fun α p' hstep => ?_, fun α q' hstep => ?_⟩
    · rw [smC_step_iff] at hstep; obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨smSpec, weakStep_tau_of_tauStar (tauStar_refl _ _ _), ⟨Or.inl rfl, rfl⟩⟩
    · rw [smSpec_step_iff] at hstep; obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨smB, Or.inr ⟨by decide, smUni, smB, tauStar_single hCA, hAB,
        tauStar_refl _ _ _⟩, ⟨Or.inr (Or.inl rfl), rfl⟩⟩

/-- **Exercise 3.20** (§3.4, p.58). `SmUni ≈ Spec`: the Small University is
observationally equivalent to `Spec ≝ pub.Spec` (the two internal `coin`/`coffee`
handshakes are unobservable). -/
theorem ex_3_20_smuni : smUni ≈[ccsLTS smuniDefn, Act.tau] smSpec :=
  isWeakBisimulation_smRel.le_weaklyBisimilar ⟨Or.inl rfl, rfl⟩

end DeepWiki.ReactiveSystems
