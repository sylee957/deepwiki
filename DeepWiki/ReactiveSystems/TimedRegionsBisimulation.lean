import DeepWiki.ReactiveSystems.TimedRegions
import DeepWiki.ReactiveSystems.TimedBisimulationUntimed

/-! # Region equivalence and untimed bisimilarity
In a *well-formed* timed automaton (all guards and invariants compare clocks only
against constants within the clamp `cmax`), region-equivalent valuations at the
same location are **untimed bisimilar**. The relation "same location,
region-equivalent valuations" is an untimed bisimulation: action steps are matched
using guard invariance and reset preservation (`regionEq_satisfies`,
`RegionEq.reset`), and delay steps using the region time-successor property
(`TimeSuccessor`). The theorem is stated modularly in the time-successor hypothesis
— which holds outright for single-clock automata (`timeSuccessor_of_subsingleton`),
giving the unconditional result there. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- A timed automaton is **well-formed** for `cmax` when every guard and every
location invariant only compares clocks against constants within the clamp
`cmax` (so region equivalence cannot distinguish the states they constrain). -/
def TimedAutomaton.WellFormed {Loc Act C : Type*} (A : TimedAutomaton Loc Act C)
    (cmax : C → ℕ) : Prop :=
  (∀ ℓ g a r ℓ', A.edge ℓ g a r ℓ' → ClockConstraint.BoundedBy cmax g) ∧
  (∀ ℓ, ClockConstraint.BoundedBy cmax (A.inv ℓ))

/-- "Same location, region-equivalent valuations" is an untimed bisimulation on a
well-formed automaton (given the region time-successor property). Action steps
follow the same edge (guard invariance + reset preservation); delay steps are
matched by the time-successor delay. -/
theorem regionEq_untimedBisimulation {Loc Act C : Type*} (A : TimedAutomaton Loc Act C)
    {cmax : C → ℕ} (wf : A.WellFormed cmax) (hts : TimeSuccessor cmax) :
    LTS.IsBisimulation A.tlts.untimedLTS
      (fun s₁ s₂ : Loc × Valuation C => s₁.1 = s₂.1 ∧ RegionEq cmax s₁.2 s₂.2) := by
  obtain ⟨wfg, wfi⟩ := wf
  rintro ⟨ℓ, v⟩ ⟨_, v'⟩ ⟨rfl, hreg⟩
  have hsymm : RegionEq cmax v' v := (regionEq_equivalence cmax).symm hreg
  constructor
  · rintro a ⟨ℓ', v₁⟩ hstep
    match a with
    | some act =>
        obtain ⟨g, r, hedge, hg, hv1, hinv1⟩ := (TimedAutomaton.tlts_act_iff A ℓ v act ℓ' v₁).mp hstep
        subst hv1
        refine ⟨(ℓ', Valuation.reset r v'),
          (TimedAutomaton.tlts_act_iff A ℓ v' act ℓ' (Valuation.reset r v')).mpr
            ⟨g, r, hedge, (regionEq_satisfies hreg (wfg _ _ _ _ _ hedge)).mp hg, rfl,
              (regionEq_satisfies (RegionEq.reset r hreg) (wfi ℓ')).mp hinv1⟩,
          rfl, RegionEq.reset r hreg⟩
    | none =>
        obtain ⟨d, hd⟩ := hstep
        obtain ⟨rfl, hv1, hinvb, hinva⟩ := (TimedAutomaton.tlts_delay_iff A ℓ v d ℓ' v₁).mp hd
        subst hv1
        obtain ⟨d', hreg'⟩ := hts hreg d
        exact ⟨(ℓ', Valuation.add v' d'), ⟨d',
            (TimedAutomaton.tlts_delay_iff A ℓ' v' d' ℓ' (v'.add d')).mpr
              ⟨rfl, rfl, (regionEq_satisfies hreg (wfi ℓ')).mp hinvb,
                (regionEq_satisfies hreg' (wfi ℓ')).mp hinva⟩⟩,
          rfl, hreg'⟩
  · rintro a ⟨ℓ', v₁⟩ hstep
    match a with
    | some act =>
        obtain ⟨g, r, hedge, hg, hv1, hinv1⟩ := (TimedAutomaton.tlts_act_iff A ℓ v' act ℓ' v₁).mp hstep
        subst hv1
        refine ⟨(ℓ', Valuation.reset r v),
          (TimedAutomaton.tlts_act_iff A ℓ v act ℓ' (Valuation.reset r v)).mpr
            ⟨g, r, hedge, (regionEq_satisfies hsymm (wfg _ _ _ _ _ hedge)).mp hg, rfl,
              (regionEq_satisfies (RegionEq.reset r hsymm) (wfi ℓ')).mp hinv1⟩,
          rfl, RegionEq.reset r hreg⟩
    | none =>
        obtain ⟨d, hd⟩ := hstep
        obtain ⟨rfl, hv1, hinvb, hinva⟩ := (TimedAutomaton.tlts_delay_iff A ℓ v' d ℓ' v₁).mp hd
        subst hv1
        obtain ⟨d', hreg'⟩ := hts hsymm d
        exact ⟨(ℓ', Valuation.add v d'), ⟨d',
            (TimedAutomaton.tlts_delay_iff A ℓ' v d' ℓ' (v.add d')).mpr
              ⟨rfl, rfl, (regionEq_satisfies hsymm (wfi ℓ')).mp hinvb,
                (regionEq_satisfies hreg' (wfi ℓ')).mp hinva⟩⟩,
          rfl, (regionEq_equivalence cmax).symm hreg'⟩

/-- Untimed-bisimilarity result, modular form. In a well-formed timed automaton
with the region time-successor property, region-equivalent valuations at the same
location are untimed bisimilar. -/
theorem regionEq_untimedBisimilar {Loc Act C : Type*} (A : TimedAutomaton Loc Act C)
    {cmax : C → ℕ} (wf : A.WellFormed cmax) (hts : TimeSuccessor cmax)
    {ℓ : Loc} {v v' : Valuation C} (h : RegionEq cmax v v') :
    A.tlts.UntimedBisimilar (ℓ, v) (ℓ, v') :=
  (regionEq_untimedBisimulation A wf hts).le_bisimilar ⟨rfl, h⟩

/-- Single-clock timed automata (unconditional): the region time-successor
property holds outright when there is at most one clock, so region-equivalent
valuations at the same location are untimed bisimilar. -/
theorem regionEq_untimedBisimilar_of_subsingleton {Loc Act C : Type*} [Subsingleton C]
    (A : TimedAutomaton Loc Act C) {cmax : C → ℕ} (wf : A.WellFormed cmax)
    {ℓ : Loc} {v v' : Valuation C} (h : RegionEq cmax v v') :
    A.tlts.UntimedBisimilar (ℓ, v) (ℓ, v') :=
  regionEq_untimedBisimilar A wf (timeSuccessor_of_subsingleton cmax) h

/-- Untimed-bisimilarity result, **unconditional for finite clock sets**. A timed
automaton has finitely many clocks, so the general region time-successor property
(`timeSuccessor_of_fintype`) holds, and region-equivalent valuations at the same
location are untimed bisimilar — no extra hypothesis. -/
theorem regionEq_untimedBisimilar_of_fintype {Loc Act C : Type*} [Fintype C]
    (A : TimedAutomaton Loc Act C) {cmax : C → ℕ} (wf : A.WellFormed cmax)
    {ℓ : Loc} {v v' : Valuation C} (h : RegionEq cmax v v') :
    A.tlts.UntimedBisimilar (ℓ, v) (ℓ, v') :=
  regionEq_untimedBisimilar A wf (timeSuccessor_of_fintype cmax) h

end DeepWiki.ReactiveSystems
