import DeepWiki.ReactiveSystems.Traces
import DeepWiki.ReactiveSystems.BisimulationWeak
import DeepWiki.ReactiveSystems.SimulationWeak

/-! # String bisimilarity coincides with bisimilarity
A *string bisimulation* matches whole action-sequences (`Path`) rather than single
steps; a *weak string bisimulation* matches observable sequences (`WeakPath`).
Either notion of "string bisimilar" coincides with the corresponding
(strong/weak) bisimilarity, because a single step is a length-one path and any
path decomposes into single steps. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*} {L : LTS Proc Act}

/-! ## String bisimilarity = strong bisimilarity -/

/-- `R` is a *string bisimulation*: related states match each other's
action-sequence paths into `R`. -/
def IsStringBisimulation (L : LTS Proc Act) (R : Proc → Proc → Prop) : Prop :=
  ∀ ⦃p q⦄, R p q →
    (∀ s p', Path L p s p' → ∃ q', Path L q s q' ∧ R p' q') ∧
    (∀ s q', Path L q s q' → ∃ p', Path L p s p' ∧ R p' q')

/-- `p` and `q` are *string bisimilar*: some string bisimulation relates them. -/
def StringBisimilar (L : LTS Proc Act) (p q : Proc) : Prop :=
  ∃ R, IsStringBisimulation L R ∧ R p q

/-- Strong bisimilarity is a string bisimulation (it mirrors whole paths). -/
theorem isStringBisimulation_bisimilar : IsStringBisimulation L (Bisimilar L) := by
  intro p q hpq
  refine ⟨fun s p' hp => hpq.path_forward hp, fun s q' hq => ?_⟩
  obtain ⟨p', hp', hb⟩ := hpq.symm.path_forward hq
  exact ⟨p', hp', hb.symm⟩

/-- A string bisimulation is a strong bisimulation (a single step is a
length-one path). -/
theorem isBisimulation_of_isStringBisimulation {R : Proc → Proc → Prop}
    (h : IsStringBisimulation L R) : IsBisimulation L R := by
  intro p q hpq
  obtain ⟨hf, hb⟩ := h hpq
  refine ⟨fun a p' hstep => ?_, fun a q' hstep => ?_⟩
  · obtain ⟨q', hpath, hr⟩ := hf [a] p' (Path.cons hstep (Path.nil p'))
    cases hpath with | cons hs hrest => cases hrest with | nil => exact ⟨_, hs, hr⟩
  · obtain ⟨p', hpath, hr⟩ := hb [a] q' (Path.cons hstep (Path.nil q'))
    cases hpath with | cons hs hrest => cases hrest with | nil => exact ⟨_, hs, hr⟩

/-- String bisimilarity coincides with strong bisimilarity. -/
theorem stringBisimilar_iff_bisimilar (p q : Proc) :
    StringBisimilar L p q ↔ Bisimilar L p q := by
  constructor
  · rintro ⟨R, hR, hpq⟩
    exact (isBisimulation_of_isStringBisimulation hR).le_bisimilar hpq
  · exact fun h => ⟨Bisimilar L, isStringBisimulation_bisimilar, h⟩

/-! ## Weak string bisimilarity = weak bisimilarity -/

variable {tau : Act}

/-- A weak bisimulation transports a weak path, keeping the endpoints related. -/
theorem IsWeakBisimulation.matchWeakPath {R : Proc → Proc → Prop}
    (hR : IsWeakBisimulation L tau R) :
    ∀ {p : Proc} {w : List Act} {p' q : Proc},
      WeakPath L tau p w p' → R p q → ∃ q', WeakPath L tau q w q' ∧ R p' q' := by
  intro p w
  induction w generalizing p with
  | nil =>
      intro p' q hpath hRpq
      obtain ⟨q', hq', hb⟩ := hR.matchTauStar hpath hRpq
      exact ⟨q', hq', hb⟩
  | cons a w ih =>
      intro p' q hpath hRpq
      obtain ⟨hane, p₁, hws, hrest⟩ := hpath
      obtain ⟨q₁, hwq, hb₁⟩ := hR.matchWeakStep hws hRpq
      obtain ⟨q', hpath', hb'⟩ := ih hrest hb₁
      exact ⟨q', ⟨hane, q₁, hwq, hpath'⟩, hb'⟩

/-- `R` is a *weak string bisimulation*: related states match each other's
observable-sequence weak paths into `R`. -/
def IsWeakStringBisimulation (L : LTS Proc Act) (tau : Act) (R : Proc → Proc → Prop) : Prop :=
  ∀ ⦃p q⦄, R p q →
    (∀ w p', WeakPath L tau p w p' → ∃ q', WeakPath L tau q w q' ∧ R p' q') ∧
    (∀ w q', WeakPath L tau q w q' → ∃ p', WeakPath L tau p w p' ∧ R p' q')

/-- `p` and `q` are *weakly string bisimilar*: some weak string bisimulation
relates them. -/
def WeaklyStringBisimilar (L : LTS Proc Act) (tau : Act) (p q : Proc) : Prop :=
  ∃ R, IsWeakStringBisimulation L tau R ∧ R p q

/-- Weak bisimilarity is a weak string bisimulation. -/
theorem isWeakStringBisimulation_weaklyBisimilar :
    IsWeakStringBisimulation L tau (WeaklyBisimilar L tau) := by
  intro p q hpq
  refine ⟨fun w p' hpath =>
    isWeakBisimulation_weaklyBisimilar.matchWeakPath hpath hpq, fun w q' hpath => ?_⟩
  obtain ⟨p', hp', hb⟩ := isWeakBisimulation_weaklyBisimilar.matchWeakPath hpath hpq.symm
  exact ⟨p', hp', hb.symm⟩

/-- A weak string bisimulation is a weak bisimulation (a single step embeds as a
length-≤1 weak path; trailing silent steps are absorbed). -/
theorem isWeakBisimulation_of_isWeakStringBisimulation {R : Proc → Proc → Prop}
    (h : IsWeakStringBisimulation L tau R) : IsWeakBisimulation L tau R := by
  intro p q hpq
  obtain ⟨hf, hb⟩ := h hpq
  refine ⟨fun α p' hstep => ?_, fun α q' hstep => ?_⟩
  · by_cases hα : α = tau
    · subst hα
      obtain ⟨q', hpath, hr⟩ := hf [] p' (tauStar_single hstep)
      exact ⟨q', weakStep_tau_of_tauStar hpath, hr⟩
    · obtain ⟨q', hpath, hr⟩ := hf [α] p' ⟨hα, p', step_weakStep hstep, tauStar_refl _ _ _⟩
      obtain ⟨_, q₁, hwq, hrest⟩ := hpath
      exact ⟨q', weakStep_trans_tauStar hwq hrest, hr⟩
  · by_cases hα : α = tau
    · subst hα
      obtain ⟨p', hpath, hr⟩ := hb [] q' (tauStar_single hstep)
      exact ⟨p', weakStep_tau_of_tauStar hpath, hr⟩
    · obtain ⟨p', hpath, hr⟩ := hb [α] q' ⟨hα, q', step_weakStep hstep, tauStar_refl _ _ _⟩
      obtain ⟨_, p₁, hwp, hrest⟩ := hpath
      exact ⟨p', weakStep_trans_tauStar hwp hrest, hr⟩

/-- Weak string bisimilarity coincides with weak bisimilarity. -/
theorem weaklyStringBisimilar_iff_weaklyBisimilar (p q : Proc) :
    WeaklyStringBisimilar L tau p q ↔ WeaklyBisimilar L tau p q := by
  constructor
  · rintro ⟨R, hR, hpq⟩
    exact (isWeakBisimulation_of_isWeakStringBisimulation hR).le_weaklyBisimilar hpq
  · exact fun h => ⟨WeaklyBisimilar L tau, isWeakStringBisimulation_weaklyBisimilar, h⟩

end LTS

end DeepWiki.ReactiveSystems
