import DeepWiki.ReactiveSystems.Bisimulation

/-! # Simulation and the simulation preorder
A one-sided bisimulation: every move of the simulated state must be matched, but
not necessarily conversely. Similarity `⊑` is a preorder coarser than strong
bisimilarity, and ready simulation refines it by also preserving ready sets. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-- `IsSimulation L R`: whenever `R p q`, every `a`-move of `p` is matched by an
`a`-move of `q` into `R` (the forward half of a bisimulation only). -/
def IsSimulation (L : LTS Proc Act) (R : Proc → Proc → Prop) : Prop :=
  ∀ ⦃p q⦄, R p q → ∀ a p', (L ⊢ p ⟶[a] p') → ∃ q', (L ⊢ q ⟶[a] q') ∧ R p' q'

/-- `Simulated L p q` (`p ⊑ q`): `q` simulates `p` — some simulation relates them. -/
def Simulated (L : LTS Proc Act) (p q : Proc) : Prop := ∃ R, IsSimulation L R ∧ R p q

@[inherit_doc] scoped notation:50 p:51 " ⊑[" L "] " q:51 => LTS.Simulated L p q

/-- The identity relation is a simulation. -/
theorem isSimulation_eq (L : LTS Proc Act) : IsSimulation L (· = ·) := by
  rintro p q rfl a p' h; exact ⟨p', h, rfl⟩

/-- The composition of two simulations is a simulation. -/
theorem IsSimulation.comp {L : LTS Proc Act} {R S : Proc → Proc → Prop}
    (hR : IsSimulation L R) (hS : IsSimulation L S) :
    IsSimulation L (fun p r => ∃ q, R p q ∧ S q r) := by
  rintro p r ⟨q, hpq, hqr⟩ a p' hp
  obtain ⟨q', hq', hpq'⟩ := hR hpq a p' hp
  obtain ⟨r', hr', hqr'⟩ := hS hqr a q' hq'
  exact ⟨r', hr', q', hpq', hqr'⟩

/-- The simulation preorder is reflexive: `p ⊑ p`. -/
@[refl] theorem simulated_refl (L : LTS Proc Act) (p : Proc) : Simulated L p p :=
  ⟨(· = ·), isSimulation_eq L, rfl⟩

/-- The simulation preorder is transitive: `p ⊑ q → q ⊑ r → p ⊑ r`. -/
theorem Simulated.trans {L : LTS Proc Act} {p q r : Proc}
    (hpq : Simulated L p q) (hqr : Simulated L q r) : Simulated L p r :=
  let ⟨_, hR, hpq⟩ := hpq; let ⟨_, hS, hqr⟩ := hqr; ⟨_, hR.comp hS, q, hpq, hqr⟩

/-- The simulation preorder is a preorder: reflexive and transitive. -/
theorem simulated_preorder (L : LTS Proc Act) :
    (∀ p, Simulated L p p) ∧
      (∀ p q r, Simulated L p q → Simulated L q r → Simulated L p r) :=
  ⟨simulated_refl L, fun _ _ _ => Simulated.trans⟩

/-- A strong bisimulation is a simulation. -/
theorem IsBisimulation.isSimulation {L : LTS Proc Act} {R : Proc → Proc → Prop}
    (h : IsBisimulation L R) : IsSimulation L R := fun _ _ hpq a p' hp => (h hpq).1 a p' hp

/-- Strong bisimilarity refines the simulation preorder: `p ~ q → p ⊑ q`. -/
theorem Bisimilar.simulated {L : LTS Proc Act} {p q : Proc} (h : Bisimilar L p q) :
    Simulated L p q := let ⟨R, hR, hpq⟩ := h; ⟨R, hR.isSimulation, hpq⟩

/-- The ready set (set of initial actions) of a state. -/
def initials (L : LTS Proc Act) (p : Proc) : Set Act := {a | ∃ p', L.step p a p'}

/-- `IsReadySimulation L R`: a simulation that additionally preserves ready sets. -/
def IsReadySimulation (L : LTS Proc Act) (R : Proc → Proc → Prop) : Prop :=
  IsSimulation L R ∧ ∀ ⦃p q⦄, R p q → initials L p = initials L q

end LTS

end DeepWiki.ReactiveSystems
