import DeepWiki.ReactiveSystems.LabelledTransitionSystems

/-! # Strong bisimulation and strong bisimilarity
The central behavioural equivalence: a relation is a strong bisimulation when
matching transitions can always be answered on both sides, and two states are
strongly bisimilar (`~`) when some bisimulation relates them. We prove the
master result that `~` is an equivalence relation, the largest strong
bisimulation, and itself satisfies the bisimulation transfer property. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*} (L : LTS Proc Act)

/-- `IsBisimulation L R`: `R` is a strong bisimulation — whenever `R p q`, every
`a`-move of `p` is matched by an `a`-move of `q` into the relation, and
symmetrically every `a`-move of `q` is matched by one of `p`. -/
def IsBisimulation (R : Proc → Proc → Prop) : Prop :=
  ∀ ⦃p q⦄, R p q →
    (∀ a p', (L ⊢ p ⟶[a] p') → ∃ q', (L ⊢ q ⟶[a] q') ∧ R p' q') ∧
    (∀ a q', (L ⊢ q ⟶[a] q') → ∃ p', (L ⊢ p ⟶[a] p') ∧ R p' q')

/-- Strong bisimilarity `p ~ q`: some strong bisimulation relates `p` and `q`. -/
def Bisimilar (p q : Proc) : Prop := ∃ R, IsBisimulation L R ∧ R p q

/-- Strong bisimilarity `p ~[L] q` (the book's `p ~ q`). -/
scoped notation:50 p:51 " ~[" L "] " q:51 => LTS.Bisimilar L p q

variable {L}

/-- The identity relation is a strong bisimulation. -/
theorem isBisimulation_eq : IsBisimulation L (· = ·) := by
  rintro p q rfl
  exact ⟨fun a p' h => ⟨p', h, rfl⟩, fun a q' h => ⟨q', h, rfl⟩⟩

/-- The converse of a strong bisimulation is a strong bisimulation. -/
theorem IsBisimulation.inv {R : Proc → Proc → Prop} (h : IsBisimulation L R) :
    IsBisimulation L (fun p q => R q p) := by
  rintro p q hqp
  obtain ⟨h1, h2⟩ := h hqp
  exact ⟨fun a p' hp => (h2 a p' hp).imp fun _ => id,
         fun a q' hq => (h1 a q' hq).imp fun _ => id⟩

/-- The composition of two strong bisimulations is a strong bisimulation. -/
theorem IsBisimulation.comp {R S : Proc → Proc → Prop}
    (hR : IsBisimulation L R) (hS : IsBisimulation L S) :
    IsBisimulation L (fun p r => ∃ q, R p q ∧ S q r) := by
  rintro p r ⟨q, hpq, hqr⟩
  obtain ⟨hR1, hR2⟩ := hR hpq
  obtain ⟨hS1, hS2⟩ := hS hqr
  refine ⟨fun a p' hp => ?_, fun a r' hr => ?_⟩
  · obtain ⟨q', hq', hpq'⟩ := hR1 a p' hp
    obtain ⟨r', hr', hqr'⟩ := hS1 a q' hq'
    exact ⟨r', hr', q', hpq', hqr'⟩
  · obtain ⟨q', hq', hqr'⟩ := hS2 a r' hr
    obtain ⟨p', hp', hpq'⟩ := hR2 a q' hq'
    exact ⟨p', hp', q', hpq', hqr'⟩

/-- Strong bisimilarity is itself a strong bisimulation (the union of them all). -/
theorem isBisimulation_bisimilar : IsBisimulation L (Bisimilar L) := by
  rintro p q ⟨R, hR, hpq⟩
  obtain ⟨h1, h2⟩ := hR hpq
  refine ⟨fun a p' hp => ?_, fun a q' hq => ?_⟩
  · obtain ⟨q', hq', hpq'⟩ := h1 a p' hp; exact ⟨q', hq', R, hR, hpq'⟩
  · obtain ⟨p', hp', hpq'⟩ := h2 a q' hq; exact ⟨p', hp', R, hR, hpq'⟩

/-- Any strong bisimulation is contained in strong bisimilarity: `~` is the
largest strong bisimulation. -/
theorem IsBisimulation.le_bisimilar {R : Proc → Proc → Prop} (h : IsBisimulation L R) :
    ∀ ⦃p q⦄, R p q → Bisimilar L p q := fun _ _ hpq => ⟨R, h, hpq⟩

/-- Strong bisimilarity is reflexive: `p ~ p`. -/
@[refl] theorem bisimilar_refl (p : Proc) : Bisimilar L p p :=
  ⟨(· = ·), isBisimulation_eq, rfl⟩

/-- Strong bisimilarity is symmetric: `p ~ q → q ~ p`. -/
theorem Bisimilar.symm {p q : Proc} (h : Bisimilar L p q) : Bisimilar L q p :=
  let ⟨_, hR, hpq⟩ := h; ⟨_, hR.inv, hpq⟩

/-- Strong bisimilarity is transitive: `p ~ q → q ~ r → p ~ r`. -/
theorem Bisimilar.trans {p q r : Proc}
    (hpq : Bisimilar L p q) (hqr : Bisimilar L q r) : Bisimilar L p r :=
  let ⟨_, hR, hpq⟩ := hpq
  let ⟨_, hS, hqr⟩ := hqr
  ⟨_, hR.comp hS, q, hpq, hqr⟩

/-- Strong bisimilarity is an equivalence relation. -/
theorem equivalence_bisimilar : Equivalence (Bisimilar L) :=
  ⟨bisimilar_refl, Bisimilar.symm, Bisimilar.trans⟩

/-- Strong bisimilarity satisfies the bisimulation transfer property: `p ~ q`
iff every move of one side is matched by a `~`-related move of the other.
(The book's fixed-point property of `~`.) -/
theorem bisimilar_iff (p q : Proc) :
    (p ~[L] q) ↔
      (∀ a p', (L ⊢ p ⟶[a] p') → ∃ q', (L ⊢ q ⟶[a] q') ∧ (p' ~[L] q')) ∧
      (∀ a q', (L ⊢ q ⟶[a] q') → ∃ p', (L ⊢ p ⟶[a] p') ∧ (p' ~[L] q')) := by
  constructor
  · exact fun h => isBisimulation_bisimilar h
  · intro h
    refine ⟨fun a b => Bisimilar L a b ∨ (a = p ∧ b = q), ?_, Or.inr ⟨rfl, rfl⟩⟩
    rintro x y (hxy | ⟨rfl, rfl⟩)
    · obtain ⟨h1, h2⟩ := isBisimulation_bisimilar hxy
      exact ⟨fun a x' hx => (h1 a x' hx).imp fun _ => And.imp_right Or.inl,
             fun a y' hy => (h2 a y' hy).imp fun _ => And.imp_right Or.inl⟩
    · exact ⟨fun a x' hx => (h.1 a x' hx).imp fun _ => And.imp_right Or.inl,
             fun a y' hy => (h.2 a y' hy).imp fun _ => And.imp_right Or.inl⟩

/-- A state with an outgoing transition is never bisimilar to a deadlocked state. -/
theorem not_bisim_dead_of_step {x y x' : Proc} {a : Act} (hx : L ⊢ x ⟶[a] x')
    (hy : ∀ a' y', ¬ (L ⊢ y ⟶[a'] y')) : ¬ (x ~[L] y) :=
  fun h => let ⟨y', hstep, _⟩ := ((bisimilar_iff x y).mp h).1 a x' hx; hy a y' hstep

end LTS

end DeepWiki.ReactiveSystems
