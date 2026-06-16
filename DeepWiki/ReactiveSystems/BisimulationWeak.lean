import DeepWiki.ReactiveSystems.Bisimulation

/-! # Weak bisimulation and observational equivalence
Abstracting away the internal action `τ`: weak transitions `=α⇒` allow silent
moves around an observable step, a weak bisimulation matches each concrete move
by a weak one, and weak bisimilarity `≈` (observational equivalence) is the
largest weak bisimulation. We prove `≈` is an equivalence relation and that
strong bisimilarity refines it. The silent action `τ` is supplied as a
parameter, so the theory applies to any LTS with a distinguished `τ`. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-- `tauStar L τ`: the reflexive-transitive closure `(→τ)*` of silent steps. -/
def tauStar (L : LTS Proc Act) (tau : Act) : Proc → Proc → Prop :=
  Relation.ReflTransGen fun p q => L.step p tau q

theorem tauStar_refl (L : LTS Proc Act) (tau : Act) (p : Proc) : tauStar L tau p p :=
  Relation.ReflTransGen.refl

theorem tauStar_single {L : LTS Proc Act} {tau : Act} {p q : Proc} (h : L.step p tau q) :
    tauStar L tau p q := Relation.ReflTransGen.single h

theorem tauStar_trans {L : LTS Proc Act} {tau : Act} {p q r : Proc}
    (h₁ : tauStar L tau p q) (h₂ : tauStar L tau q r) : tauStar L tau p r :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Weak transition `p =α⇒ q` (Definition 3.3): for `α = τ`, a chain of silent
steps; for `α ≠ τ`, silent steps surrounding one `α`-step. -/
def WeakStep (L : LTS Proc Act) (tau : Act) (p : Proc) (α : Act) (q : Proc) : Prop :=
  (α = tau ∧ tauStar L tau p q) ∨
  (α ≠ tau ∧ ∃ p' q', tauStar L tau p p' ∧ (L ⊢ p' ⟶[α] q') ∧ tauStar L tau q' q)

/-- Weak transition `L ⊢ p =[α]⇒[τ] q` (the book's `p =α⇒ q`). -/
scoped notation:40 L:max " ⊢ " p:41 " =[" a "]⇒[" t "] " q:41 => LTS.WeakStep L t p a q

/-- A chain of silent steps is a weak `τ`-transition. -/
theorem weakStep_tau_of_tauStar {L : LTS Proc Act} {tau : Act} {p q : Proc}
    (h : tauStar L tau p q) : L ⊢ p =[tau]⇒[tau] q := Or.inl ⟨rfl, h⟩

/-- Every concrete transition is a weak transition. -/
theorem step_weakStep {L : LTS Proc Act} {tau : Act} {p : Proc} {α : Act} {q : Proc}
    (h : L ⊢ p ⟶[α] q) : L ⊢ p =[α]⇒[tau] q := by
  by_cases hα : α = tau
  · subst hα; exact Or.inl ⟨rfl, tauStar_single h⟩
  · exact Or.inr ⟨hα, p, q, tauStar_refl L tau p, h, tauStar_refl L tau q⟩

/-- `IsWeakBisimulation L τ R`: each concrete move of one side is matched by a
*weak* transition of the other side into `R` (Definition 3.4). -/
def IsWeakBisimulation (L : LTS Proc Act) (tau : Act) (R : Proc → Proc → Prop) : Prop :=
  ∀ ⦃p q⦄, R p q →
    (∀ α p', (L ⊢ p ⟶[α] p') → ∃ q', (L ⊢ q =[α]⇒[tau] q') ∧ R p' q') ∧
    (∀ α q', (L ⊢ q ⟶[α] q') → ∃ p', (L ⊢ p =[α]⇒[tau] p') ∧ R p' q')

/-- Weak bisimilarity `p ≈ q` (observational equivalence): some weak bisimulation
relates `p` and `q`. -/
def WeaklyBisimilar (L : LTS Proc Act) (tau : Act) (p q : Proc) : Prop :=
  ∃ R, IsWeakBisimulation L tau R ∧ R p q

/-- Weak bisimilarity `p ≈[L, τ] q` (observational equivalence, the book's
`p ≈ q`). -/
scoped notation:50 p:51 " ≈[" L ", " t "] " q:51 => LTS.WeaklyBisimilar L t p q

variable {L : LTS Proc Act} {tau : Act}

/-- A weak bisimulation can mirror a whole chain of silent steps. -/
theorem IsWeakBisimulation.matchTauStar {R : Proc → Proc → Prop}
    (hR : IsWeakBisimulation L tau R) {p p' : Proc} (hpp' : tauStar L tau p p') :
    ∀ {q}, R p q → ∃ q', tauStar L tau q q' ∧ R p' q' := by
  induction hpp' with
  | refl => exact fun {q} h => ⟨q, tauStar_refl L tau q, h⟩
  | @tail b pe _hchain hstep ih =>
      intro q h
      obtain ⟨qb, hqb, hbb⟩ := ih h
      obtain ⟨q', hw, hb'⟩ := (hR hbb).1 tau pe hstep
      rcases hw with ⟨_, htau⟩ | ⟨hne, _⟩
      · exact ⟨q', tauStar_trans hqb htau, hb'⟩
      · exact absurd rfl hne

/-- A weak bisimulation can mirror a weak transition (not just a concrete one). -/
theorem IsWeakBisimulation.matchWeakStep {R : Proc → Proc → Prop}
    (hR : IsWeakBisimulation L tau R) {p : Proc} {α : Act} {p' : Proc}
    (hw : WeakStep L tau p α p') : ∀ {q}, R p q → ∃ q', WeakStep L tau q α q' ∧ R p' q' := by
  intro q h
  rcases hw with ⟨hα, hts⟩ | ⟨hα, p₁, p₂, h₁, hstep, h₂⟩
  · subst hα
    obtain ⟨q', hq', hb'⟩ := hR.matchTauStar hts h
    exact ⟨q', weakStep_tau_of_tauStar hq', hb'⟩
  · obtain ⟨q₁, hq₁, hb₁⟩ := hR.matchTauStar h₁ h
    obtain ⟨q₂, hwm, hb₂⟩ := (hR hb₁).1 α p₂ hstep
    obtain ⟨q', hq', hb'⟩ := hR.matchTauStar h₂ hb₂
    rcases hwm with ⟨hτ, _⟩ | ⟨_, q₁', q₂', hA, hB, hC⟩
    · exact absurd hτ hα
    · exact ⟨q', Or.inr ⟨hα, q₁', q₂', tauStar_trans hq₁ hA, hB, tauStar_trans hC hq'⟩, hb'⟩

/-- The identity relation is a weak bisimulation. -/
theorem isWeakBisimulation_eq : IsWeakBisimulation L tau (· = ·) := by
  rintro p q rfl
  exact ⟨fun α p' h => ⟨p', step_weakStep h, rfl⟩, fun α q' h => ⟨q', step_weakStep h, rfl⟩⟩

/-- The converse of a weak bisimulation is a weak bisimulation. -/
theorem IsWeakBisimulation.inv {R : Proc → Proc → Prop} (h : IsWeakBisimulation L tau R) :
    IsWeakBisimulation L tau (fun p q => R q p) := by
  rintro p q hqp
  obtain ⟨h1, h2⟩ := h hqp
  exact ⟨fun α p' hp => (h2 α p' hp).imp fun _ => id,
         fun α q' hq => (h1 α q' hq).imp fun _ => id⟩

/-- The composition of two weak bisimulations is a weak bisimulation. -/
theorem IsWeakBisimulation.comp {R S : Proc → Proc → Prop}
    (hR : IsWeakBisimulation L tau R) (hS : IsWeakBisimulation L tau S) :
    IsWeakBisimulation L tau (fun p r => ∃ q, R p q ∧ S q r) := by
  rintro p r ⟨q, hpq, hqr⟩
  refine ⟨fun α p' hp => ?_, fun α r' hr => ?_⟩
  · obtain ⟨q', hwq, hb1⟩ := (hR hpq).1 α p' hp
    obtain ⟨r', hwr, hb2⟩ := hS.matchWeakStep hwq hqr
    exact ⟨r', hwr, q', hb1, hb2⟩
  · obtain ⟨q', hwq, hb2⟩ := (hS hqr).2 α r' hr
    obtain ⟨p', hwp, hb1⟩ := hR.inv.matchWeakStep hwq hpq
    exact ⟨p', hwp, q', hb1, hb2⟩

/-- Weak bisimilarity is itself a weak bisimulation (the union of them all). -/
theorem isWeakBisimulation_weaklyBisimilar :
    IsWeakBisimulation L tau (WeaklyBisimilar L tau) := by
  rintro p q ⟨R, hR, hpq⟩
  obtain ⟨h1, h2⟩ := hR hpq
  refine ⟨fun α p' hp => ?_, fun α q' hq => ?_⟩
  · obtain ⟨q', hw, hb⟩ := h1 α p' hp; exact ⟨q', hw, R, hR, hb⟩
  · obtain ⟨p', hw, hb⟩ := h2 α q' hq; exact ⟨p', hw, R, hR, hb⟩

/-- Any weak bisimulation is contained in weak bisimilarity: `≈` is the largest. -/
theorem IsWeakBisimulation.le_weaklyBisimilar {R : Proc → Proc → Prop}
    (h : IsWeakBisimulation L tau R) : ∀ ⦃p q⦄, R p q → WeaklyBisimilar L tau p q :=
  fun _ _ hpq => ⟨R, h, hpq⟩

@[refl] theorem weaklyBisimilar_refl (p : Proc) : WeaklyBisimilar L tau p p :=
  ⟨(· = ·), isWeakBisimulation_eq, rfl⟩

theorem WeaklyBisimilar.symm {p q : Proc} (h : WeaklyBisimilar L tau p q) :
    WeaklyBisimilar L tau q p := let ⟨_, hR, hpq⟩ := h; ⟨_, hR.inv, hpq⟩

theorem WeaklyBisimilar.trans {p q r : Proc} (hpq : WeaklyBisimilar L tau p q)
    (hqr : WeaklyBisimilar L tau q r) : WeaklyBisimilar L tau p r :=
  let ⟨_, hR, hpq⟩ := hpq; let ⟨_, hS, hqr⟩ := hqr; ⟨_, hR.comp hS, _, hpq, hqr⟩

/-- Weak bisimilarity (observational equivalence) is an equivalence relation. -/
theorem equivalence_weaklyBisimilar : Equivalence (WeaklyBisimilar L tau) :=
  ⟨weaklyBisimilar_refl, WeaklyBisimilar.symm, WeaklyBisimilar.trans⟩

/-- A strong bisimulation is a weak bisimulation. -/
theorem IsBisimulation.isWeakBisimulation {R : Proc → Proc → Prop} (h : IsBisimulation L R) :
    IsWeakBisimulation L tau R := by
  intro p q hpq
  obtain ⟨h1, h2⟩ := h hpq
  exact ⟨fun α p' hp => (h1 α p' hp).imp fun _ => And.imp_left step_weakStep,
         fun α q' hq => (h2 α q' hq).imp fun _ => And.imp_left step_weakStep⟩

/-- Strong bisimilarity refines weak bisimilarity: `p ~ q` implies `p ≈ q`. -/
theorem Bisimilar.weaklyBisimilar {p q : Proc} (h : Bisimilar L p q) :
    WeaklyBisimilar L tau p q := let ⟨_, hR, hpq⟩ := h; ⟨_, hR.isWeakBisimulation, hpq⟩

/-- Mutually `τ`-reachable states are weakly bisimilar (Exercise 3.27): the
relation "each `τ`-reaches the other" is a weak bisimulation. -/
theorem weaklyBisimilar_of_tauStar {p q : Proc}
    (hpq : tauStar L tau p q) (hqp : tauStar L tau q p) : WeaklyBisimilar L tau p q := by
  refine ⟨fun x y => tauStar L tau x y ∧ tauStar L tau y x, ?_, hpq, hqp⟩
  rintro x y ⟨hxy, hyx⟩
  refine ⟨fun α x' hstep => ⟨x', ?_, tauStar_refl L tau x', tauStar_refl L tau x'⟩,
          fun α y' hstep => ⟨y', ?_, tauStar_refl L tau y', tauStar_refl L tau y'⟩⟩
  · by_cases hα : α = tau
    · subst hα; exact Or.inl ⟨rfl, tauStar_trans hyx (tauStar_single hstep)⟩
    · exact Or.inr ⟨hα, x, x', hyx, hstep, tauStar_refl L tau x'⟩
  · by_cases hα : α = tau
    · subst hα; exact Or.inl ⟨rfl, tauStar_trans hxy (tauStar_single hstep)⟩
    · exact Or.inr ⟨hα, y, y', hxy, hstep, tauStar_refl L tau y'⟩

end LTS

end DeepWiki.ReactiveSystems
