import DeepWiki.ReactiveSystems.BisimulationWeak

/-! # Weak simulation, the weak-simulation preorder, and weak traces
The one-sided weak analogue of bisimulation: a *weak simulation* answers each
concrete move of one state by a *weak* transition of the other, and `s'` *weakly
simulates* `s` when some weak simulation relates them. The weak-simulation
preorder is reflexive and transitive, and weak simulation preserves weak traces —
a *weak trace* being a sequence of visible actions performed via weak transitions.
A weak bisimulation is in particular a weak simulation, so observational
equivalence refines the weak-simulation preorder both ways. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-! ## Weak simulation and the weak-simulation preorder -/

/-- `IsWeakSimulation L τ R`: whenever `R s₁ s₂` and `s₁ —α→
s₁'` for any action `α` (including `τ`), there is a *weak* transition `s₂ =α⇒ s₂'`
with `R s₁' s₂'`. -/
def IsWeakSimulation (L : LTS Proc Act) (tau : Act) (R : Proc → Proc → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, R s₁ s₂ →
    ∀ α s₁', (L ⊢ s₁ ⟶[α] s₁') → ∃ s₂', (L ⊢ s₂ =[α]⇒[tau] s₂') ∧ R s₁' s₂'

/-- `s'` *weakly simulates* `s` (`WeaklySimulates L τ s' s`):
some weak simulation `R` relates the simulated `s` to the simulator `s'`. -/
def WeaklySimulates (L : LTS Proc Act) (tau : Act) (s' s : Proc) : Prop :=
  ∃ R, IsWeakSimulation L tau R ∧ R s s'

variable {L : LTS Proc Act} {tau : Act}

/-- A weak simulation mirrors a whole chain of silent steps. -/
theorem IsWeakSimulation.matchTauStar {R : Proc → Proc → Prop}
    (hR : IsWeakSimulation L tau R) {p p' : Proc} (hpp' : tauStar L tau p p') :
    ∀ {q}, R p q → ∃ q', tauStar L tau q q' ∧ R p' q' := by
  induction hpp' with
  | refl => exact fun {q} h => ⟨q, tauStar_refl L tau q, h⟩
  | @tail b pe _hchain hstep ih =>
      intro q h
      obtain ⟨qb, hqb, hbb⟩ := ih h
      obtain ⟨q', hw, hb'⟩ := hR hbb tau pe hstep
      rcases hw with ⟨_, htau⟩ | ⟨hne, _⟩
      · exact ⟨q', tauStar_trans hqb htau, hb'⟩
      · exact absurd rfl hne

/-- A weak simulation mirrors a weak transition (not just a concrete one). -/
theorem IsWeakSimulation.matchWeakStep {R : Proc → Proc → Prop}
    (hR : IsWeakSimulation L tau R) {p : Proc} {α : Act} {p' : Proc}
    (hw : WeakStep L tau p α p') : ∀ {q}, R p q → ∃ q', WeakStep L tau q α q' ∧ R p' q' := by
  intro q h
  rcases hw with ⟨hα, hts⟩ | ⟨hα, p₁, p₂, h₁, hstep, h₂⟩
  · subst hα
    obtain ⟨q', hq', hb'⟩ := hR.matchTauStar hts h
    exact ⟨q', weakStep_tau_of_tauStar hq', hb'⟩
  · obtain ⟨q₁, hq₁, hb₁⟩ := hR.matchTauStar h₁ h
    obtain ⟨q₂, hwm, hb₂⟩ := hR hb₁ α p₂ hstep
    obtain ⟨q', hq', hb'⟩ := hR.matchTauStar h₂ hb₂
    rcases hwm with ⟨hτ, _⟩ | ⟨_, q₁', q₂', hA, hB, hC⟩
    · exact absurd hτ hα
    · exact ⟨q', Or.inr ⟨hα, q₁', q₂', tauStar_trans hq₁ hA, hB, tauStar_trans hC hq'⟩, hb'⟩

/-- The identity relation is a weak simulation. -/
theorem isWeakSimulation_eq : IsWeakSimulation L tau (· = ·) := by
  rintro s₁ s₂ rfl α s₁' hstep
  exact ⟨s₁', step_weakStep hstep, rfl⟩

/-- The composition of two weak simulations is a weak simulation. -/
theorem IsWeakSimulation.comp {R S : Proc → Proc → Prop}
    (hR : IsWeakSimulation L tau R) (hS : IsWeakSimulation L tau S) :
    IsWeakSimulation L tau (fun s u => ∃ t, R s t ∧ S t u) := by
  rintro s u ⟨t, hRst, hStu⟩ α s' hstep
  obtain ⟨t', hwt, hRt'⟩ := hR hRst α s' hstep
  obtain ⟨u', hwu, hSu'⟩ := hS.matchWeakStep hwt hStu
  exact ⟨u', hwu, t', hRt', hSu'⟩

/-- A weak bisimulation is in particular a weak simulation (its forward half). -/
theorem IsWeakBisimulation.isWeakSimulation {R : Proc → Proc → Prop}
    (h : IsWeakBisimulation L tau R) : IsWeakSimulation L tau R :=
  fun _ _ hpq α p' hp => (h hpq).1 α p' hp

/-- Every state weakly simulates itself. -/
theorem weaklySimulates_refl (s : Proc) : WeaklySimulates L tau s s :=
  ⟨(· = ·), isWeakSimulation_eq, rfl⟩

/-- The weak-simulation preorder is transitive: if `s''`
weakly simulates `s'` and `s'` weakly simulates `s`, then `s''` weakly simulates
`s`. -/
theorem WeaklySimulates.trans {s s' s'' : Proc}
    (h1 : WeaklySimulates L tau s'' s') (h2 : WeaklySimulates L tau s' s) :
    WeaklySimulates L tau s'' s := by
  obtain ⟨R, hR, hRs⟩ := h1
  obtain ⟨S, hS, hSs⟩ := h2
  exact ⟨fun b a => ∃ m, S b m ∧ R m a, hS.comp hR, s', hSs, hRs⟩

/-! ## Weak traces and weak trace equivalence -/

/-- A *weak path* `WeakPath L τ p w q`: from `p`, the list `w` of *visible*
actions is performed via weak transitions ending at `q` (the empty list allows
silent drift). -/
def WeakPath (L : LTS Proc Act) (tau : Act) : Proc → List Act → Proc → Prop
  | p, [], q => tauStar L tau p q
  | p, a :: w, q => a ≠ tau ∧ ∃ p', (L ⊢ p =[a]⇒[tau] p') ∧ WeakPath L tau p' w q

/-- The *weak traces* of `p`: the sequences of visible actions
`p` can perform via weak transitions. -/
def WeakTraces (L : LTS Proc Act) (tau : Act) (p : Proc) : Set (List Act) :=
  {w | ∃ q, WeakPath L tau p w q}

/-- *Weak trace equivalence*: equal weak-trace sets. -/
def WeakTraceEquiv (L : LTS Proc Act) (tau : Act) (p q : Proc) : Prop :=
  WeakTraces L tau p = WeakTraces L tau q

/-- The empty weak trace belongs to every state. -/
theorem nil_mem_weakTraces (p : Proc) : [] ∈ WeakTraces L tau p :=
  ⟨p, tauStar_refl L tau p⟩

/-- A weak simulation transports a weak path: if `R s s'` and `s` has a weak path
along `w`, so does `s'`. -/
theorem IsWeakSimulation.weakPath {R : Proc → Proc → Prop} (hR : IsWeakSimulation L tau R) :
    ∀ {s : Proc} {w : List Act} {q s' : Proc},
      WeakPath L tau s w q → R s s' → ∃ q', WeakPath L tau s' w q' := by
  intro s w
  induction w generalizing s with
  | nil =>
      intro q s' hpath hRss'
      obtain ⟨q', hq', _⟩ := hR.matchTauStar hpath hRss'
      exact ⟨q', hq'⟩
  | cons a w ih =>
      intro q s' hpath hRss'
      obtain ⟨hane, p', hws, hrest⟩ := hpath
      obtain ⟨t', hwt, hRp't'⟩ := hR.matchWeakStep hws hRss'
      obtain ⟨q', hpath'⟩ := ih hrest hRp't'
      exact ⟨q', hane, t', hwt, hpath'⟩

/-- If `s'` weakly simulates `s`, then every weak trace of
`s` is also a weak trace of `s'`. -/
theorem WeaklySimulates.weakTraces_subset {s s' : Proc} (h : WeaklySimulates L tau s' s) :
    WeakTraces L tau s ⊆ WeakTraces L tau s' := by
  obtain ⟨R, hR, hRss'⟩ := h
  rintro w ⟨q, hpath⟩
  exact hR.weakPath hpath hRss'

/-! ## Weak bisimilarity refines the weak-simulation preorder and weak traces -/

/-- Weakly bisimilar states weakly simulate each other (each direction is the
forward half of a weak bisimulation). -/
theorem WeaklyBisimilar.weaklySimulates {p q : Proc} (h : WeaklyBisimilar L tau p q) :
    WeaklySimulates L tau q p :=
  let ⟨R, hR, hpq⟩ := h; ⟨R, hR.isWeakSimulation, hpq⟩

/-- **Weak bisimilarity refines weak trace equivalence** (the weak analogue of
`Bisimilar.traceEquiv`): observationally equivalent states have the same weak
traces. -/
theorem WeaklyBisimilar.weakTraceEquiv {p q : Proc} (h : WeaklyBisimilar L tau p q) :
    WeakTraceEquiv L tau p q := by
  show WeakTraces L tau p = WeakTraces L tau q
  ext w
  exact ⟨fun hw => h.weaklySimulates.weakTraces_subset hw,
         fun hw => h.symm.weaklySimulates.weakTraces_subset hw⟩

end LTS

end DeepWiki.ReactiveSystems
