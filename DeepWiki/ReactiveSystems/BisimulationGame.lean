import DeepWiki.ReactiveSystems.Bisimulation
import DeepWiki.ReactiveSystems.BisimulationWeak

/-! # The bisimulation game
The strong/weak bisimulation games (§3.5): from a configuration `(p, q)` the
attacker challenges with a move of one side, and the defender must answer with a
matching move (a concrete one in the strong game, a weak transition `=α⇒` in the
weak game) on the other side; the new configuration is the pair of targets. The
defender wins every infinite play and every finite play in which the attacker is
stuck; the attacker wins when the defender is stuck.

A positional defender winning strategy is exactly an invariant set of
configurations in which every attacker challenge can be answered — i.e. a
(weak) bisimulation. This yields Propositions 3.3 and 3.4: the defender has a
winning strategy from `(p, q)` iff `p ~ q` (resp. `p ≈ q`). -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-- A configuration of the bisimulation game: a pair of states. -/
abbrev GameConfig (Proc : Type*) := Proc × Proc

/-- One round of the strong bisimulation game leads from `c` to `c'` when both
states move under a common action — the attacker challenges on one side, the
defender matches on the other (Definition 3.5). -/
def GameRound (L : LTS Proc Act) (c c' : GameConfig Proc) : Prop :=
  ∃ a, L.step c.1 a c'.1 ∧ L.step c.2 a c'.2

/-- A configuration where the attacker is stuck (neither state can move): a
defender win. -/
def AttackerStuck (L : LTS Proc Act) (c : GameConfig Proc) : Prop :=
  (∀ a p', ¬ L.step c.1 a p') ∧ (∀ a q', ¬ L.step c.2 a q')

/-- A defender winning strategy in the strong game (Definition 3.5; the invariant
of Exercise 3.38): a set `R` of configurations in which, from any `(p, q) ∈ R`,
every attacker challenge can be answered on the other side, staying in `R`. -/
def DefenderStrategy (L : LTS Proc Act) (R : Proc → Proc → Prop) : Prop :=
  ∀ ⦃p q⦄, R p q →
    (∀ a p', L.step p a p' → ∃ q', L.step q a q' ∧ R p' q') ∧
    (∀ a q', L.step q a q' → ∃ p', L.step p a p' ∧ R p' q')

/-- The defender wins the strong bisimulation game from `(p, q)`: some winning
strategy relates them. -/
def DefenderWins (L : LTS Proc Act) (p q : Proc) : Prop :=
  ∃ R, DefenderStrategy L R ∧ R p q

/-- A defender winning strategy is exactly a strong bisimulation. -/
theorem defenderStrategy_iff (L : LTS Proc Act) (R : Proc → Proc → Prop) :
    DefenderStrategy L R ↔ IsBisimulation L R := Iff.rfl

/-- Following a winning strategy, the defender answers any left-attack. -/
theorem DefenderStrategy.respondLeft {L : LTS Proc Act} {R : Proc → Proc → Prop}
    (hR : DefenderStrategy L R) {p q : Proc} (hpq : R p q) {a p'} (hatt : L.step p a p') :
    ∃ q', L.step q a q' ∧ R p' q' := (hR hpq).1 a p' hatt

/-- Following a winning strategy, the defender answers any right-attack. -/
theorem DefenderStrategy.respondRight {L : LTS Proc Act} {R : Proc → Proc → Prop}
    (hR : DefenderStrategy L R) {p q : Proc} (hpq : R p q) {a q'} (hatt : L.step q a q') :
    ∃ p', L.step p a p' ∧ R p' q' := (hR hpq).2 a q' hatt

/-- Operational soundness of a winning strategy: from any configuration in `R`,
the defender is never the stuck player — either the attacker is already stuck (a
defender win), or the defender completes the round into `R`. -/
theorem DefenderStrategy.not_stuck {L : LTS Proc Act} {R : Proc → Proc → Prop}
    (hR : DefenderStrategy L R) {p q : Proc} (hpq : R p q) :
    AttackerStuck L (p, q) ∨ ∃ c', GameRound L (p, q) c' ∧ R c'.1 c'.2 := by
  by_cases h : (∃ a p', L.step p a p') ∨ (∃ a q', L.step q a q')
  · refine Or.inr ?_
    rcases h with ⟨a, p', hp⟩ | ⟨a, q', hq⟩
    · obtain ⟨q', hq', hr⟩ := (hR hpq).1 a p' hp; exact ⟨(p', q'), ⟨a, hp, hq'⟩, hr⟩
    · obtain ⟨p', hp', hr⟩ := (hR hpq).2 a q' hq; exact ⟨(p', q'), ⟨a, hp', hq⟩, hr⟩
  · simp only [not_or, not_exists] at h
    exact Or.inl h

/-- **Proposition 3.3** (§3.5). The defender has a winning strategy in the strong
bisimulation game from `(p, q)` iff `p ~ q`. -/
theorem defenderWins_iff_bisimilar (L : LTS Proc Act) (p q : Proc) :
    DefenderWins L p q ↔ Bisimilar L p q := Iff.rfl

/-- **Proposition 3.3**, attacker side. By determinacy, the attacker has a winning
strategy — i.e. there is no defender winning strategy — exactly when `p ≁ q`. -/
theorem no_defenderWins_iff_not_bisimilar (L : LTS Proc Act) (p q : Proc) :
    ¬ DefenderWins L p q ↔ ¬ Bisimilar L p q :=
  not_congr (defenderWins_iff_bisimilar L p q)

/-! ## The weak bisimulation game (Definition 3.6) -/

/-- A defender winning strategy in the weak game (Definition 3.6): each concrete
attacker move is answered by a *weak* transition `=α⇒` on the other side, staying
in `R`. -/
def DefenderStrategyWeak (L : LTS Proc Act) (tau : Act) (R : Proc → Proc → Prop) : Prop :=
  ∀ ⦃p q⦄, R p q →
    (∀ α p', L.step p α p' → ∃ q', WeakStep L tau q α q' ∧ R p' q') ∧
    (∀ α q', L.step q α q' → ∃ p', WeakStep L tau p α p' ∧ R p' q')

/-- The defender wins the weak bisimulation game from `(p, q)`. -/
def DefenderWinsWeak (L : LTS Proc Act) (tau : Act) (p q : Proc) : Prop :=
  ∃ R, DefenderStrategyWeak L tau R ∧ R p q

/-- A defender weak-game strategy is exactly a weak bisimulation. -/
theorem defenderStrategyWeak_iff (L : LTS Proc Act) (tau : Act) (R : Proc → Proc → Prop) :
    DefenderStrategyWeak L tau R ↔ IsWeakBisimulation L tau R := Iff.rfl

/-- **Proposition 3.4** (§3.5). The defender has a winning strategy in the weak
bisimulation game from `(p, q)` iff `p ≈ q`. -/
theorem defenderWinsWeak_iff_weaklyBisimilar (L : LTS Proc Act) (tau : Act) (p q : Proc) :
    DefenderWinsWeak L tau p q ↔ WeaklyBisimilar L tau p q := Iff.rfl

end LTS

end DeepWiki.ReactiveSystems
