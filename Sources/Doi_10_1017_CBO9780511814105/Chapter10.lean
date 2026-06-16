import DeepWiki.ReactiveSystems.TimedAutomata
import DeepWiki.ReactiveSystems.NetworkTimedAutomata
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 10: Timed automata
Book-numbered restatements for the syntax (§10.2), semantics (§10.3) and networks
(§10.4) of timed automata, discharged by the `DeepWiki.ReactiveSystems` library. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems

/-! ## §10.2 Syntax of timed automata -/

/-- **Definition 10.1** (§10.2, p.176). Clock constraints / guards
`g ::= tt ∣ x ⋈ n ∣ g₁ ∧ g₂`. The library's `ClockConstraint`. -/
abbrev def_10_1 := @ClockConstraint

/-- **§10.2** (p.176), the increment `v + d` of a clock valuation by a delay. -/
abbrev valuation_add := @Valuation.add

/-- **§10.2** (p.176), the reset `v[r]` of the clocks in `r` to zero. -/
noncomputable def valuation_reset := @Valuation.reset

/-- **Definition 10.2** (§10.2, p.177). Evaluation of a clock constraint under a
valuation. The library's `satisfies`. -/
abbrev def_10_2 := @satisfies

/-- **Definition 10.4** (§10.2, p.179). A timed automaton: locations, an edge
relation carrying guard/action/reset, and location invariants. The library's
`TimedAutomaton`. -/
abbrev def_10_4 := @TimedAutomaton

/-! ## §10.3 Semantics of timed automata -/

/-- **Definition 10.5** (§10.3, p.180). The timed LTS `T(A)` denoted by a timed
automaton — guarded action transitions with clock resets, and delay transitions
that advance all clocks within the location invariant. The library's
`TimedAutomaton.tlts`. -/
noncomputable def def_10_5 := @TimedAutomaton.tlts

/-- **Definition 10.5** (§10.3, p.180). The semantics of a timed automaton has
deterministic delay transitions (time-determinism axiom 9.2). -/
theorem def_10_5_timeDeterministic {Loc Act C : Type*} (A : TimedAutomaton Loc Act C) :
    A.tlts.TimeDeterministic := A.timeDeterministic

/-! ## §10.4 Networks of timed automata -/

/-- **§10.4** (p.187). Network actions `Act = {c! ∣ c} ∪ {c? ∣ c} ∪ N` with the
complementary channel actions `c!`/`c?`. The library's `NetAct`. -/
abbrev netAct := @NetAct

/-- **Definition 10.6** (§10.4, p.187). A (binary) network of timed automata
`A₁ ∣ A₂` over a shared clock set, as a timed automaton over location pairs:
independent `N`-moves of each component and `τ`-synchronisations on complementary
channels. The library's `networkAutomaton`. -/
abbrev def_10_6 := @networkAutomaton

/-- **Definition 10.7** (§10.4, p.188). The TLTS `T(A)` of a network: states pair
the component locations with the shared valuation; actions/syncs as above and a
*simultaneous* delay of all components (the conjoined invariant). The library's
`networkTLTS`. -/
noncomputable abbrev def_10_7 := @networkTLTS

/-- **Definition 10.7** (§10.4, p.188), synchronisation rule. Complementary
channel edges (`c!` in `A₁`, `c?` in `A₂`) yield an internal `τ`-move of the
network. -/
theorem def_10_7_sync {Chan Ord C L₁ L₂ : Type*}
    (A₁ : TimedAutomaton L₁ (NetAct Chan Ord) C) (A₂ : TimedAutomaton L₂ (NetAct Chan Ord) C)
    {ℓ₁ ℓ₁' : L₁} {ℓ₂ ℓ₂' : L₂} {c : Chan} {g₁ g₂ : ClockConstraint C} {r₁ r₂ : Set C}
    {v : Valuation C} (h₁ : A₁.edge ℓ₁ g₁ (NetAct.out c) r₁ ℓ₁')
    (h₂ : A₂.edge ℓ₂ g₂ (NetAct.inp c) r₂ ℓ₂')
    (hg : satisfies v (ClockConstraint.and g₁ g₂))
    (hinv : satisfies (Valuation.reset (r₁ ∪ r₂) v)
      ((networkAutomaton A₁ A₂).inv (ℓ₁', ℓ₂'))) :
    (networkTLTS A₁ A₂).act ((ℓ₁, ℓ₂), v) NetAct.tau
      ((ℓ₁', ℓ₂'), Valuation.reset (r₁ ∪ r₂) v) :=
  networkTLTS_sync A₁ A₂ h₁ h₂ hg hinv

/-- **Definition 10.3** (§10.1, p.177). Two clock constraints are equivalent iff
satisfied by the same valuations. The library's `ConstraintEquiv` (an equivalence
relation, `constraintEquiv_equivalence`). -/
abbrev def_10_3 := @DeepWiki.ReactiveSystems.ConstraintEquiv

/-- **Exercise 10.2** (§10.1, p.177). There is a clock constraint satisfied by
every valuation (`tt`) and one satisfied by no valuation (`x < 0`, impossible over
`ℝ≥0`). -/
theorem ex_10_2 {C : Type*} (x : C) :
    (∃ g : DeepWiki.ReactiveSystems.ClockConstraint C,
        ∀ v, DeepWiki.ReactiveSystems.satisfies v g) ∧
    (∃ g : DeepWiki.ReactiveSystems.ClockConstraint C,
        ∀ v, ¬ DeepWiki.ReactiveSystems.satisfies v g) :=
  ⟨⟨.true_, DeepWiki.ReactiveSystems.satisfies_true_all⟩,
   ⟨.atom x .lt 0, DeepWiki.ReactiveSystems.not_satisfies_lt_zero x⟩⟩

end DeepWiki.Rs
