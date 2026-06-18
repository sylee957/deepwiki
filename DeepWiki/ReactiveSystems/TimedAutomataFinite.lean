import DeepWiki.ReactiveSystems.SymbolicModelCheckingDecidable

/-! # Finite-data timed automata (executable carrier)
The executable counterpart of `TimedAutomaton`: a `FinAutomaton` carries its edges
as a **finite list** of `(ℓ, g, a, reset-list, ℓ')` tuples (resets as `List C`),
together with location invariants and an initial location — pure data, no
`noncomputable`. Its interpretation `toTimedAutomaton` reads the edge relation off
the list (resets coerced to sets), so the entire real-valued region theory applies
verbatim. The constructive clamp `cmax` (the pointwise maximum of every guard/invariant
constant) makes the interpretation `WellFormed`, the entry point for the bounded
finite-region decision procedure. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {Loc Act C : Type*}

/-- A **finite-data timed automaton**: an initial location, a finite list of edges
`(ℓ, g, a, r, ℓ')` (the reset `r` a `List C`), and location invariants. The
computable carrier underlying the model-checking decision procedure. -/
structure FinAutomaton (Loc Act C : Type*) where
  /-- The initial location. -/
  initial : Loc
  /-- The finite edge list `(ℓ, guard, action, reset-list, ℓ')`. -/
  edges : List (Loc × ClockConstraint C × Act × List C × Loc)
  /-- The location invariants. -/
  inv : Loc → ClockConstraint C

namespace FinAutomaton

/-- The `TimedAutomaton` denoted by a `FinAutomaton`: the edge relation `ℓ —g,a,r→ ℓ'`
holds when some list edge `(ℓ, g, a, rl, ℓ')` has the reset set `r = ↑rl`. -/
def toTimedAutomaton (A : FinAutomaton Loc Act C) : TimedAutomaton Loc Act C where
  initial := A.initial
  edge ℓ g a r ℓ' := ∃ rl : List C, (ℓ, g, a, rl, ℓ') ∈ A.edges ∧ r = {x | x ∈ rl}
  inv := A.inv

/-- The interpreted edge relation is list membership with a list-backed reset set. -/
@[simp] theorem edge_iff (A : FinAutomaton Loc Act C) (ℓ : Loc) (g : ClockConstraint C)
    (a : Act) (r : Set C) (ℓ' : Loc) :
    A.toTimedAutomaton.edge ℓ g a r ℓ' ↔
      ∃ rl : List C, (ℓ, g, a, rl, ℓ') ∈ A.edges ∧ r = {x | x ∈ rl} := Iff.rfl

/-- The interpreted invariants are the automaton's invariants. -/
@[simp] theorem inv_eq (A : FinAutomaton Loc Act C) (ℓ : Loc) :
    A.toTimedAutomaton.inv ℓ = A.inv ℓ := rfl

/-- The interpreted initial location is the automaton's initial location. -/
@[simp] theorem initial_eq (A : FinAutomaton Loc Act C) :
    A.toTimedAutomaton.initial = A.initial := rfl

/-- A list member is below the list's `max`-fold (with base `0`). -/
private theorem mem_le_foldr_max {n : ℕ} : ∀ {l : List ℕ}, n ∈ l → n ≤ l.foldr max 0
  | [], h => absurd h (by simp)
  | a :: t, h => by
      rcases List.mem_cons.mp h with rfl | ht
      · exact le_max_left _ _
      · exact le_trans (mem_le_foldr_max ht) (le_max_right _ _)

/-- The constructive clamp of a finite automaton: per clock `x`, the maximum constant
appearing in any edge guard or location invariant (via `ClockConstraint.bound`). -/
def cmax [Fintype Loc] (A : FinAutomaton Loc Act C) : C → ℕ := fun x =>
  max ((A.edges.map (fun e => e.2.1.bound x)).foldr max 0)
      (Finset.univ.sup (fun ℓ => (A.inv ℓ).bound x))

/-- The interpretation of a finite automaton is well-formed for its constructive clamp:
every guard and invariant is bounded by `cmax`. -/
theorem wellFormed [Fintype Loc] (A : FinAutomaton Loc Act C) :
    A.toTimedAutomaton.WellFormed A.cmax := by
  refine ⟨?_, ?_⟩
  · rintro ℓ g a r ℓ' ⟨rl, hmem, rfl⟩
    refine ClockConstraint.boundedBy_mono (fun x => ?_) (ClockConstraint.boundedBy_bound g)
    have h1 : g.bound x ≤ (A.edges.map (fun e => e.2.1.bound x)).foldr max 0 :=
      mem_le_foldr_max (List.mem_map.mpr ⟨_, hmem, rfl⟩)
    simp only [cmax]
    exact le_trans h1 (le_max_left _ _)
  · intro ℓ
    refine ClockConstraint.boundedBy_mono (fun x => ?_) (ClockConstraint.boundedBy_bound (A.inv ℓ))
    have h1 : (A.inv ℓ).bound x ≤ Finset.univ.sup (fun ℓ' => (A.inv ℓ').bound x) :=
      Finset.le_sup (f := fun ℓ' => (A.inv ℓ').bound x) (Finset.mem_univ ℓ)
    simp only [cmax]
    exact le_trans h1 (le_max_right _ _)

/-- Smoke test: a 2-location, 1-clock finite automaton with one guarded resetting edge
interprets into a `TimedAutomaton` that is well-formed for its constructive clamp. -/
example : True := by
  let A : FinAutomaton (Fin 2) Unit (Fin 1) :=
    { initial := 0
      edges := [(0, ClockConstraint.atom 0 Cmp.le 1, (), [0], 1)]
      inv := fun _ => ClockConstraint.true_ }
  have : A.toTimedAutomaton.WellFormed A.cmax := A.wellFormed
  trivial

end FinAutomaton

end DeepWiki.ReactiveSystems
