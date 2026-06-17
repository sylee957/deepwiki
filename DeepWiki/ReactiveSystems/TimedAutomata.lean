import DeepWiki.ReactiveSystems.TimedTransitionSystems

/-! # Timed automata
Finite automata extended with real-valued clocks: edges carry a
guard (clock constraint), an action, and a set of clocks to reset; locations
carry invariants. A timed automaton denotes a timed LTS whose states are
location/valuation pairs — action transitions follow a guarded edge (resetting
its clocks), and delay transitions advance every clock while the invariant
holds. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- A comparison operator for clock constraints (`≤, <, =, >, ≥`). -/
inductive Cmp | le | lt | eq | gt | ge

/-- The meaning of a comparison between a clock value and a natural bound. -/
def Cmp.holds : Cmp → ℝ≥0 → ℕ → Prop
  | .le, r, n => r ≤ n
  | .lt, r, n => r < n
  | .eq, r, n => r = n
  | .gt, r, n => r > n
  | .ge, r, n => r ≥ n

/-- Clock constraints / guards over a set of clocks `C`:
`g ::= tt ∣ x ⋈ n ∣ g₁ ∧ g₂`. -/
inductive ClockConstraint (C : Type*)
  | true_ : ClockConstraint C
  | atom : C → Cmp → ℕ → ClockConstraint C
  | and : ClockConstraint C → ClockConstraint C → ClockConstraint C

/-- A clock valuation records the time elapsed since each clock was last reset. -/
abbrev Valuation (C : Type*) := C → ℝ≥0

/-- `v + d`: increase every clock value by the delay `d`. -/
def Valuation.add {C : Type*} (v : Valuation C) (d : ℝ≥0) : Valuation C := fun x => v x + d

/-- `(v + d) x = v x + d` pointwise. -/
@[simp] theorem Valuation.add_apply {C : Type*} (v : Valuation C) (d : ℝ≥0) (x : C) :
    v.add d x = v x + d := rfl

/-- Delaying a valuation by `a` then `b` equals delaying once by `a + b`. -/
theorem Valuation.add_add {C : Type*} (v : Valuation C) (a b : ℝ≥0) :
    (v.add a).add b = v.add (a + b) := by
  funext x; simp only [Valuation.add_apply]; ring

open Classical in
/-- `v[r]`: reset the clocks in `r` to zero, leaving the others unchanged. -/
noncomputable def Valuation.reset {C : Type*} (r : Set C) (v : Valuation C) : Valuation C :=
  fun x => if x ∈ r then 0 else v x

/-- A reset clock reads zero. -/
theorem Valuation.reset_mem {C : Type*} {r : Set C} {x : C} (h : x ∈ r) (v : Valuation C) :
    Valuation.reset r v x = 0 := by unfold Valuation.reset; exact if_pos h

/-- An unreset clock keeps its value. -/
theorem Valuation.reset_not_mem {C : Type*} {r : Set C} {x : C} (h : x ∉ r) (v : Valuation C) :
    Valuation.reset r v x = v x := by unfold Valuation.reset; exact if_neg h

/-- Two single-clock resets commute: `u[y][x] = u[x][y]`. -/
theorem Valuation.reset_comm {C : Type*} (x y : C) (u : Valuation C) :
    Valuation.reset {x} (Valuation.reset {y} u) = Valuation.reset {y} (Valuation.reset {x} u) := by
  funext z
  by_cases hx : z = x <;> by_cases hy : z = y <;>
    simp [Valuation.reset, Set.mem_singleton_iff, hx, hy]

/-- Evaluation of a clock constraint under a valuation. -/
def satisfies {C : Type*} (v : Valuation C) : ClockConstraint C → Prop
  | .true_ => True
  | .atom x c n => c.holds (v x) n
  | .and g₁ g₂ => satisfies v g₁ ∧ satisfies v g₂

/-- Two clock constraints are *equivalent* iff
they are satisfied by exactly the same valuations. -/
def ConstraintEquiv {C : Type*} (g₁ g₂ : ClockConstraint C) : Prop :=
  ∀ v : Valuation C, satisfies v g₁ ↔ satisfies v g₂

/-- Constraint equivalence is an equivalence relation. -/
theorem constraintEquiv_equivalence {C : Type*} : Equivalence (@ConstraintEquiv C) :=
  ⟨fun _ _ => Iff.rfl, fun h v => (h v).symm, fun h₁ h₂ v => (h₁ v).trans (h₂ v)⟩

/-- A constraint satisfied by *every* valuation: `tt`. -/
theorem satisfies_true_all {C : Type*} (v : Valuation C) :
    satisfies v (ClockConstraint.true_ : ClockConstraint C) := trivial

/-- A constraint satisfied by *no* valuation: `x < 0` (impossible over `ℝ≥0`). -/
theorem not_satisfies_lt_zero {C : Type*} (x : C) (v : Valuation C) :
    ¬ satisfies v (ClockConstraint.atom x Cmp.lt 0) := by
  simp [satisfies, Cmp.holds]

/-- A timed automaton over locations `Loc`, actions `Act` and
clocks `C`: an initial location, an edge relation `ℓ —g,a,r→ ℓ'` carrying a
guard, action and reset set, and a location-invariant assignment. -/
structure TimedAutomaton (Loc Act C : Type*) where
  /-- The initial location. -/
  initial : Loc
  /-- The edge relation `(ℓ, g, a, r, ℓ') ∈ E`. -/
  edge : Loc → ClockConstraint C → Act → Set C → Loc → Prop
  /-- The location invariants. -/
  inv : Loc → ClockConstraint C

namespace TimedAutomaton

variable {Loc Act C : Type*}

/-- The timed LTS denoted by a timed automaton: states are
location/valuation pairs; an action transition follows an edge whose guard holds,
resetting its clocks into a state respecting the target invariant; a delay `d`
advances all clocks provided the current location's invariant holds before and
after. -/
noncomputable def tlts (A : TimedAutomaton Loc Act C) : TLTS (Loc × Valuation C) Act where
  step p l q :=
    match l with
    | .inl a => ∃ g r, A.edge p.1 g a r q.1 ∧ satisfies p.2 g ∧
        q.2 = Valuation.reset r p.2 ∧ satisfies q.2 (A.inv q.1)
    | .inr d => q.1 = p.1 ∧ q.2 = p.2.add d ∧
        satisfies p.2 (A.inv p.1) ∧ satisfies (p.2.add d) (A.inv p.1)

/-- Unfolding of the action transitions of `A`'s semantics. -/
theorem tlts_act_iff (A : TimedAutomaton Loc Act C) (ℓ : Loc) (v : Valuation C) (a : Act)
    (ℓ' : Loc) (v' : Valuation C) :
    A.tlts.act (ℓ, v) a (ℓ', v') ↔
      ∃ g r, A.edge ℓ g a r ℓ' ∧ satisfies v g ∧ v' = Valuation.reset r v ∧
        satisfies v' (A.inv ℓ') := Iff.rfl

/-- Unfolding of the delay transitions of `A`'s semantics. -/
theorem tlts_delay_iff (A : TimedAutomaton Loc Act C) (ℓ : Loc) (v : Valuation C) (d : ℝ≥0)
    (ℓ' : Loc) (v' : Valuation C) :
    A.tlts.delay (ℓ, v) d (ℓ', v') ↔
      ℓ' = ℓ ∧ v' = v.add d ∧ satisfies v (A.inv ℓ) ∧ satisfies (v.add d) (A.inv ℓ) := Iff.rfl

/-- Delay transitions of a timed automaton are deterministic (time determinism):
the post-delay state `(ℓ, v + d)` is uniquely determined. -/
theorem timeDeterministic (A : TimedAutomaton Loc Act C) : A.tlts.TimeDeterministic := by
  rintro p d q q' ⟨hℓ, hv, _, _⟩ ⟨hℓ', hv', _, _⟩
  exact Prod.ext (hℓ.trans hℓ'.symm) (hv.trans hv'.symm)

end TimedAutomaton

end DeepWiki.ReactiveSystems
