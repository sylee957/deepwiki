import DeepWiki.Refine.DependencyRequirements
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Preorder.Finite

/-! # Finite annotation-constraint solving

Annotation-inference constraints receive a denotational semantics and a finite-enumeration solver.
Exact constructor constraints and lower-bound relaxations are represented separately; the solver
returns every componentwise-minimal assignment. -/

namespace DeepWiki.Refine

/-- An assignment gives one relation annotation to every inference variable. -/
abbrev AnnotationAssignment (arity : Nat) := Fin arity → Annotation

/-- Componentwise comparison of finite annotation assignments is decidable. -/
instance {arity : Nat} : DecidableLE (AnnotationAssignment arity) := fun _left _right =>
  Fintype.decidableForallFintype

/-- A constraint-graph node is either an annotation constant or an inference variable. -/
inductive AnnotationNode (arity : Nat) where
  /-- A fixed annotation in the constraint graph. -/
  | constant (annotation : Annotation)
  /-- An annotation chosen by the inference solver. -/
  | variable (index : Fin arity)
  deriving DecidableEq, Repr

/-- Evaluate a constraint-graph node under an annotation assignment. -/
def AnnotationNode.evaluate {arity : Nat} (assignment : AnnotationAssignment arity) :
    AnnotationNode arity → Annotation
  | .constant annotation => annotation
  | .variable index => assignment index

/-- Exact calculus constraints and their lower-bound graph-reduction counterparts. -/
inductive AnnotationConstraint (arity : Nat) where
  /-- An order edge requires the lower node to lie below the upper node. -/
  | order (lower upper : AnnotationNode arity)
  /-- A universe edge records membership in the `D_□` locus. -/
  | universe (source target : AnnotationNode arity)
  /-- The calculus requires exact arrow-constructor dependencies. -/
  | arrow (output domain codomain : AnnotationNode arity)
  /-- The calculus requires exact dependent-product dependencies. -/
  | product (output domain codomain : AnnotationNode arity)
  /-- Relaxed arrow dependencies impose componentwise lower bounds. -/
  | arrowLower (output domain codomain : AnnotationNode arity)
  /-- Relaxed dependent-product dependencies impose componentwise lower bounds. -/
  | productLower (output domain codomain : AnnotationNode arity)
  /-- A registered constant selects one finite output/input annotation row. -/
  | registeredConstant (output : AnnotationNode arity) (inputs : List (AnnotationNode arity))
      (rows : List (Annotation × List Annotation))
  deriving DecidableEq, Repr

/-- A constraint holds when its nodes satisfy the corresponding annotation rule. -/
def AnnotationConstraint.Holds {arity : Nat}
    (assignment : AnnotationAssignment arity) : AnnotationConstraint arity → Prop
  | .order lower upper => lower.evaluate assignment ≤ upper.evaluate assignment
  | .universe source target =>
      AdmissibleUniverseTranslation (source.evaluate assignment) (target.evaluate assignment)
  | .arrow output domain codomain =>
      arrowRequirements (output.evaluate assignment) =
        (domain.evaluate assignment, codomain.evaluate assignment)
  | .product output domain codomain =>
      dependentProductRequirements (output.evaluate assignment) =
        (domain.evaluate assignment, codomain.evaluate assignment)
  | .arrowLower output domain codomain =>
      (arrowRequirements (output.evaluate assignment)).1 ≤ domain.evaluate assignment ∧
        (arrowRequirements (output.evaluate assignment)).2 ≤ codomain.evaluate assignment
  | .productLower output domain codomain =>
      (dependentProductRequirements (output.evaluate assignment)).1 ≤ domain.evaluate assignment ∧
        (dependentProductRequirements (output.evaluate assignment)).2 ≤ codomain.evaluate assignment
  | .registeredConstant output inputs rows =>
      rows.any (fun row => decide
        (output.evaluate assignment = row.1 ∧
          inputs.map (fun input => input.evaluate assignment) = row.2)) = true

/-- A registered-constant constraint holds exactly when one table row matches all nodes. -/
@[simp] theorem AnnotationConstraint.holds_registeredConstant_iff {arity : Nat}
    (assignment : AnnotationAssignment arity) (output : AnnotationNode arity)
    (inputs : List (AnnotationNode arity)) (rows : List (Annotation × List Annotation)) :
    (AnnotationConstraint.registeredConstant output inputs rows).Holds assignment ↔
      ∃ row ∈ rows,
        output.evaluate assignment = row.1 ∧
          inputs.map (fun input => input.evaluate assignment) = row.2 := by
  simp [AnnotationConstraint.Holds, List.any_eq_true]

/-- Holding of a finite annotation constraint is decidable. -/
instance {arity : Nat} (assignment : AnnotationAssignment arity)
    (constraint : AnnotationConstraint arity) : Decidable (constraint.Holds assignment) := by
  cases constraint <;> simp only [AnnotationConstraint.Holds] <;> infer_instance

/-- Replace exact constructor equalities by componentwise lower bounds. -/
def AnnotationConstraint.relaxToLowerBounds {arity : Nat} :
    AnnotationConstraint arity → AnnotationConstraint arity
  | .arrow output domain codomain => .arrowLower output domain codomain
  | .product output domain codomain => .productLower output domain codomain
  | constraint => constraint

/-- Every exact constructor constraint satisfies its lower-bound relaxation. -/
theorem AnnotationConstraint.Holds.relaxToLowerBounds {arity : Nat}
    {assignment : AnnotationAssignment arity}
    {constraint : AnnotationConstraint arity}
    (holds : constraint.Holds assignment) :
    constraint.relaxToLowerBounds.Holds assignment := by
  cases constraint <;>
    simp_all [AnnotationConstraint.relaxToLowerBounds, AnnotationConstraint.Holds]

/-- A finite annotation-constraint problem is a list of constraint-graph edges. -/
abbrev AnnotationConstraintSystem (arity : Nat) := List (AnnotationConstraint arity)

/-- An assignment satisfies a system when it satisfies every generated constraint. -/
def AnnotationConstraintSystem.Satisfies {arity : Nat}
    (system : AnnotationConstraintSystem arity)
    (assignment : AnnotationAssignment arity) : Prop :=
  system.Forall fun constraint => constraint.Holds assignment

/-- Relax every exact constructor constraint to componentwise lower bounds. -/
def AnnotationConstraintSystem.relaxToLowerBounds {arity : Nat}
    (system : AnnotationConstraintSystem arity) : AnnotationConstraintSystem arity :=
  system.map AnnotationConstraint.relaxToLowerBounds

/-- Exact system satisfaction implies satisfaction after lower-bound relaxation. -/
theorem AnnotationConstraintSystem.Satisfies.relaxToLowerBounds {arity : Nat}
    {system : AnnotationConstraintSystem arity}
    {assignment : AnnotationAssignment arity}
    (satisfies : system.Satisfies assignment) :
    system.relaxToLowerBounds.Satisfies assignment := by
  induction system with
  | nil => simp [AnnotationConstraintSystem.relaxToLowerBounds,
      AnnotationConstraintSystem.Satisfies]
  | cons constraint rest ih =>
      simp only [AnnotationConstraintSystem.relaxToLowerBounds, List.map_cons,
        AnnotationConstraintSystem.Satisfies, List.forall_cons] at satisfies ⊢
      exact ⟨satisfies.1.relaxToLowerBounds, ih satisfies.2⟩

/-- Satisfaction of a finite annotation-constraint system is decidable. -/
instance {arity : Nat} (system : AnnotationConstraintSystem arity)
    (assignment : AnnotationAssignment arity) : Decidable (system.Satisfies assignment) := by
  unfold AnnotationConstraintSystem.Satisfies
  infer_instance

/-- All satisfying assignments, computed by exhaustive finite-domain search. -/
def AnnotationConstraintSystem.solutions {arity : Nat}
    (system : AnnotationConstraintSystem arity) : Finset (AnnotationAssignment arity) :=
  Finset.univ.filter system.Satisfies

/-- Membership in `solutions` is exactly satisfaction of the constraint system. -/
@[simp] theorem AnnotationConstraintSystem.mem_solutions_iff {arity : Nat}
    {system : AnnotationConstraintSystem arity}
    {assignment : AnnotationAssignment arity} :
    assignment ∈ system.solutions ↔ system.Satisfies assignment := by
  simp [AnnotationConstraintSystem.solutions]

/-- A solution is Pareto-minimal in the componentwise annotation order. -/
def AnnotationConstraintSystem.IsMinimalSolution {arity : Nat}
    (system : AnnotationConstraintSystem arity)
    (assignment : AnnotationAssignment arity) : Prop :=
  Minimal system.Satisfies assignment

/-- A least solution satisfies the system below every other satisfying assignment. -/
def AnnotationConstraintSystem.IsLeastSolution {arity : Nat}
    (system : AnnotationConstraintSystem arity)
    (assignment : AnnotationAssignment arity) : Prop :=
  system.Satisfies assignment ∧
    ∀ candidate, system.Satisfies candidate → assignment ≤ candidate

/-- Pareto-minimality of a finite annotation assignment is decidable. -/
instance {arity : Nat} (system : AnnotationConstraintSystem arity)
    (assignment : AnnotationAssignment arity) :
    Decidable (system.IsMinimalSolution assignment) := by
  letI : Decidable
      (∀ candidate : AnnotationAssignment arity,
        system.Satisfies candidate → candidate ≤ assignment → assignment ≤ candidate) :=
    Fintype.decidableForallFintype
  apply decidable_of_iff
    (system.Satisfies assignment ∧
      ∀ candidate : AnnotationAssignment arity,
        system.Satisfies candidate → candidate ≤ assignment → assignment ≤ candidate)
  rfl

/-- Least-solution status for a finite annotation system is decidable. -/
instance {arity : Nat} (system : AnnotationConstraintSystem arity)
    (assignment : AnnotationAssignment arity) :
    Decidable (system.IsLeastSolution assignment) := by
  unfold AnnotationConstraintSystem.IsLeastSolution
  letI : Decidable
      (∀ candidate : AnnotationAssignment arity,
        system.Satisfies candidate → assignment ≤ candidate) :=
    Fintype.decidableForallFintype
  infer_instance

/-- Every least satisfying assignment is Pareto-minimal. -/
theorem AnnotationConstraintSystem.IsLeastSolution.isMinimalSolution {arity : Nat}
    {system : AnnotationConstraintSystem arity}
    {assignment : AnnotationAssignment arity}
    (least : system.IsLeastSolution assignment) :
    system.IsMinimalSolution assignment := by
  refine ⟨least.1, ?_⟩
  intro candidate candidateSatisfies _
  exact least.2 candidate candidateSatisfies

/-- A Pareto-minimal solution equals any least solution. -/
theorem AnnotationConstraintSystem.IsMinimalSolution.eq_of_isLeastSolution {arity : Nat}
    {system : AnnotationConstraintSystem arity}
    {least candidate : AnnotationAssignment arity}
    (minimal : system.IsMinimalSolution candidate)
    (leastSolution : system.IsLeastSolution least) :
    candidate = least := by
  have leastLe : least ≤ candidate := leastSolution.2 candidate minimal.1
  have candidateLe : candidate ≤ least := minimal.2 (y := least) leastSolution.1 leastLe
  exact le_antisymm candidateLe leastLe

/-- Every componentwise-minimal satisfying assignment, computed by finite search. -/
def AnnotationConstraintSystem.minimalSolutions {arity : Nat}
    (system : AnnotationConstraintSystem arity) : Finset (AnnotationAssignment arity) :=
  Finset.univ.filter system.IsMinimalSolution

/-- Membership in `minimalSolutions` is exactly Pareto-minimal satisfaction. -/
@[simp] theorem AnnotationConstraintSystem.mem_minimalSolutions_iff {arity : Nat}
    {system : AnnotationConstraintSystem arity}
    {assignment : AnnotationAssignment arity} :
    assignment ∈ system.minimalSolutions ↔ system.IsMinimalSolution assignment := by
  simp [AnnotationConstraintSystem.minimalSolutions]

/-- Every assignment returned by the minimal solver satisfies the original constraints. -/
theorem AnnotationConstraintSystem.minimalSolutions_sound {arity : Nat}
    {system : AnnotationConstraintSystem arity}
    {assignment : AnnotationAssignment arity}
    (member : assignment ∈ system.minimalSolutions) :
    system.Satisfies assignment :=
  (AnnotationConstraintSystem.mem_minimalSolutions_iff.mp member).1

/-- Every satisfiable finite constraint system has a componentwise-minimal solution. -/
theorem AnnotationConstraintSystem.minimalSolutions_nonempty_of_satisfiable {arity : Nat}
    {system : AnnotationConstraintSystem arity}
    (satisfiable : ∃ assignment, system.Satisfies assignment) :
    system.minimalSolutions.Nonempty := by
  obtain ⟨assignment, satisfies⟩ := satisfiable
  obtain ⟨minimal, _, minimality⟩ := Finite.exists_le_minimal satisfies
  exact ⟨minimal, AnnotationConstraintSystem.mem_minimalSolutions_iff.mpr minimality⟩

/-- The minimal solver returns an assignment exactly when the system is satisfiable. -/
theorem AnnotationConstraintSystem.minimalSolutions_nonempty_iff {arity : Nat}
    {system : AnnotationConstraintSystem arity} :
    system.minimalSolutions.Nonempty ↔ ∃ assignment, system.Satisfies assignment := by
  constructor
  · rintro ⟨assignment, member⟩
    exact ⟨assignment, system.minimalSolutions_sound member⟩
  · exact system.minimalSolutions_nonempty_of_satisfiable

/-- If a pointwise least solution exists, the minimal solver returns only it. -/
theorem AnnotationConstraintSystem.minimalSolutions_eq_singleton_of_isLeastSolution {arity : Nat}
    {system : AnnotationConstraintSystem arity}
    {assignment : AnnotationAssignment arity}
    (least : system.IsLeastSolution assignment) :
    system.minimalSolutions = {assignment} := by
  ext candidate
  simp only [AnnotationConstraintSystem.mem_minimalSolutions_iff, Finset.mem_singleton]
  constructor
  · intro minimal
    exact minimal.eq_of_isLeastSolution least
  · rintro rfl
    exact least.isMinimalSolution

/-- Arrow lower-bound propagation is strictly weaker than the exact dependency equation. -/
theorem arrowLowerRelaxation_strict :
    let assignment : AnnotationAssignment 0 := fun index => Fin.elim0 index
    let bare : Annotation := ⟨.zero, .zero⟩
    let output := AnnotationNode.constant (arity := 0) bare
    let domain := AnnotationNode.constant (arity := 0) Annotation.function
    let codomain := AnnotationNode.constant (arity := 0) bare
    (AnnotationConstraint.arrowLower output domain codomain).Holds assignment ∧
      ¬ (AnnotationConstraint.arrow output domain codomain).Holds assignment := by
  decide

example {arity : Nat} {system : AnnotationConstraintSystem arity}
    {assignment : AnnotationAssignment arity} :
    assignment ∈ system.solutions ↔ system.Satisfies assignment :=
  AnnotationConstraintSystem.mem_solutions_iff

example {arity : Nat} {system : AnnotationConstraintSystem arity} :
    system.minimalSolutions.Nonempty ↔ ∃ assignment, system.Satisfies assignment :=
  AnnotationConstraintSystem.minimalSolutions_nonempty_iff

example {arity : Nat} {system : AnnotationConstraintSystem arity}
    {assignment : AnnotationAssignment arity}
    (least : system.IsLeastSolution assignment) :
    system.minimalSolutions = {assignment} :=
  AnnotationConstraintSystem.minimalSolutions_eq_singleton_of_isLeastSolution least

example :
    (fun _ : Fin 1 => Annotation.function) ∈
      AnnotationConstraintSystem.minimalSolutions
        ([.order (.constant Annotation.function) (.variable 0)] :
          AnnotationConstraintSystem 1) := by
  decide

end DeepWiki.Refine
