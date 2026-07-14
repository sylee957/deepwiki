import DeepWiki.Refine.AnnotationConstraintSolver
import DeepWiki.Refine.AnnotationLattice
import Mathlib.Data.List.FinRange

/-! # Acyclic annotation-constraint graph reduction

A precedence graph and reversed-Kahn schedule reduce supported lower-bound constraints by joining
their propagated bounds. Unsupported exact constructor equations, cycles, and failed final checks
remain explicit results. -/

namespace DeepWiki.Refine

namespace AnnotationConstraintGraph

/-- A dependency edge requires its first annotation variable to precede its second. -/
abbrev Dependency (arity : Nat) := Fin arity × Fin arity

/-- A dependency between distinct variable nodes, with constants and self-edges omitted. -/
def nodeDependencyTo {arity : Nat}
    (before after : AnnotationNode arity) : List (Dependency arity) :=
  match before, after with
  | .variable source, .variable target =>
      if source = target then [] else [(source, target)]
  | _, _ => []

/-- Precedence edges for the supported lower-bound constraint fragment. -/
def constraintDependencies {arity : Nat}
    (constraint : AnnotationConstraint arity) : Option (List (Dependency arity)) :=
  match constraint with
  | .order lower upper => some (nodeDependencyTo lower upper)
  | .universe source target => some (nodeDependencyTo target source)
  | .arrow _ _ _ => none
  | .product _ _ _ => none
  | .arrowLower output domain codomain =>
      some (nodeDependencyTo output domain ++ nodeDependencyTo output codomain)
  | .productLower output domain codomain =>
      some (nodeDependencyTo output domain ++ nodeDependencyTo output codomain)
  | .registeredConstant output inputs _ =>
      some (inputs.flatMap fun input => nodeDependencyTo output input)

/-- Collect all precedence edges, failing on exact constructor equations absent from the graph. -/
def dependencies {arity : Nat} :
    AnnotationConstraintSystem arity → Option (List (Dependency arity))
  | [] => some []
  | constraint :: system => do
      let head ← constraintDependencies constraint
      let tail ← dependencies system
      pure (head ++ tail)

/-- Whether an edge from the candidate node exits to another remaining node. -/
def hasOutgoingTo {arity : Nat} (remaining : List (Fin arity))
    (edge : Dependency arity) (node : Fin arity) : Bool :=
  decide (edge.1 = node ∧ edge.2 ∈ remaining)

/-- A node is an exit when none of its dependency successors remains in the graph. -/
def isExit {arity : Nat} (edges : List (Dependency arity))
    (remaining : List (Fin arity)) (node : Fin arity) : Bool :=
  !(edges.any fun edge => hasOutgoingTo remaining edge node)

/-- Fuel-bounded reversed-Kahn reduction, removing one ready node at each successful step. -/
def topologicalOrderAux {arity : Nat} (edges : List (Dependency arity)) :
    Nat → List (Fin arity) → Option (List (Fin arity))
  | 0, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, remaining =>
      match remaining.find? (isExit edges remaining) with
      | none => none
      | some node =>
          match topologicalOrderAux edges fuel (remaining.erase node) with
          | none => none
          | some order => some (order ++ [node])

/-- Compute a precedence order, returning `none` when reversed Kahn gets stuck. -/
def topologicalOrder {arity : Nat}
    (edges : List (Dependency arity)) : Option (List (Fin arity)) :=
  topologicalOrderAux edges (List.finRange arity).length (List.finRange arity)

/-- Operational cycle detection is failure of the reversed-Kahn topological reduction. -/
def HasCycle {arity : Nat} (edges : List (Dependency arity)) : Prop :=
  topologicalOrder edges = none

/-- Attach a lower bound to a variable node exactly when it is the node being instantiated. -/
def nodeBoundAt {arity : Nat} (node : AnnotationNode arity)
    (current : Fin arity) (bound : Annotation) : List Annotation :=
  match node with
  | .constant _ => []
  | .variable index => if index = current then [bound] else []

/-- The first registered-constant input row whose output matches the instantiated output node. -/
def registeredInputRequirements? {arity : Nat} (assignment : AnnotationAssignment arity)
    (output : AnnotationNode arity) (rows : List (Annotation × List Annotation)) :
    Option (List Annotation) :=
  match rows.find? (fun row => decide (output.evaluate assignment = row.1)) with
  | none => none
  | some row => some row.2

/-- Lower bounds contributed by a registered-constant input row at one variable. -/
def registeredInputBoundsAt {arity : Nat} (current : Fin arity) :
    List (AnnotationNode arity) → List Annotation → List Annotation
  | input :: inputs, required :: requirements =>
      nodeBoundAt input current required ++
        registeredInputBoundsAt current inputs requirements
  | _, _ => []

/-- Lower bounds generated for one variable after predecessor variables have been instantiated. -/
def constraintLowerBoundsFor {arity : Nat}
    (assignment : AnnotationAssignment arity) (current : Fin arity) :
    AnnotationConstraint arity → List Annotation
  | .order lower upper =>
      nodeBoundAt upper current (lower.evaluate assignment)
  | .universe source target =>
      if (target.evaluate assignment).IsUniverseWeak then []
      else nodeBoundAt source current ⊤
  | .arrow _ _ _ => []
  | .product _ _ _ => []
  | .arrowLower output domain codomain =>
      let requirements := arrowRequirements (output.evaluate assignment)
      nodeBoundAt domain current requirements.1 ++ nodeBoundAt codomain current requirements.2
  | .productLower output domain codomain =>
      let requirements := dependentProductRequirements (output.evaluate assignment)
      nodeBoundAt domain current requirements.1 ++ nodeBoundAt codomain current requirements.2
  | .registeredConstant output inputs rows =>
      match registeredInputRequirements? assignment output rows with
      | none => []
      | some requirements => registeredInputBoundsAt current inputs requirements

/-- Join every lower bound generated for one variable by a constraint system. -/
def lowerBound {arity : Nat} (system : AnnotationConstraintSystem arity)
    (assignment : AnnotationAssignment arity) (current : Fin arity) : Annotation :=
  (system.flatMap fun constraint => constraintLowerBoundsFor assignment current constraint).foldl
    (fun accumulated bound => accumulated ⊔ bound) ⊥

/-- Instantiate one variable at the least upper bound currently propagated to it. -/
def instantiateOne {arity : Nat} (system : AnnotationConstraintSystem arity)
    (assignment : AnnotationAssignment arity) (current : Fin arity) :
    AnnotationAssignment arity :=
  Function.update assignment current (lowerBound system assignment current)

/-- Instantiate all variables in a proposed precedence order from the bottom assignment. -/
def instantiateInOrder {arity : Nat} (system : AnnotationConstraintSystem arity)
    (order : List (Fin arity)) : AnnotationAssignment arity :=
  order.foldl (instantiateOne system) (fun _ => ⊥)

/-- Observable outcomes of lower-bound graph solving. -/
inductive Result (arity : Nat) where
  /-- The input contains an exact arrow or product equation not represented by the graph. -/
  | unsupported
  /-- Reversed Kahn found no exit before it consumed all dependency nodes. -/
  | cyclic
  /-- The propagated candidate failed an original constraint or an upper-bound check. -/
  | inconsistent (candidate : AnnotationAssignment arity)
  /-- The propagated candidate passed every original constraint. -/
  | solved (assignment : AnnotationAssignment arity)

/-- Read one inferred annotation from a successful graph result. -/
def Result.valueAt? {arity : Nat} (result : Result arity)
    (index : Fin arity) : Option Annotation :=
  match result with
  | .solved assignment => some (assignment index)
  | _ => none

/-- Certify a propagated candidate against the denotational constraint semantics. -/
def certify {arity : Nat} (system : AnnotationConstraintSystem arity)
    (candidate : AnnotationAssignment arity) : Result arity :=
  if system.Satisfies candidate then .solved candidate else .inconsistent candidate

/-- A candidate reported as solved satisfies the original, unmodified constraint system. -/
theorem certify_sound {arity : Nat} {system : AnnotationConstraintSystem arity}
    {candidate assignment : AnnotationAssignment arity}
    (solved : certify system candidate = .solved assignment) :
    system.Satisfies assignment := by
  by_cases satisfies : system.Satisfies candidate
  · simp only [certify, satisfies, if_pos, Result.solved.injEq] at solved
    subst assignment
    exact satisfies
  · simp [certify, satisfies] at solved

/-- Run scheduled lower-bound propagation and certify its candidate before returning it. -/
def solve {arity : Nat} (system : AnnotationConstraintSystem arity) : Result arity :=
  match dependencies system with
  | none => .unsupported
  | some edges =>
      match topologicalOrder edges with
      | none => .cyclic
      | some order => certify system (instantiateInOrder system order)

/-- Every assignment returned by graph reduction satisfies the denotational system semantics. -/
theorem solve_sound {arity : Nat} {system : AnnotationConstraintSystem arity}
    {assignment : AnnotationAssignment arity}
    (solved : solve system = .solved assignment) :
    system.Satisfies assignment := by
  unfold solve at solved
  split at solved
  · contradiction
  · split at solved
    · contradiction
    · exact certify_sound solved

/-- Graph solving refines exhaustive solving: every reported assignment is an enumerated solution. -/
theorem solve_mem_solutions {arity : Nat} {system : AnnotationConstraintSystem arity}
    {assignment : AnnotationAssignment arity}
    (solved : solve system = .solved assignment) :
    assignment ∈ system.solutions :=
  AnnotationConstraintSystem.mem_solutions_iff.mpr (solve_sound solved)

/-- On an acyclic supported system, graph success is exactly certification of its propagated candidate. -/
theorem solve_succeeds_iff_propagated_satisfies {arity : Nat}
    {system : AnnotationConstraintSystem arity} {edges : List (Dependency arity)}
    {order : List (Fin arity)}
    (dependenciesEq : dependencies system = some edges)
    (orderEq : topologicalOrder edges = some order) :
    (∃ assignment, solve system = .solved assignment) ↔
      system.Satisfies (instantiateInOrder system order) := by
  simp only [solve, dependenciesEq, orderEq]
  unfold certify
  by_cases satisfies : system.Satisfies (instantiateInOrder system order)
  · simp [satisfies]
  · simp [satisfies]

/-- Duplicate registered-output rows can make first-match propagation return a nonminimal solution. -/
theorem registeredFirstMatch_can_return_nonminimal :
    let system : AnnotationConstraintSystem 2 :=
      [.order (.constant Annotation.function) (.variable 0),
        .registeredConstant (.variable 0) [.variable 1]
          [(Annotation.function, [Annotation.isomorphism]),
            (Annotation.function, [Annotation.function])]]
    let candidate := instantiateInOrder system [0, 1]
    solve system = .solved candidate ∧
      system.Satisfies candidate ∧ ¬ system.IsMinimalSolution candidate := by
  dsimp only
  constructor
  · rfl
  constructor <;> native_decide

/-- Duplicate registered-output rows can make first-match propagation reject a satisfiable system. -/
theorem registeredFirstMatch_can_reject_satisfiable :
    let system : AnnotationConstraintSystem 2 :=
      [.order (.constant Annotation.function) (.variable 0),
        .registeredConstant (.variable 0) [.variable 1]
          [(Annotation.function, [Annotation.isomorphism]),
            (Annotation.function, [Annotation.function])],
        .registeredConstant (.variable 0) [.variable 1]
          [(Annotation.function, [Annotation.function])]]
    let candidate := instantiateInOrder system [0, 1]
    system.Satisfies (fun _ => Annotation.function) ∧
      solve system = .inconsistent candidate ∧ ¬ system.Satisfies candidate := by
  dsimp only
  constructor
  · native_decide
  constructor
  · rfl
  · native_decide

/-- Graph propagation is not complete even on supported acyclic systems with satisfying assignments. -/
theorem graphSolve_not_complete_on_supported_acyclic_systems :
    ¬ ∀ (arity : Nat) (system : AnnotationConstraintSystem arity)
        (edges : List (Dependency arity)) (order : List (Fin arity)),
      dependencies system = some edges →
      topologicalOrder edges = some order →
      (∃ assignment, system.Satisfies assignment) →
      ∃ assignment, solve system = .solved assignment := by
  intro complete
  let system : AnnotationConstraintSystem 2 :=
    [.order (.constant Annotation.function) (.variable 0),
      .registeredConstant (.variable 0) [.variable 1]
        [(Annotation.function, [Annotation.isomorphism]),
          (Annotation.function, [Annotation.function])],
      .registeredConstant (.variable 0) [.variable 1]
        [(Annotation.function, [Annotation.function])]]
  have dependenciesEq : dependencies system = some [(0, 1), (0, 1)] := by
    rfl
  have orderEq : topologicalOrder (arity := 2) [(0, 1), (0, 1)] = some [0, 1] := by
    rfl
  have satisfiable : ∃ assignment, system.Satisfies assignment :=
    ⟨fun _ => Annotation.function, by native_decide⟩
  obtain ⟨assignment, solved⟩ :=
    complete 2 system [(0, 1), (0, 1)] [0, 1]
      dependenciesEq orderEq satisfiable
  have rejected :
      solve system = .inconsistent (instantiateInOrder system [0, 1]) := by
    rfl
  rw [rejected] at solved
  contradiction

/-- A solved graph assignment need not be Pareto-minimal among denotational solutions. -/
theorem graphSolve_not_always_minimal :
    ¬ ∀ (arity : Nat) (system : AnnotationConstraintSystem arity)
        (assignment : AnnotationAssignment arity),
      solve system = .solved assignment → system.IsMinimalSolution assignment := by
  intro alwaysMinimal
  let system : AnnotationConstraintSystem 2 :=
    [.order (.constant Annotation.function) (.variable 0),
      .registeredConstant (.variable 0) [.variable 1]
        [(Annotation.function, [Annotation.isomorphism]),
          (Annotation.function, [Annotation.function])]]
  let candidate := instantiateInOrder system [0, 1]
  have solved : solve system = .solved candidate := by
    rfl
  have notMinimal : ¬ system.IsMinimalSolution candidate := by
    native_decide
  exact notMinimal (alwaysMinimal 2 system candidate solved)

/-- A registered table does not by itself infer its output annotation from its available rows. -/
theorem registeredOutput_is_not_inferred :
    let system : AnnotationConstraintSystem 1 :=
      [.registeredConstant (.variable 0) [] [(Annotation.function, [])]]
    let candidate := instantiateInOrder system [0]
    dependencies system = some [] ∧ topologicalOrder (arity := 1) [] = some [0] ∧
      system.Satisfies (fun _ => Annotation.function) ∧
        solve system = .inconsistent candidate := by
  dsimp only
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · native_decide
  · rfl

/-- A singleton exact arrow equation is outside the graph solver's supported fragment. -/
theorem solve_singleton_exactArrow_unsupported {arity : Nat}
    (output domain codomain : AnnotationNode arity) :
    solve [.arrow output domain codomain] = .unsupported :=
  rfl

/-- A singleton exact dependent-product equation is outside the graph solver's supported fragment. -/
theorem solve_singleton_exactProduct_unsupported {arity : Nat}
    (output domain codomain : AnnotationNode arity) :
    solve [.product output domain codomain] = .unsupported :=
  rfl

/-- A satisfiable exact arrow equation is unsupported, while its lower-bound relaxation is solved. -/
theorem exactArrow_supportedOnlyAfterRelaxation :
    let exact : AnnotationConstraintSystem 0 :=
      [.arrow (.constant Annotation.function) (.constant ⟨.zero, .one⟩)
        (.constant Annotation.function)]
    let relaxed := exact.relaxToLowerBounds
    let candidate := instantiateInOrder relaxed []
    exact.Satisfies (fun index => Fin.elim0 index) ∧
      solve exact = .unsupported ∧
        solve relaxed = .solved candidate ∧ relaxed.Satisfies candidate := by
  dsimp only
  constructor
  · native_decide
  constructor
  · rfl
  constructor
  · rfl
  · native_decide

example :
    topologicalOrder
      (arity := 2) [(0, 1), (1, 0)] = none := by
  decide

example :
    topologicalOrder
      (arity := 3) [(0, 1), (1, 2)] = some [0, 1, 2] := by
  decide

example :
    match solve
      ([.order (.constant Annotation.function) (.variable 0)] :
        AnnotationConstraintSystem 1) with
    | .solved assignment => assignment 0 = Annotation.function
    | _ => False := by
  rfl

example :
    let result := solve
      ([.order (.constant Annotation.function) (.variable 0),
        .arrowLower (.variable 0) (.variable 1) (.variable 2)] :
        AnnotationConstraintSystem 3)
    result.valueAt? 0 = some Annotation.function ∧
      result.valueAt? 1 = some ⟨.zero, .one⟩ ∧
      result.valueAt? 2 = some Annotation.function := by
  decide

example :
    let result := solve
      ([.order (.constant Annotation.isomorphism) (.variable 1),
        .universe (.variable 0) (.variable 1)] :
        AnnotationConstraintSystem 2)
    result.valueAt? 0 = some Annotation.equivalence ∧
      result.valueAt? 1 = some Annotation.isomorphism := by
  decide

example :
    let result := solve
      ([.order (.constant Annotation.function) (.variable 0),
        .registeredConstant (.variable 0) [.variable 1]
          [(Annotation.function, [Annotation.isomorphism])]] :
        AnnotationConstraintSystem 2)
    result.valueAt? 0 = some Annotation.function ∧
      result.valueAt? 1 = some Annotation.isomorphism := by
  decide

example {arity : Nat} {system : AnnotationConstraintSystem arity}
    {assignment : AnnotationAssignment arity}
    (solved : solve system = .solved assignment) :
    system.Satisfies assignment :=
  solve_sound solved

end AnnotationConstraintGraph

end DeepWiki.Refine
