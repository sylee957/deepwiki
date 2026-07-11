import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentReconstruct

/-! # Tangent coupled-solver capability

The hypertangent monomial case reduces special integration to a coupled differential system. This module
exposes that executable subproblem behind an operation/law pair without claiming the missing recombination. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- Prop-free executable capability for the tangent coupled differential system over `ℚ(x)[t]`. -/
structure CTangentCoupledSolver where
  /-- Solve the level-`n` tangent system with the supplied coefficient-degree bound. -/
  solve : ℕ → DensePoly ℚ → DensePoly ℚ → List (DensePoly ℚ) → List (DensePoly ℚ) → ℕ →
    Option (List (DensePoly ℚ) × List (DensePoly ℚ))

/-- Denotation-level soundness contract for a tangent coupled solver. -/
class LawfulCTangentCoupledSolver (C : CTangentCoupledSolver) : Prop where
  /-- Every returned pair solves the requested tangent system. -/
  sound : ∀ (dbound : ℕ) (b0 b2 : DensePoly ℚ) (c1 c2 q1 q2 : List (DensePoly ℚ)) (n : ℕ),
    C.solve dbound b0 b2 c1 c2 n = some (q1, q2) → TanSolves b0 b2 n c1 c2 q1 q2

/-- Relative-completeness contract for a tangent coupled solver. -/
class CompleteCTangentCoupledSolver (C : CTangentCoupledSolver) : Prop where
  /-- Any solvable system is found at some finite coefficient-degree bound. -/
  complete : ∀ (b0 b2 : DensePoly ℚ) (c1 c2 : List (DensePoly ℚ)) (n : ℕ),
    (∃ q1 q2, TanSolves b0 b2 n c1 c2 q1 q2) →
      ∃ dbound q1 q2, C.solve dbound b0 b2 c1 c2 n = some (q1, q2)

/-- The existing degree-bounded tangent cancellation algorithm as a coupled-solver capability. -/
def tangentCoupledSolver [CLinearSolve ℚ] : CTangentCoupledSolver where
  solve := cCoupledDECancelTan

/-- The tangent cancellation algorithm realizes the coupled-solver soundness contract. -/
instance instLawfulCTangentCoupledSolver [CLinearSolve ℚ] [LawfulCLinearSolve ℚ] :
    LawfulCTangentCoupledSolver tangentCoupledSolver where
  sound dbound b0 b2 c1 c2 q1 q2 n hrun :=
    DensePoly.reconstruct dbound b0 n b2 c1 c2 q1 q2 hrun

end DeepWiki.SymbolicIntegration
