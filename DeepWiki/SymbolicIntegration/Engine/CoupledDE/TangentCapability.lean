import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentReconstruct
import DeepWiki.SymbolicIntegration.Engine.Assemble

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

/-- Executable data for one tangent coupled-system call. -/
structure TangentCoupledProblem where
  /-- Coefficient-degree search bound. -/
  degreeBound : ℕ
  /-- Diagonal constant coefficient. -/
  diagonal : DensePoly ℚ
  /-- Off-diagonal coefficient. -/
  offDiagonal : DensePoly ℚ
  /-- First coupled right-hand side. -/
  rhs₁ : List (DensePoly ℚ)
  /-- Second coupled right-hand side. -/
  rhs₂ : List (DensePoly ℚ)
  /-- Tangent-system level. -/
  level : ℕ

/-- Prop-free boundary that prepares and reassembles the tangent coupled special problem. -/
structure CTangentSpecialBridge where
  /-- Translate a canonical special fraction into a coupled problem. -/
  prepare : DensePoly (DenseFrac ℚ) → DensePoly (DenseFrac ℚ) → DensePoly (DenseFrac ℚ) →
    DensePoly (DenseFrac ℚ) → Option TangentCoupledProblem
  /-- Reassemble a coupled solution as the represented special antiderivative. -/
  reassemble : TangentCoupledProblem → List (DensePoly ℚ) → List (DensePoly ℚ) →
    DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)

/-- Semantic reconstruction contract for the missing tangent special bridge. -/
class LawfulCTangentSpecialBridge (B : CTangentSpecialBridge) : Prop where
  /-- Preparing, solving, and reassembling yields the required special-part identity. -/
  sound : ∀ (Dt fp b ds : DensePoly (DenseFrac ℚ)) (p : TangentCoupledProblem)
      (q₁ q₂ : List (DensePoly ℚ)),
    B.prepare Dt fp b ds = some p →
    TanSolves p.diagonal p.offDiagonal p.level p.rhs₁ p.rhs₂ q₁ q₂ →
    let out := B.reassemble p q₁ q₂
    CPoly.toPoly out.2 ≠ 0 ∧
      towerFractionFieldDerivP Dt (fieldFracP out.1 out.2) =
        fieldFracP fp CPoly.one + fieldFracP b ds

/-- Compose a tangent coupled solver and special bridge into a monomial-case operation. -/
def tangentMonomialCase (S : CTangentCoupledSolver) (B : CTangentSpecialBridge) :
    CMonomialCase DensePoly (DenseFrac ℚ) where
  integrateSpecial Dt fp b ds := do
    let p ← B.prepare Dt fp b ds
    let (q₁, q₂) ← S.solve p.degreeBound p.diagonal p.offDiagonal p.rhs₁ p.rhs₂ p.level
    some (B.reassemble p q₁ q₂)
  postprocessNormal _ before := some before

/-- Lawful coupled solving and reconstruction make the composed tangent monomial case lawful. -/
instance instLawfulCMonomialCaseTangent (S : CTangentCoupledSolver) (B : CTangentSpecialBridge)
    [LawfulCTangentCoupledSolver S] [LawfulCTangentSpecialBridge B] :
    LawfulCMonomialCase (tangentMonomialCase S B) where
  special_sound Dt fp b ds snum sden hrun := by
    simp only [tangentMonomialCase] at hrun
    rcases hprepare : B.prepare Dt fp b ds with _ | p
    · simp [hprepare] at hrun
    · rw [hprepare] at hrun
      change (S.solve p.degreeBound p.diagonal p.offDiagonal p.rhs₁ p.rhs₂ p.level).bind
        (fun q => some (B.reassemble p q.1 q.2)) = some (snum, sden) at hrun
      rcases hsolve : S.solve p.degreeBound p.diagonal p.offDiagonal p.rhs₁ p.rhs₂ p.level with
        _ | ⟨q₁, q₂⟩
      · simp [hsolve] at hrun
      · simp only [hsolve, Option.bind_some, Option.some.injEq] at hrun
        have hnum : (B.reassemble p q₁ q₂).1 = snum := congrArg Prod.fst hrun
        have hden : (B.reassemble p q₁ q₂).2 = sden := congrArg Prod.snd hrun
        rw [← hnum, ← hden]
        exact LawfulCTangentSpecialBridge.sound Dt fp b ds p q₁ q₂ hprepare
          (LawfulCTangentCoupledSolver.sound p.degreeBound p.diagonal p.offDiagonal
            p.rhs₁ p.rhs₂ q₁ q₂ p.level hsolve)
  postprocessNormal_sound _ _ _ before after hbefore hrun := by
    change some before = some after at hrun
    have heq : before = after := Option.some.inj hrun
    subst after
    exact hbefore
  postprocessNormal_den_nonzero _ before after hden hrun := by
    change some before = some after at hrun
    have heq : before = after := Option.some.inj hrun
    subst after
    exact hden

end DeepWiki.SymbolicIntegration
