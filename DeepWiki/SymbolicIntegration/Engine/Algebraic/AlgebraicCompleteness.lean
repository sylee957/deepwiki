import DeepWiki.SymbolicIntegration.AlgebraicCompleteness
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalWellFounded
import DeepWiki.SymbolicIntegration.Engine.Algebraic.TorsionLogTerm
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogSoundness

/-! # Computable algebraic integrator completeness residuals

Torsion-decision witnesses and residual interfaces for the simple-radical algebraic integration
completeness direction. -/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.AlgebraicCompleteness

/-! ## Torsion-decision witnesses -/

section Witnesses

open DeepWiki.SymbolicIntegration

/-- The engine rejects the infinite-order witness `(3,5)` on `y² = x³ - 2`. -/
theorem engine_none_of_nonTorsion_witness :
    isTorsionDivisor 5 hypRhoX3m2 1 hypPt35 = none
    ∧ elementarityViaTorsion 5 hypRhoX3m2 1 hypPt35 = false
    ∧ (torsionLogTerm 5 tltRhoX3m2 hypRhoX3m2 1 hypPt35).isNone = true := by native_decide

/-- The engine accepts the order-3 flex `(0,1)` on `y² = x³ + 1`. -/
theorem engine_some_of_torsion_witness :
    isTorsionDivisor 5 hypRhoX3p1 1 hypPt01 = some 3
    ∧ elementarityViaTorsion 5 hypRhoX3p1 1 hypPt01 = true
    ∧ (torsionLogTerm 5 tltRhoX3p1 hypRhoX3p1 1 hypPt01).isSome = true := by native_decide

end Witnesses

/-! ## Divisor-torsion residual interface -/

section TorsionFrontier

open DeepWiki.SymbolicIntegration

/-- `DivisorTorsionDecisionFrontier isTorsion` relates `elementarityViaTorsion` to `isTorsion`. -/
def DivisorTorsionDecisionFrontier
    (isTorsion : DensePoly.MumfordDivisor ℚ → Prop) : Prop :=
  ∀ (ρq : DensePoly ℚ) (g : ℕ) (D : DensePoly.MumfordDivisor ℚ),
    ∃ (p : ℕ) (_ : Fact p.Prime),
      (elementarityViaTorsion p ρq g D = true ↔ isTorsion D)

/-- `elementarityViaTorsion p ρq g D = true` iff `isTorsionDivisor` returns `some m`. -/
theorem elementarityViaTorsion_iff_some (p : ℕ) [Fact p.Prime]
    (ρq : DensePoly ℚ) (g : ℕ) (D : DensePoly.MumfordDivisor ℚ) :
    elementarityViaTorsion p ρq g D = true
      ↔ ∃ m, isTorsionDivisor p ρq g D = some m := by
  unfold elementarityViaTorsion
  rw [Option.isSome_iff_exists]

/-- `(torsionLogTerm p ρ ρq g D).isSome = true` iff `isTorsionDivisor` returns `some m`. -/
theorem torsionLogTerm_isSome_iff (p : ℕ) [Fact p.Prime]
    (ρ : DenseFrac ℚ) (ρq : DensePoly ℚ) (g : ℕ) (D : DensePoly.MumfordDivisor ℚ) :
    (torsionLogTerm p ρ ρq g D).isSome = true
      ↔ ∃ m, isTorsionDivisor p ρq g D = some m := by
  unfold torsionLogTerm
  cases h : isTorsionDivisor p ρq g D with
  | none => simp
  | some m => simp

end TorsionFrontier

/-! ## Completeness residuals -/

section Assembly

open DeepWiki.SymbolicIntegration

variable (ρ : DenseFrac ℚ) (ρq : DensePoly ℚ) (g : ℕ) (D : DensePoly.MumfordDivisor ℚ)

/-- `AlgebraicCompletenessResidual` bundles torsion detection and the elementarity criterion. -/
structure AlgebraicCompletenessResidual (p : ℕ) [Fact p.Prime]
    (isTorsion : Prop) (elem : Prop) : Prop where
  /-- Torsion detection agrees with the abstract torsion predicate. -/
  htorsion : (∃ m, isTorsionDivisor p ρq g D = some m) ↔ isTorsion
  /-- Abstract torsion agrees with elementarity. -/
  hcriterion : isTorsion ↔ elem

/-- Under `AlgebraicCompletenessResidual`, `torsionLogTerm` returns a term iff `elem`. -/
theorem cIntegrateAlgebraicWf_complete_of_residual {isTorsion elem : Prop} (p : ℕ)
    [Fact p.Prime] (hres : AlgebraicCompletenessResidual ρq g D p isTorsion elem) :
    (torsionLogTerm p ρ ρq g D).isSome = true ↔ elem := by
  rw [torsionLogTerm_isSome_iff, hres.htorsion, hres.hcriterion]

/-- Under `AlgebraicCompletenessResidual`, `¬ elem` makes `torsionLogTerm` return `none`. -/
theorem engine_none_of_not_elementary {isTorsion elem : Prop} (p : ℕ) [Fact p.Prime]
    (hres : AlgebraicCompletenessResidual ρq g D p isTorsion elem) (hne : ¬ elem) :
    (torsionLogTerm p ρ ρq g D).isNone = true := by
  rw [Option.isNone_iff_eq_none, ← Option.not_isSome_iff_eq_none, Bool.not_eq_true]
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  exact hne ((cIntegrateAlgebraicWf_complete_of_residual ρ ρq g D p hres).mp hcon)

end Assembly

/-! ## Axiom audit -/


/-! ### Axiom audit -/

#print axioms elementarityViaTorsion_iff_some
#print axioms torsionLogTerm_isSome_iff
#print axioms cIntegrateAlgebraicWf_complete_of_residual
#print axioms engine_none_of_not_elementary

end DeepWiki.SymbolicIntegration.AlgebraicCompleteness
