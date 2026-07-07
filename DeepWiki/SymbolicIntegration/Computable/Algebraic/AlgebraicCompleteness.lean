import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalWellFounded
import DeepWiki.SymbolicIntegration.Computable.Algebraic.TorsionLogTerm
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalLogSoundness
import Mathlib.FieldTheory.Differential.Liouville

/-! # Completeness of the algebraic integrator

Liouville-form predicates, descent lemmas, torsion-decision witnesses, and residual interfaces for
the simple-radical algebraic integration completeness direction. -/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.AlgebraicCompleteness

/-! ## Algebraic-elementary predicates -/

section Predicate

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- `IsAlgebraicElementary F K f` gives a Liouville form for `f` over `K`. -/
def IsAlgebraicElementary (f : F) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → K) (v : K),
    (algebraMap F K f) = ∑ x, (algebraMap F K (c x)) * logDeriv (u x) + v′

end Predicate

/-! ## Finite-dimensional descent -/

section FiniteDimDescent

variable (F : Type*) (K : Type*) [Field F] [Field K] [CharZero F]
variable [Differential F] [Differential K] [Algebra F K] [DifferentialAlgebra F K]

/-- Elementary over a finite-dimensional extension `K / F` descends to `F`. -/
theorem elementary_base_of_elementary_finiteDim [FiniteDimensional F K] (f : F)
    (h : IsAlgebraicElementary F K f) : IsAlgebraicElementary F F f := by
  haveI : IsLiouville F K := isLiouville_of_finiteDimensional
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := h
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville f ι c hc u v hrep
  exact ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-- Base non-elementarity propagates up a finite-dimensional extension `K / F`. -/
theorem not_elementary_extension_of_not_elementary_base_alg [FiniteDimensional F K] (f : F)
    (h : ¬ IsAlgebraicElementary F F f) : ¬ IsAlgebraicElementary F K f :=
  fun hK => h (elementary_base_of_elementary_finiteDim F K f hK)

end FiniteDimDescent

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

/-! ## Liouville and rational-part residual interfaces -/

section Frontier

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- `AlgebraicLiouvilleFrontier F` propagates base non-elementarity through Liouville extensions. -/
def AlgebraicLiouvilleFrontier : Prop :=
  ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K] [IsLiouville F K]
    (f : F), ¬ IsAlgebraicElementary F F f → ¬ IsAlgebraicElementary F K f

omit [CharZero F] in
/-- `AlgebraicLiouvilleFrontier F` holds for each supplied Liouville extension. -/
theorem algebraicLiouville_single_extension : AlgebraicLiouvilleFrontier F := by
  intro K _ _ _ _ _ f h hK
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := hK
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville f ι c hc u v hrep
  exact h ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-! ### Rational parts -/

omit [CharZero F] in
/-- The derivative `v′` is algebraic-elementary via the empty logarithmic family. -/
theorem ratPart_isAlgebraicElementary (v : F) : IsAlgebraicElementary F F (v′) := by
  refine ⟨Empty, inferInstance, Empty.elim, fun x => x.elim, Empty.elim, v, ?_⟩
  simp only [Algebra.algebraMap_self_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_add]

/-- `RationalPartExhaustivenessFrontier F` reduces `f - v′` to a purely logarithmic form. -/
def RationalPartExhaustivenessFrontier : Prop :=
  ∀ (f v : F), IsAlgebraicElementary F F f →
    IsAlgebraicElementary F F (f - v′) →
      ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → F),
        (f - v′) = ∑ x, c x * logDeriv (u x)

end Frontier

/-! ## Divisor-torsion residual interface -/

section TorsionFrontier

open DeepWiki.SymbolicIntegration

/-- `DivisorTorsionDecisionFrontier isTorsion` relates `elementarityViaTorsion` to `isTorsion`. -/
def DivisorTorsionDecisionFrontier
    (isTorsion : CPolyG.MumfordDivisor ℚ → Prop) : Prop :=
  ∀ (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ),
    ∃ (p : ℕ) (_ : Fact p.Prime),
      (elementarityViaTorsion p ρq g D = true ↔ isTorsion D)

/-- `elementarityViaTorsion p ρq g D = true` iff `isTorsionDivisor` returns `some m`. -/
theorem elementarityViaTorsion_iff_some (p : ℕ) [Fact p.Prime]
    (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ) :
    elementarityViaTorsion p ρq g D = true
      ↔ ∃ m, isTorsionDivisor p ρq g D = some m := by
  unfold elementarityViaTorsion
  rw [Option.isSome_iff_exists]

/-- `(torsionLogTerm p ρ ρq g D).isSome = true` iff `isTorsionDivisor` returns `some m`. -/
theorem torsionLogTerm_isSome_iff (p : ℕ) [Fact p.Prime]
    (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ) :
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

variable (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ)

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

/-! ## Restatements and axiom audit -/

/-! ### Restatements (anonymous `example`s) -/

section Restatements

open DeepWiki.SymbolicIntegration

-- The within-tower algebraic descent: elementary over a finite algebraic extension descends to the base.
example (F K : Type*) [Field F] [Field K] [CharZero F] [Differential F] [Differential K] [Algebra F K]
    [DifferentialAlgebra F K] [FiniteDimensional F K] (f : F) (h : IsAlgebraicElementary F K f) :
    IsAlgebraicElementary F F f :=
  elementary_base_of_elementary_finiteDim F K f h

-- ★ The decision-procedure equivalence: the engine emits a log term iff the integrand is elementary,
-- modulo the two named deep frontiers (the Liouville criterion + the good-reduction torsion decision).
example (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ)
    {isTorsion elem : Prop} (p : ℕ) [Fact p.Prime]
    (hres : AlgebraicCompletenessResidual ρq g D p isTorsion elem) :
    (torsionLogTerm p ρ ρq g D).isSome = true ↔ elem :=
  cIntegrateAlgebraicWf_complete_of_residual ρ ρq g D p hres

-- ★ The headline "none ⟹ not elementary" for the algebraic integrator's log part, modulo the frontiers.
example (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ)
    {isTorsion elem : Prop} (p : ℕ) [Fact p.Prime]
    (hres : AlgebraicCompletenessResidual ρq g D p isTorsion elem) (hne : ¬ elem) :
    (torsionLogTerm p ρ ρq g D).isNone = true :=
  engine_none_of_not_elementary ρ ρq g D p hres hne

end Restatements

/-! ### Axiom audit -/

#print axioms elementary_base_of_elementary_finiteDim
#print axioms not_elementary_extension_of_not_elementary_base_alg
#print axioms ratPart_isAlgebraicElementary
#print axioms algebraicLiouville_single_extension
#print axioms elementarityViaTorsion_iff_some
#print axioms torsionLogTerm_isSome_iff
#print axioms cIntegrateAlgebraicWf_complete_of_residual
#print axioms engine_none_of_not_elementary

end DeepWiki.SymbolicIntegration.AlgebraicCompleteness
