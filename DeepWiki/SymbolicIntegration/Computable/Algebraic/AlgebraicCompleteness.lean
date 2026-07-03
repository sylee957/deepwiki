import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalWellFounded
import DeepWiki.SymbolicIntegration.Computable.Algebraic.TorsionLogTerm
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalLogSoundness
import Mathlib.FieldTheory.Differential.Liouville

/-! # Completeness of the algebraic integrator: the "`none` ⟹ not elementary" direction

The converse of soundness for the simple-radical algebraic integrator `cIntegrateAlgebraicWf`
(over `y² = ρ`): no log argument plus a non-torsion residue divisor means no elementary
antiderivative. Assembles the within-tower descent (from Mathlib's `isLiouville_of_finiteDimensional`)
and reduces full completeness to two named `def` frontiers — the Liouville structure theorem for the
curve's function field and the good-reduction divisor-torsion decision correctness. -/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.AlgebraicCompleteness

/-! ## The algebraic-elementary predicate (Liouville form over a differential field `K`) -/

section Predicate

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- The algebraic-elementary predicate `IsAlgebraicElementary F K f`: `f ∈ F` has an elementary
antiderivative of Liouville form over `K` — `↑f = ∑ᵢ ↑cᵢ · logDeriv uᵢ + v′` with constants
`cᵢ ∈ F`, arguments `uᵢ ∈ K`, and `v ∈ K`. -/
def IsAlgebraicElementary (f : F) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → K) (v : K),
    (algebraMap F K f) = ∑ x, (algebraMap F K (c x)) * logDeriv (u x) + v′

end Predicate

/-! ## The within-tower algebraic descent (via Mathlib's `isLiouville_of_finiteDimensional`) -/

section FiniteDimDescent

variable (F : Type*) (K : Type*) [Field F] [Field K] [CharZero F]
variable [Differential F] [Differential K] [Algebra F K] [DifferentialAlgebra F K]

/-- Elementary over a finite-dimensional algebraic extension `K / F` (`CharZero F`) descends to
elementary over the base `F`. Rides `isLiouville_of_finiteDimensional`. -/
theorem elementary_base_of_elementary_finiteDim [FiniteDimensional F K] (f : F)
    (h : IsAlgebraicElementary F K f) : IsAlgebraicElementary F F f := by
  haveI : IsLiouville F K := isLiouville_of_finiteDimensional
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := h
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville f ι c hc u v hrep
  exact ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-- Non-elementarity over the base `F` propagates up a finite-dimensional algebraic extension `K / F`
(contrapositive of `elementary_base_of_elementary_finiteDim`). -/
theorem not_elementary_extension_of_not_elementary_base_alg [FiniteDimensional F K] (f : F)
    (h : ¬ IsAlgebraicElementary F F f) : ¬ IsAlgebraicElementary F K f :=
  fun hK => h (elementary_base_of_elementary_finiteDim F K f hK)

end FiniteDimDescent

/-! ## The torsion-decision soundness on concrete witnesses -/

section Witnesses

open DeepWiki.SymbolicIntegration

/-- The engine decides the infinite-order witness `(3,5)` on `y² = x³ − 2` non-elementary:
`isTorsionDivisor = none`, `elementarityViaTorsion = false`, and `torsionLogTerm = none`. -/
theorem engine_none_of_nonTorsion_witness :
    isTorsionDivisor 5 hypRhoX3m2 1 hypPt35 = none
    ∧ elementarityViaTorsion 5 hypRhoX3m2 1 hypPt35 = false
    ∧ (torsionLogTerm 5 tltRhoX3m2 hypRhoX3m2 1 hypPt35).isNone = true := by native_decide

/-- The engine decides the order-3 flex `(0,1)` on `y² = x³ + 1` elementary: `isTorsionDivisor =
some 3`, `elementarityViaTorsion = true`, and `torsionLogTerm` produces a `(1/3)·log(y − 1)` term. -/
theorem engine_some_of_torsion_witness :
    isTorsionDivisor 5 hypRhoX3p1 1 hypPt01 = some 3
    ∧ elementarityViaTorsion 5 hypRhoX3p1 1 hypPt01 = true
    ∧ (torsionLogTerm 5 tltRhoX3p1 hypRhoX3p1 1 hypPt01).isSome = true := by native_decide

end Witnesses

/-! ## The deep frontier (named `def`s, never `sorry`) -/

section Frontier

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- Frontier 1 — Liouville's structure theorem for a curve's function field: for every differential
algebraic extension `K` with an `IsLiouville F K` instance, base non-elementarity
(`¬ IsAlgebraicElementary F F f`) stays non-elementary over `K`, i.e. the search over `K` is exhaustive. -/
def AlgebraicLiouvilleFrontier : Prop :=
  ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K] [IsLiouville F K]
    (f : F), ¬ IsAlgebraicElementary F F f → ¬ IsAlgebraicElementary F K f

omit [CharZero F] in
/-- `AlgebraicLiouvilleFrontier F` is a theorem at the single-extension level: for any Liouville
extension `K / F`, base non-elementarity propagates. -/
theorem algebraicLiouville_single_extension : AlgebraicLiouvilleFrontier F := by
  intro K _ _ _ _ _ f h hK
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := hK
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville f ι c hc u v hrep
  exact h ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-! ### The rational-part half of the decomposition (the always-elementary part) -/

omit [CharZero F] in
/-- The rational part `D(v)` is always elementary: any `f = v′` is `IsAlgebraicElementary F F` via
the empty constant family and antiderivative `v`. -/
theorem ratPart_isAlgebraicElementary (v : F) : IsAlgebraicElementary F F (v′) := by
  refine ⟨Empty, inferInstance, Empty.elim, fun x => x.elim, Empty.elim, v, ?_⟩
  simp only [Algebra.algebraMap_self_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_add]

/-- Frontier 1b — rational-part exhaustiveness: if `f` is elementary, then `f − v′` (after
subtracting the computed rational antiderivative) is elementary with a purely logarithmic form
(empty derivative part, all constants × `logDeriv`). -/
def RationalPartExhaustivenessFrontier : Prop :=
  ∀ (f v : F), IsAlgebraicElementary F F f →
    IsAlgebraicElementary F F (f - v′) →
      ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → F),
        (f - v′) = ∑ x, c x * logDeriv (u x)

end Frontier

/-! ## Frontier piece 2 — the good-reduction divisor-torsion decision correctness -/

section TorsionFrontier

open DeepWiki.SymbolicIntegration

/-- Frontier 2 — the good-reduction torsion-decision correctness: the Boolean decision
`elementarityViaTorsion p ρq g D` agrees with an abstract torsion predicate `isTorsion D` for some
good prime `p`. -/
def DivisorTorsionDecisionFrontier
    (isTorsion : CPolyG.MumfordDivisor ℚ → Prop) : Prop :=
  ∀ (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ),
    ∃ (p : ℕ) (_ : Fact p.Prime),
      (elementarityViaTorsion p ρq g D = true ↔ isTorsion D)

/-- `elementarityViaTorsion p ρq g D = true ↔ ∃ m, isTorsionDivisor p ρq g D = some m`: the Boolean
decision is exactly whether a torsion order was found. -/
theorem elementarityViaTorsion_iff_some (p : ℕ) [Fact p.Prime]
    (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ) :
    elementarityViaTorsion p ρq g D = true
      ↔ ∃ m, isTorsionDivisor p ρq g D = some m := by
  unfold elementarityViaTorsion
  rw [Option.isSome_iff_exists]

/-- `(torsionLogTerm p ρ ρq g D).isSome ↔ ∃ m, isTorsionDivisor p ρq g D = some m`: the log branch
fires exactly when the torsion decision returns `some m`. -/
theorem torsionLogTerm_isSome_iff (p : ℕ) [Fact p.Prime]
    (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ) :
    (torsionLogTerm p ρ ρq g D).isSome = true
      ↔ ∃ m, isTorsionDivisor p ρq g D = some m := by
  unfold torsionLogTerm
  cases h : isTorsionDivisor p ρq g D with
  | none => simp
  | some m => simp

end TorsionFrontier

/-! ## The algebraic-completeness residual, and the decision-procedure equivalence -/

section Assembly

open DeepWiki.SymbolicIntegration

variable (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ)

/-- The algebraic-completeness residual `AlgebraicCompletenessResidual p ρq g D isTorsion elem`:
bundles the two frontier-instances on divisor `D` — `htorsion` (frontier 2) and `hcriterion`
(frontier 1) — that turn the engine's non-principal-branch output into the integrand's elementarity. -/
structure AlgebraicCompletenessResidual (p : ℕ) [Fact p.Prime]
    (isTorsion : Prop) (elem : Prop) : Prop where
  /-- Frontier 2 on `D`: `(∃ m, isTorsionDivisor = some m) ↔ isTorsion`. -/
  htorsion : (∃ m, isTorsionDivisor p ρq g D = some m) ↔ isTorsion
  /-- Frontier 1 on `D`: `isTorsion ↔ elem` (elementary iff the residue divisor is torsion). -/
  hcriterion : isTorsion ↔ elem

/-- Algebraic completeness modulo the residual: under `AlgebraicCompletenessResidual`, the engine's
non-principal log branch returns a term iff the integrand is elementary —
`(torsionLogTerm p ρ ρq g D).isSome = true ↔ elem`. -/
theorem cIntegrateAlgebraicWf_complete_of_residual {isTorsion elem : Prop} (p : ℕ)
    [Fact p.Prime] (hres : AlgebraicCompletenessResidual ρq g D p isTorsion elem) :
    (torsionLogTerm p ρ ρq g D).isSome = true ↔ elem := by
  rw [torsionLogTerm_isSome_iff, hres.htorsion, hres.hcriterion]

/-- Non-elementarity ⟹ the engine emits no log term: under the residual,
`¬ elem → (torsionLogTerm p ρ ρq g D).isNone = true`. -/
theorem engine_none_of_not_elementary {isTorsion elem : Prop} (p : ℕ) [Fact p.Prime]
    (hres : AlgebraicCompletenessResidual ρq g D p isTorsion elem) (hne : ¬ elem) :
    (torsionLogTerm p ρ ρq g D).isNone = true := by
  rw [Option.isNone_iff_eq_none, ← Option.not_isSome_iff_eq_none, Bool.not_eq_true]
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  exact hne ((cIntegrateAlgebraicWf_complete_of_residual ρ ρq g D p hres).mp hcon)

end Assembly

/-! ## The completeness map

`cIntegrateAlgebraicWf_complete_of_residual` proves `some ⟺ elementary` under
`AlgebraicCompletenessResidual`; `engine_none_of_not_elementary` is the "`none` ⟹ not elementary"
reading. The within-tower descent, the always-elementary rational part, and the engine-side control
flow are proven; the two deep frontiers (`AlgebraicLiouvilleFrontier`,
`DivisorTorsionDecisionFrontier`, plus `RationalPartExhaustivenessFrontier`) are named `def`s, never
`sorry`. -/

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
