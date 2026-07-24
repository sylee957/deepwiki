import Mathlib.FieldTheory.Differential.Liouville
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # Structural Liouville descent

The Weak Liouville Theorem over Mathlib's `Differential.IsLiouville`: for a Liouville extension
`L ⊇ F` with no new constants, `g ∈ L` with `g′ ∈ F` gives `g′ = v₀′ + Σ cᵢ · logDeriv vᵢ` over `F`.
Its contrapositive propagates base non-elementarity through Liouville towers. -/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.LiouvilleStructure

/-! ## The Weak-Liouville-form predicate -/

section Predicate

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- `HasWeakLiouvilleForm F K g`: read in `K`, `↑g = ∑ᵢ ↑cᵢ · logDeriv uᵢ + v′` for constants
`cᵢ ∈ F`, `uᵢ ∈ K`, `v ∈ K`. -/
def HasWeakLiouvilleForm (g : F) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → K) (v : K),
    (algebraMap F K g) = ∑ x, (algebraMap F K (c x)) * logDeriv (u x) + v′

end Predicate

/-! ## The structural core: the descent through a Liouville instance -/

section Core

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- The descent: for a Liouville extension `K / F`, a base `g ∈ F` with a `K`-Liouville form has an
`F`-Liouville form. -/
theorem weakLiouville_descend [IsLiouville F K] (g : F) (h : HasWeakLiouvilleForm F K g) :
    HasWeakLiouvilleForm F F g := by
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := h
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville g ι c hc u v hrep
  exact ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-- Non-elementarity propagates up a Liouville extension: no `F`-Liouville form for `g` gives no
`K`-Liouville form. -/
theorem weakLiouville_propagates [IsLiouville F K] (g : F)
    (h : ¬ HasWeakLiouvilleForm F F g) : ¬ HasWeakLiouvilleForm F K g :=
  fun hK => h (weakLiouville_descend F K g hK)

/-- `IsLiouville F K ↔` every base element with a `K`-Liouville form has an `F`-Liouville form. -/
theorem hasWeakLiouvilleForm_descends_iff :
    IsLiouville F K ↔ ∀ g : F, HasWeakLiouvilleForm F K g → HasWeakLiouvilleForm F F g := by
  constructor
  · intro inst g h
    exact weakLiouville_descend F K g h
  · intro hdesc
    refine ⟨fun g ι _ c hc u v hrep => ?_⟩
    obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := hdesc g ⟨ι, inferInstance, c, hc, u, v, hrep⟩
    refine ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, ?_⟩
    simpa only [Algebra.algebraMap_self_apply] using hrep₀

end Core

/-! ## The Weak Liouville Theorem proper: `g ∈ L`, `g′ ∈ F` ⟹ the Liouville form over `F` -/

section Theorem

variable (F : Type*) (L : Type*) [Field F] [Field L] [Differential F] [Differential L]
variable [Algebra F L] [DifferentialAlgebra F L]

omit [DifferentialAlgebra F L] in
/-- A base element that is a derivative up the tower has the trivial `L`-Liouville form: `↑a = (↑g)′`
gives `HasWeakLiouvilleForm F L a` with empty constant family. -/
theorem hasWeakLiouvilleForm_tower_of_isDeriv (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F L a :=
  ⟨Empty, inferInstance, Empty.elim, fun x => x.elim, Empty.elim, g, by
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] using h⟩

omit [DifferentialAlgebra F L] in
/-- Weak Liouville Theorem, descent form: for a Liouville extension `L / F`, `g ∈ L` with `g′ ∈ F`
(via `↑a = (↑g)′`) gives `HasWeakLiouvilleForm F F a`. -/
theorem weakLiouville_of_isLiouville [IsLiouville F L] (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F F a :=
  weakLiouville_descend F L a (hasWeakLiouvilleForm_tower_of_isDeriv F L a g h)

end Theorem

/-! ## The algebraic case: via Mathlib's `isLiouville_of_finiteDimensional` -/

section CaseAlgebraic

variable (F : Type*) (L : Type*) [Field F] [Field L] [CharZero F] [Differential F] [Differential L]
variable [Algebra F L] [DifferentialAlgebra F L]

/-- The algebraic case: for a finite-dimensional extension `L / F` (char 0), `g ∈ L` with `g′ ∈ F`
gives `HasWeakLiouvilleForm F F a`. -/
theorem weakLiouville_finiteDimensional [FiniteDimensional F L] (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F F a := by
  haveI : IsLiouville F L := isLiouville_of_finiteDimensional
  exact weakLiouville_of_isLiouville F L a g h

/-- Algebraic case, contrapositive: no `F`-Liouville form for `a` gives none over a finite-dimensional
extension `L / F`. -/
theorem not_weakElementary_finiteDimensional [FiniteDimensional F L] (a : F)
    (h : ¬ HasWeakLiouvilleForm F F a) : ¬ HasWeakLiouvilleForm F L a := by
  haveI : IsLiouville F L := isLiouville_of_finiteDimensional
  exact weakLiouville_propagates F L a h

end CaseAlgebraic

/-! ## The tower assembly: iterated `IsLiouville.trans` -/

section TowerAssembly

variable (F : Type*) (M : Type*) (L : Type*)
variable [Field F] [Field M] [Field L]
variable [Differential F] [Differential M] [Differential L]
variable [Algebra F M] [Algebra M L] [Algebra F L]
variable [DifferentialAlgebra F M] [DifferentialAlgebra M L] [DifferentialAlgebra F L]
variable [IsScalarTower F M L] [Differential.ContainConstants F M]

omit [DifferentialAlgebra M L] [DifferentialAlgebra F L] in
/-- Tower step: `M / F` and `L / M` Liouville with `ContainConstants F M` give `IsLiouville F L`. -/
theorem isLiouville_tower [IsLiouville F M] [IsLiouville M L] : IsLiouville F L :=
  IsLiouville.trans F M ‹IsLiouville F M› ‹IsLiouville M L›

omit [DifferentialAlgebra M L] [DifferentialAlgebra F L] in
/-- Weak Liouville Theorem over a two-layer tower `F ⊆ M ⊆ L`: `g ∈ L` with `g′ ∈ F` gives
`HasWeakLiouvilleForm F F a`. -/
theorem weakLiouville_tower [IsLiouville F M] [IsLiouville M L] (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F F a := by
  haveI : IsLiouville F L := isLiouville_tower F M L
  exact weakLiouville_of_isLiouville F L a g h

omit [DifferentialAlgebra M L] [DifferentialAlgebra F L] in
/-- Two-layer contrapositive: no `F`-Liouville form for `a` gives none over `L`. -/
theorem not_weakElementary_tower [IsLiouville F M] [IsLiouville M L] (a : F)
    (h : ¬ HasWeakLiouvilleForm F F a) : ¬ HasWeakLiouvilleForm F L a := by
  haveI : IsLiouville F L := isLiouville_tower F M L
  exact weakLiouville_propagates F L a h

end TowerAssembly

/-! ## The transcendental exponential-layer assumption -/

section ExpResidual

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- Every transcendental exp monomial layer `K / F` carries an `IsLiouville F K` instance. -/
def ExponentialLayerResidual : Prop :=
  ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K],
    Nonempty (IsLiouville F K)

omit [CharZero F] in
/-- Given `ExponentialLayerResidual F`, the Weak Liouville Theorem holds for an exp layer: `g ∈ K`
with `g′ ∈ F` gives `HasWeakLiouvilleForm F F a`. -/
theorem weakLiouville_of_expResidual (hexp : ExponentialLayerResidual F)
    (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    (a : F) (g : K) (h : (algebraMap F K a) = g′) : HasWeakLiouvilleForm F F a := by
  haveI : IsLiouville F K := (hexp K).some
  exact weakLiouville_of_isLiouville F K a g h

end ExpResidual

/-! ### Axiom audit -/


#print axioms weakLiouville_descend
#print axioms weakLiouville_of_isLiouville
#print axioms weakLiouville_finiteDimensional
#print axioms not_weakElementary_finiteDimensional
#print axioms isLiouville_tower

end DeepWiki.SymbolicIntegration.LiouvilleStructure
