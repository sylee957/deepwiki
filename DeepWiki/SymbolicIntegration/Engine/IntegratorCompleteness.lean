import DeepWiki.SymbolicIntegration.LiouvilleLog
import DeepWiki.SymbolicIntegration.RationalIntegrationLiouville
import DeepWiki.SymbolicIntegration.Engine.LiouvilleExpBridge
import Mathlib.FieldTheory.Differential.Liouville

/-! # Integrator completeness: non-elementarity propagation

The Liouville-form existential `HasLiouvilleForm`, its equivalence with Mathlib's
`Differential.IsLiouville` (`isLiouville_iff_descends`), and non-elementarity propagation up
logarithmic and log-then-algebraic towers, via the log keystone `isLiouville_logExtension_uncond`. -/

open scoped Differential
open Polynomial Differential algebraMap
open DeepWiki.SymbolicIntegration.LiouvilleLog

namespace DeepWiki.SymbolicIntegration.Completeness

section Abstract

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- `HasLiouvilleForm F K a`: `↑a = ∑ᵢ ↑cᵢ · logDeriv uᵢ + v′` in `K` for constants `cᵢ ∈ F`, arguments
`uᵢ ∈ K`, `v ∈ K` — the Liouville form of "`∫ a` is elementary in `K`". -/
def HasLiouvilleForm (a : F) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → K) (v : K),
    (a : K) = ∑ x, (c x : K) * logDeriv (u x) + v′

/-- Given `IsLiouville F K`, a base integrand `a ∈ F` with a Liouville form over `K` already has one
over `F`. -/
theorem elementary_base_of_elementary_extension [IsLiouville F K] (a : F)
    (h : HasLiouvilleForm F K a) : HasLiouvilleForm F F a := by
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := h
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville a ι c hc u v hrep
  exact ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-- Non-elementarity propagates up a Liouville extension: no Liouville form over `F` implies none over
`K`. -/
theorem not_elementary_extension_of_not_elementary_base [IsLiouville F K] (a : F)
    (h : ¬ HasLiouvilleForm F F a) : ¬ HasLiouvilleForm F K a :=
  fun hK => h (elementary_base_of_elementary_extension F K a hK)

/-- **Tower exhaustiveness (transitivity kernel of Thm 5.5.2/5.5.3).** Non-elementarity propagates up a
*composed* Liouville tower `F ⊆ K ⊆ L`: if `a ∈ F` has no Liouville form over `F`, it has none over the
top `L`. Composes the two Liouville layers with `IsLiouville.trans`, so iterating gives the general
finite-tower "no Liouville form over the base ⟹ not elementary anywhere in the tower". -/
theorem not_elementary_tower_of_not_elementary_base (L : Type*) [Field L] [Differential L]
    [Algebra K L] [Algebra F L] [DifferentialAlgebra F K] [IsScalarTower F K L]
    [Differential.ContainConstants F K] [IsLiouville F K] [IsLiouville K L]
    (a : F) (h : ¬ HasLiouvilleForm F F a) : ¬ HasLiouvilleForm F L a := by
  haveI : IsLiouville F L := IsLiouville.trans F K ‹IsLiouville F K› ‹IsLiouville K L›
  exact not_elementary_extension_of_not_elementary_base F L a h

/-- `IsLiouville F K ↔` for every base integrand, a Liouville form over `K` descends to one over `F`. -/
theorem isLiouville_iff_descends :
    IsLiouville F K ↔ ∀ a : F, HasLiouvilleForm F K a → HasLiouvilleForm F F a := by
  constructor
  · intro inst a h
    exact elementary_base_of_elementary_extension F K a h
  · intro hdesc
    refine ⟨fun a ι _ c hc u v hrep => ?_⟩
    obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := hdesc a ⟨ι, inferInstance, c, hc, u, v, hrep⟩
    refine ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, ?_⟩
    simpa only [Algebra.algebraMap_self_apply] using hrep₀

end Abstract

section LogTower

variable {F : Type*} [Field F] [Differential F] [CharZero F]

/-- Completeness for a single logarithmic extension: for a genuine new log monomial (`NondegenerateLog u`),
a Liouville form over `F(log u) = RatFunc F` descends to one over `F`. -/
theorem logExtension_completeness (u : F) (hnd : NondegenerateLog u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    ∀ a : F, HasLiouvilleForm F (RatFunc F) a → HasLiouvilleForm F F a := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  haveI : IsLiouville F (RatFunc F) := isLiouville_logExtension_uncond u hnd
  intro a h
  exact elementary_base_of_elementary_extension F (RatFunc F) a h

/-- Non-elementarity propagates across a logarithmic extension: no Liouville form over `F` implies none
over `F(log u) = RatFunc F` for a genuine new log monomial (`NondegenerateLog u`). -/
theorem not_elementary_logExtension_of_not_elementary_base (u : F) (hnd : NondegenerateLog u)
    (a : F) (h : ¬ HasLiouvilleForm F F a) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    ¬ HasLiouvilleForm F (RatFunc F) a := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  haveI : IsLiouville F (RatFunc F) := isLiouville_logExtension_uncond u hnd
  exact not_elementary_extension_of_not_elementary_base F (RatFunc F) a h

end LogTower

section ExpTower

open DeepWiki.SymbolicIntegration.LiouvilleExp
open DeepWiki.SymbolicIntegration.LiouvilleExpBridge (isLiouville_expExtension_uncond)

variable {F : Type*} [Field F] [Differential F] [CharZero F]

/-- Completeness for a single exponential extension: for a genuine new exp monomial
(`NondegenerateExp u`), a Liouville form over `F(exp u) = RatFunc F` descends to one over `F`. -/
theorem expExtension_completeness (u : F) (hnd : NondegenerateExp u) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    ∀ a : F, HasLiouvilleForm F (RatFunc F) a → HasLiouvilleForm F F a := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  haveI : IsLiouville F (RatFunc F) := isLiouville_expExtension_uncond u hnd
  intro a h
  exact elementary_base_of_elementary_extension F (RatFunc F) a h

/-- Non-elementarity propagates across an exponential extension: no Liouville form over `F` implies
none over `F(exp u) = RatFunc F` for a genuine new exp monomial (`NondegenerateExp u`). -/
theorem not_elementary_expExtension_of_not_elementary_base (u : F) (hnd : NondegenerateExp u)
    (a : F) (h : ¬ HasLiouvilleForm F F a) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    ¬ HasLiouvilleForm F (RatFunc F) a := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  haveI : IsLiouville F (RatFunc F) := isLiouville_expExtension_uncond u hnd
  exact not_elementary_extension_of_not_elementary_base F (RatFunc F) a h

end ExpTower

section LogAlgebraicTower

variable {F : Type*} [Field F] [Differential F] [CharZero F]

/-- Completeness for a log-then-algebraic tower `F ⊆ F(log u) ⊆ A` (`A / F(log u)` finite algebraic):
a Liouville form over `A` descends to one over `F`, composing the log keystone with the algebraic
Liouville case via `IsLiouville.trans`. -/
theorem logAlgebraic_tower_completeness (u : F) (hnd : NondegenerateLog u)
    (A : Type*) [Field A] [Differential A]
    [Algebra (RatFunc F) A]
    [letI := logDifferential u; DifferentialAlgebra (RatFunc F) A]
    [Algebra F A] [DifferentialAlgebra F A]
    [letI := logDifferential u; IsScalarTower F (RatFunc F) A]
    [letI := logDifferential u; FiniteDimensional (RatFunc F) A]
    [letI := logDifferential u; Differential.ContainConstants F (RatFunc F)] :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    ∀ a : F, HasLiouvilleForm F A a → HasLiouvilleForm F F a := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  haveI hlog : IsLiouville F (RatFunc F) := isLiouville_logExtension_uncond u hnd
  haveI halg : IsLiouville (RatFunc F) A := isLiouville_of_finiteDimensional
  haveI : IsLiouville F A := IsLiouville.trans F (RatFunc F) hlog halg
  intro a h
  exact elementary_base_of_elementary_extension F A a h

/-- Non-elementarity propagates across a log-then-algebraic tower: no `F`-Liouville form implies none
over `A`. -/
theorem not_elementary_logAlgebraic_tower_of_not_elementary_base (u : F) (hnd : NondegenerateLog u)
    (A : Type*) [Field A] [Differential A]
    [Algebra (RatFunc F) A]
    [letI := logDifferential u; DifferentialAlgebra (RatFunc F) A]
    [Algebra F A] [DifferentialAlgebra F A]
    [letI := logDifferential u; IsScalarTower F (RatFunc F) A]
    [letI := logDifferential u; FiniteDimensional (RatFunc F) A]
    [letI := logDifferential u; Differential.ContainConstants F (RatFunc F)]
    (a : F) (h : ¬ HasLiouvilleForm F F a) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    ¬ HasLiouvilleForm F A a :=
  fun hA => h (logAlgebraic_tower_completeness u hnd A a hA)

end LogAlgebraicTower

section ConcreteWitness

variable {F : Type*} [Field F] [Differential F] [CharZero F]

/-- `BaseFieldObstruction a`: the integrand `a` admits no Liouville form over the base field `F`
itself. -/
def BaseFieldObstruction (a : F) : Prop := ¬ HasLiouvilleForm F F a

/-- Concrete non-elementarity reduction: `BaseFieldObstruction a` together with `NondegenerateLog u`
gives that `a` has no Liouville form over `F(log u)`. -/
theorem not_elementary_witness_criterion (u : F) (hnd : NondegenerateLog u)
    (a : F) (hobs : BaseFieldObstruction a) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    ¬ HasLiouvilleForm F (RatFunc F) a :=
  not_elementary_logExtension_of_not_elementary_base u hnd a hobs

end ConcreteWitness

/-! ## The remaining frontier

Named `Prop`-valued obligations for closing full "`none` ⟹ not elementary" over a mixed
transcendental tower. -/

section Roadmap

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- Frontier piece 1 (deliberately-too-strong roadmap marker): a Liouville instance `IsLiouville F K`
for *every* differential extension `K`. This blanket form is NOT a theorem — an arbitrary extension
need not be Liouville. The honest, per-extension exponential content — the sibling of the log keystone
`logExtension_completeness` — is proved as `expExtension_completeness` (single exp extension, under the
genuine new-monomial condition `NondegenerateExp u`), built on the unconditional exp Liouville keystone
`isLiouville_expExtension_uncond`. -/
def ExpCaseLiouvilleFrontier : Prop :=
  ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K],
    Nonempty (IsLiouville F K)

/-- Frontier piece 2 (tower exhaustiveness): for every Liouville extension `K / F`, base
non-elementarity propagates — the inductive consequence the elementary-tower structure theorem would
iterate. -/
def TowerExhaustivenessFrontier : Prop :=
  ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K] [IsLiouville F K]
    (a : F), ¬ HasLiouvilleForm F F a → ¬ HasLiouvilleForm F K a

omit [CharZero F] in
/-- `TowerExhaustivenessFrontier F` holds: single-layer propagation is a theorem, given a Liouville
instance at each layer. -/
theorem towerExhaustiveness_single_layer : TowerExhaustivenessFrontier F := by
  intro K _ _ _ _ _ a h
  exact not_elementary_extension_of_not_elementary_base F K a h

/-- Frontier piece 3: for every base integrand with `BaseFieldObstruction` and every genuine new log,
the integrand is non-elementary over the log extension. -/
def BaseObstructionFrontier : Prop :=
  ∀ (a : F), BaseFieldObstruction a → ∀ (u : F), NondegenerateLog u →
    letI := logDifferential u; letI := logDifferentialAlgebra u
    ¬ HasLiouvilleForm F (RatFunc F) a

/-- `BaseObstructionFrontier F` holds: the base-obstruction-to-non-elementary reduction is proved. -/
theorem baseObstruction_frontier_holds : BaseObstructionFrontier F := by
  intro a hobs u hnd
  exact not_elementary_witness_criterion u hnd a hobs

end Roadmap

/-! ## Restatements pinning the completeness content

These `example`s pin the assembled statements to their plain mathematical meaning. -/

section Restatements

variable {F : Type*} [Field F] [Differential F] [CharZero F]

-- The single-log keystone yields completeness: elementary over `F(log u)` descends to `F`.
example (u : F) (hnd : NondegenerateLog u) (a : F)
    (h : letI := logDifferential u; HasLiouvilleForm F (RatFunc F) a) :
    HasLiouvilleForm F F a :=
  logExtension_completeness u hnd a h

-- Non-elementarity over the base propagates to the log extension (the integrator-completeness step).
example (u : F) (hnd : NondegenerateLog u) (a : F)
    (h : ¬ HasLiouvilleForm F F a) :
    letI := logDifferential u; ¬ HasLiouvilleForm F (RatFunc F) a :=
  not_elementary_logExtension_of_not_elementary_base u hnd a h

-- The single-exp keystone yields completeness: elementary over `F(exp u)` descends to `F`.
example (u : F) (hnd : DeepWiki.SymbolicIntegration.LiouvilleExp.NondegenerateExp u) (a : F)
    (h : letI := DeepWiki.SymbolicIntegration.LiouvilleExp.expDifferential u;
      HasLiouvilleForm F (RatFunc F) a) :
    HasLiouvilleForm F F a :=
  expExtension_completeness u hnd a h

-- Non-elementarity over the base propagates to the exp extension (the integrator-completeness step).
example (u : F) (hnd : DeepWiki.SymbolicIntegration.LiouvilleExp.NondegenerateExp u) (a : F)
    (h : ¬ HasLiouvilleForm F F a) :
    letI := DeepWiki.SymbolicIntegration.LiouvilleExp.expDifferential u;
      ¬ HasLiouvilleForm F (RatFunc F) a :=
  not_elementary_expExtension_of_not_elementary_base u hnd a h

-- A concrete witness is one base-field obstruction away (rational base: that obstruction is done).
example (u : F) (hnd : NondegenerateLog u) (a : F) (hobs : BaseFieldObstruction a) :
    letI := logDifferential u; ¬ HasLiouvilleForm F (RatFunc F) a :=
  not_elementary_witness_criterion u hnd a hobs

end Restatements

-- The abstract completeness ⟺ Liouville reformulation (holds for every Liouville extension).
example (F K : Type*) [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K] :
    IsLiouville F K ↔ ∀ a : F, HasLiouvilleForm F K a → HasLiouvilleForm F F a :=
  isLiouville_iff_descends F K

end DeepWiki.SymbolicIntegration.Completeness
