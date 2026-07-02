import DeepWiki.SymbolicIntegration.LiouvilleLogExtension
import DeepWiki.SymbolicIntegration.RationalIntegrationLiouville
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

/-- `HasLiouvilleForm F K a`: the base-field integrand `a ∈ F` satisfies, viewed in `K`,
`↑a = ∑ᵢ ↑cᵢ · logDeriv uᵢ + v′` for finitely many constants `cᵢ ∈ F` (`(cᵢ)′ = 0`), arguments
`uᵢ ∈ K`, and `v ∈ K` — the Liouville form of "`∫ a` is elementary in `K`"
(`∫ a = v + ∑ cᵢ log uᵢ`). The all-in-`F` base case is `HasLiouvilleForm F F a`. -/
def HasLiouvilleForm (a : F) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → K) (v : K),
    (a : K) = ∑ x, (c x : K) * logDeriv (u x) + v′

/-- **`IsLiouville F K` is exactly "Liouville-form-over-`K` descends to Liouville-form-over-`F`".**
The *completeness reformulation*: a base-field integrand `a ∈ F` whose `K`-image has an elementary
(Liouville-form) antiderivative over `K` *already* has one over `F`.  A pure repackaging of Mathlib's
`IsLiouville` (the conclusion existential is literally `HasLiouvilleForm F F a`), so it holds for
**every** Liouville extension `K / F`. -/
theorem elementary_base_of_elementary_extension [IsLiouville F K] (a : F)
    (h : HasLiouvilleForm F K a) : HasLiouvilleForm F F a := by
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := h
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville a ι c hc u v hrep
  exact ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-- **The completeness criterion (contrapositive): non-elementarity propagates UP a Liouville
extension.**  If a base-field integrand `a ∈ F` has *no* elementary (Liouville-form) antiderivative
over `F`, then it has none over a Liouville extension `K` either.  This is the precise engine of
"the integrator returns `none` ⟹ not elementary": once `a` is non-elementary over the base, no
Liouville extension can make it elementary.  Holds for **any** `IsLiouville F K`. -/
theorem not_elementary_extension_of_not_elementary_base [IsLiouville F K] (a : F)
    (h : ¬ HasLiouvilleForm F F a) : ¬ HasLiouvilleForm F K a :=
  fun hK => h (elementary_base_of_elementary_extension F K a hK)

/-- **The two directions packaged as an iff with `IsLiouville` (given the extension).**  For a fixed
Liouville extension `K / F`, "Liouville-form-over-`K` ⟹ Liouville-form-over-`F` for every base
integrand" is *equivalent to* `IsLiouville F K` — the forward direction is the descent above, the
reverse rebuilds the class from the implication.  Confirms `IsLiouville` *is* the completeness
content, nothing more. -/
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

/-- **Completeness for a single logarithmic extension — UNCONDITIONAL.**  Let `t = log u` be a
genuine new log monomial over `F` (`NondegenerateLog u`, i.e. `log u ∉ F`).  Then an integrand
`a ∈ F` that has an elementary (Liouville-form) antiderivative over `F(log u) = RatFunc F` *already*
has one over `F`.  This rides directly on the **done** transcendental-log keystone
`isLiouville_logExtension_uncond` (Rosenlicht's logarithmic case), so it is unconditional modulo
exactly the necessary transcendence hypothesis `NondegenerateLog u`.  This is the genuine reachable
completeness milestone of the transcendental integrator. -/
theorem logExtension_completeness (u : F) (hnd : NondegenerateLog u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    ∀ a : F, HasLiouvilleForm F (RatFunc F) a → HasLiouvilleForm F F a := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  haveI : IsLiouville F (RatFunc F) := isLiouville_logExtension_uncond u hnd
  intro a h
  exact elementary_base_of_elementary_extension F (RatFunc F) a h

/-- **Non-elementarity propagates across a logarithmic extension — UNCONDITIONAL (the completeness
criterion, contrapositive).**  If `a ∈ F` has *no* elementary (Liouville-form) antiderivative over
the base `F`, and `t = log u` is a genuine new log monomial (`NondegenerateLog u`), then `a` has no
elementary antiderivative over `F(log u) = RatFunc F` either.  This is exactly the "`none` over the
base ⟹ `none` after adjoining a logarithm" half of integrator completeness — fully discharged
(modulo only the necessary transcendence input) via the done log keystone. -/
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

section LogAlgebraicTower

variable {F : Type*} [Field F] [Differential F] [CharZero F]

/-- **Completeness for a log-then-algebraic tower** `F ⊆ F(log u) ⊆ A`, `A / F(log u)` finite
algebraic.  Composes the **done** log keystone (`isLiouville_logExtension_uncond`) with Mathlib's
**algebraic** Liouville case (`isLiouville_of_finiteDimensional`) via `IsLiouville.trans`: an
integrand `a ∈ F` elementary over `A` is already elementary over `F`.  Because `IsLiouville.trans`
needs the log layer to add **no new constants**, this carries the towering hypotheses
`ContainConstants F (RatFunc F)` (the log structure's `ContainConstantsObligation`, polynomial layer
discharged in `LiouvilleLogExtension.lean` but not fully closed there) and the differential
scalar-tower compatibilities as explicit, honest assumptions.  No exponential is involved, so the
exp case (cancelled) is not needed. -/
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

/-- **Non-elementarity propagates across a log-then-algebraic tower** (the composite completeness
criterion, contrapositive).  Under the same towering hypotheses, a base integrand `a ∈ F` with no
`F`-Liouville form stays non-elementary over `A`.  So adjoining a logarithm and then any finite
algebraic extension cannot rescue a base-non-elementary integrand. -/
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

/-- **The base-field obstruction predicate (the precise residual content of a concrete witness).**
Records exactly what is left to discharge for a concrete non-elementarity proof over a log tower:
that the integrand `a` admits *no* Liouville form over the base field `F` itself.  For `F = K(x)`
rational this is the (formalized) Rothstein–Trager residue obstruction; for a general transcendental
base it is the open Rosenlicht partial-fraction computation.  Kept as a `def` (not a `sorry`) so
that the witness theorems consume it as a *stated* hypothesis, never an unproved gap. -/
def BaseFieldObstruction (a : F) : Prop := ¬ HasLiouvilleForm F F a

/-- **The concrete-non-elementarity reduction (what a specific witness needs).**  To prove a
*specific* integrand `a ∈ F` non-elementary over a logarithmic extension `F(log u)`, it suffices to
prove the **base-field obstruction** `BaseFieldObstruction a` (no Liouville form over `F` itself)
together with `NondegenerateLog u`.  This isolates exactly the remaining content for any concrete
witness: the base obstruction is the **Rosenlicht residue / partial-fraction computation**, which
here is available only for the *rational* base (`RationalIntegrationLiouville.lean`'s
`residueAt (G′) = 0`).  Supplying that base obstruction closes a concrete witness over a log tower;
witnesses over an *exponential* tower (e.g. `∫ e^{x²}`) additionally need the **cancelled** exp-case
Liouville instance and so are *not* reachable here. -/
theorem not_elementary_witness_criterion (u : F) (hnd : NondegenerateLog u)
    (a : F) (hobs : BaseFieldObstruction a) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    ¬ HasLiouvilleForm F (RatFunc F) a :=
  not_elementary_logExtension_of_not_elementary_base u hnd a hobs

end ConcreteWitness

/-! ## The precise remaining frontier (roadmap)

This block states — as honest `Prop`-valued `def`s, never `sorry` — exactly what closing the FULL
"`none` ⟹ not elementary" for a mixed transcendental tower requires.  Each is a *named* obligation
so the path is mapped and a follow-up can discharge it. -/

section Roadmap

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- **Frontier piece 1 — the exponential-case Liouville instance (CANCELLED attempt).**  The missing
transcendental sibling of the log keystone: for a genuine new exp monomial `t = exp u` (`t' = u'·t`),
`F(exp u) = RatFunc F` is a Liouville extension of `F`, i.e. there *exists* an `IsLiouville F K`
instance for the exp differential structure `K = F(exp u)`.  A prior attempt lives (incomplete) in
`LiouvilleExpExtension.lean` and was **cancelled by the user**; this development does not depend on
it.  Until such an instance exists, towers through an exponential have no completeness.  Stated
abstractly (over an arbitrary differential extension `K` standing for `F(exp u)`) as the *existence*
of the Liouville instance — the exp `Differential`/`DifferentialAlgebra` structures live in the
cancelled file, not in scope here. -/
def ExpCaseLiouvilleFrontier : Prop :=
  ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K],
    Nonempty (IsLiouville F K)

/-- **Frontier piece 2 — tower exhaustiveness (RESEARCH-grade).**  Turning "the integrator returned
`none`" into "no elementary antiderivative exists *at all*" needs the **structure theorem for
elementary extensions**: every elementary differential field over `F` is a finite tower of
logarithmic, exponential, and algebraic monomials.  Combined with a Liouville instance per monomial
kind (log: done; algebraic: Mathlib; exp: cancelled) and the algorithm⟷Liouville correspondence
(`none` ⟺ Risch-DE unsolvable at each layer), this would collapse any elementary integral to the
base Liouville form.  Not formalized; the structure theorem is the genuine research frontier.
Stated as: *for every* differential extension `K / F` carrying a Liouville instance, base
non-elementarity propagates (the inductive consequence the structure theorem would let one iterate). -/
def TowerExhaustivenessFrontier : Prop :=
  ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K] [IsLiouville F K]
    (a : F), ¬ HasLiouvilleForm F F a → ¬ HasLiouvilleForm F K a

omit [CharZero F] in
/-- **Frontier piece 2 is already a THEOREM at the single-layer level** (the inductive step the
structure theorem would iterate): for *any* Liouville extension `K / F`, base non-elementarity
propagates.  This is exactly `not_elementary_extension_of_not_elementary_base` quantified over the
extension — so `TowerExhaustivenessFrontier F` holds *given* a Liouville instance at each layer; the
open part is purely the structure theorem (every elementary tower factors into log/exp/algebraic
monomials), not this propagation. -/
theorem towerExhaustiveness_single_layer : TowerExhaustivenessFrontier F := by
  intro K _ _ _ _ _ a h
  exact not_elementary_extension_of_not_elementary_base F K a h

/-- **Frontier piece 3 — a base-field obstruction for a concrete witness (rational base: DONE).**
For a fully concrete non-elementarity (e.g. `∫ (sin x)/x` over a log tower), one must prove the
*base* field admits no Liouville form for the integrand.  For the **rational** base `K(x)` this is
the formalized Rothstein–Trager residue obstruction (`RationalIntegrationLiouville.lean`,
`residueAt (G′) = 0` and the logarithm-free iff); `not_elementary_witness_criterion` consumes it.
For a general transcendental base it is the open Rosenlicht partial-fraction computation.  Recorded
as: *for every* base integrand with the obstruction and *every* genuine new log, the integrand is
non-elementary over the log extension — which `not_elementary_witness_criterion` already proves. -/
def BaseObstructionFrontier : Prop :=
  ∀ (a : F), BaseFieldObstruction a → ∀ (u : F), NondegenerateLog u →
    letI := logDifferential u; letI := logDifferentialAlgebra u
    ¬ HasLiouvilleForm F (RatFunc F) a

/-- **Frontier piece 3 is a THEOREM** modulo only the base obstruction itself: the reduction "base
obstruction + genuine new log ⟹ non-elementary over the log extension" is fully proved
(`not_elementary_witness_criterion`).  So a concrete witness is *exactly one base-field obstruction
away* — and that obstruction is the (done-for-rational) Rosenlicht residue computation. -/
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
