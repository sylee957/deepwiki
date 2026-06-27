import DeepWiki.SymbolicIntegration.LiouvilleLogExtension
import DeepWiki.SymbolicIntegration.RationalIntegrationLiouville
import Mathlib.FieldTheory.Differential.Liouville

/-! # Completeness of the integrator — the "`none` ⟹ not elementary" frontier

This file maps and assembles the **completeness** direction of the transcendental Risch
integrator: when the integrator returns `none`, the integrand has **no elementary antiderivative**.
The *soundness* direction (`cIntegrate` returns `Some F ⟹ D F = f`, the algebraic
`D(∫f) = f` capstone) is done elsewhere; this file is about the harder converse, which is
**Liouville's theorem** (Liouville 1833–41; Rosenlicht, *Integration in finite terms*, 1972).

## What "elementary integral" means here (and why there is no `IsElementary` in Mathlib)

Mathlib has **no** `IsElementary`/`IsElementaryIntegral` predicate.  What it *does* have is the
**structural Liouville condition** `Differential.IsLiouville F K`
(`Mathlib/FieldTheory/Differential/Liouville.lean`): a differential field extension `K / F` is
*Liouville* when every `a ∈ F` that can be written as
`a = ∑ᵢ cᵢ · logDeriv uᵢ + v′` with `uᵢ, v ∈ K` and `cᵢ ∈ F` constant, can **already** be written
that way with everything in `F`.  This is exactly the engine of Liouville's theorem: the literal
content of "`∫ a` is elementary" is "`a` has the Liouville form `a = v′ + ∑ cᵢ logDeriv uᵢ` over
some elementary extension tower" (constants in the base field's constant subfield, the rest up the
tower), and `IsLiouville` is the inductive step that pushes that form down one extension layer.
Iterated down the whole tower (`IsLiouville.trans`), it collapses an elementary antiderivative
*anywhere up the tower* to the Liouville form *over the base field*.

So in this development the **elementary-integral predicate is a `logDeriv`-sum existential**
(`HasLiouvilleForm` below, in the faithful *relative* shape: constants in the base, arguments up the
tower), and `IsLiouville F K` is **precisely** the statement "elementary over `K` ⟹ elementary over
`F`" for base-field integrands.  Its **contrapositive** is the completeness criterion this file
delivers: *not elementary over `F` ⟹ not elementary over the extension `K`* — non-elementarity
**propagates up** the tower.

## What is reachable now (assembled here, axiom-clean)

- **The abstract completeness reformulation.** `isLiouville_iff_descends` /
  `not_elementary_extension_of_not_elementary_base`: `IsLiouville F K` ⟺ "Liouville-form-over-`K`
  descends to Liouville-form-over-`F`", and its contrapositive is the non-elementarity-propagation
  criterion.  These are pure repackagings of Mathlib's `IsLiouville`, so they are immediate and
  hold for **every** Liouville extension (logarithmic, algebraic, and — once available —
  exponential).
- **The single logarithmic-tower completeness — UNCONDITIONAL.**
  `logExtension_completeness` / `not_elementary_logExtension_of_not_elementary_base`: for a genuine
  new log monomial `t = log u` (`NondegenerateLog u`, i.e. `log u ∉ F`), an integrand `a ∈ F` that
  is elementary in `F(log u) = RatFunc F` is *already* elementary in `F`; contrapositively, a
  base-field integrand with no `F`-Liouville form has none over `F(log u)`.  This rides directly on
  the **done** keystone `isLiouville_logExtension_uncond` (Rosenlicht's transcendental-log case,
  proved unconditionally in `LiouvilleLogExtension.lean`).  This is the genuine reachable milestone.
- **The composite log-then-algebraic tower.** `logAlgebraic_tower_completeness`: chaining the log
  keystone with Mathlib's algebraic case `isLiouville_of_finiteDimensional` via `IsLiouville.trans`
  gives completeness for a tower `F ⊆ F(log u) ⊆ A`, `A / F(log u)` finite algebraic.  This needs
  the *towering* hypothesis `ContainConstants F (RatFunc F)` (the log adds no new constants) and the
  scalar-tower differential compatibility, which are **stated** in `LiouvilleLogExtension.lean`
  (`ContainConstantsObligation`, polynomial layer discharged) but not fully closed there; so this
  composite carries them as explicit, honest hypotheses.

## What the FULL mixed-tower completeness still needs (the precise frontier)

1. **The exponential case** (`IsLiouville F K` for `K = F(exp u)`, `t' = u'·t`).  This is the
   missing transcendental sibling of the log keystone.  A prior attempt
   (`LiouvilleExpExtension.lean`) was **cancelled** by the user; this file does **not** depend on
   finishing it.  Status: the setup and the `v ∈ F` step are done there, but the full
   `IsLiouville F (RatFunc F)` for the exp monomial is **not** proved.  Until it is, towers that
   pass through an exponential have no completeness here.
2. **Tower exhaustiveness** (research-grade).  Even with a Liouville instance for *each* monomial
   kind, "the integrator returned `none`" must be turned into "no elementary tower exists *at all*".
   That requires: (a) every elementary extension is a finite tower of log/exp/algebraic monomials
   (the *structure theorem* for elementary fields), and (b) the integrator's `none` is equivalent
   to the non-solvability of the Risch differential equation at each layer (algorithm⟷Liouville
   correspondence).  Neither is formalized; (a) is the genuine research frontier.
3. **A base-field obstruction** for a *concrete* witness (e.g. `∫ e^{x²}`, `∫ (sin x)/x`).  A fully
   concrete `¬ HasLiouvilleForm` requires proving that **no** Liouville form exists over the *base*
   field — the Rosenlicht residue/partial-fraction computation, here only available for the rational
   base (`RationalIntegrationLiouville.lean`, the `residueAt (G′) = 0` obstruction).
   `not_elementary_witness_criterion` below packages exactly this reduction; supplying the base
   obstruction (and, for `e^{x²}`, the cancelled exp instance) closes a concrete witness.

In short: **non-elementarity-propagation across a logarithmic (and log-then-algebraic) tower is
proven and axiom-clean here.  The remaining frontier is the exp-case Liouville instance (cancelled),
tower exhaustiveness (research), and a base-field obstruction for a concrete witness.**
-/

open scoped Differential
open Polynomial Differential algebraMap
open DeepWiki.SymbolicIntegration.LiouvilleLog

namespace DeepWiki.SymbolicIntegration.Completeness

section Abstract

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- **The "elementary integral of Liouville form exists over the tower `K`" predicate (faithful,
relative shape).**  A base-field integrand `a ∈ F` has an *elementary antiderivative of Liouville
form over `K`* when (viewed in `K`) `↑a = ∑ᵢ ↑cᵢ · logDeriv uᵢ + v′` for some finite family of
**constants `cᵢ ∈ F`** (`(cᵢ)′ = 0`), arguments `uᵢ ∈ K`, and `v ∈ K`.  This is the literal meaning
of "`∫ a` is elementary in the field `K`" in Liouville's theorem (`∫ a = v + ∑ cᵢ log uᵢ`, constants
in the base constant field, the rest up the tower) — and is *exactly* the hypothesis shape of
`Differential.IsLiouville.isLiouville`.  The all-in-`F` base case is `HasLiouvilleForm F F a`. -/
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
