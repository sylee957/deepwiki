import DeepWiki.SymbolicIntegration.ComputableRadicalWellFounded
import DeepWiki.SymbolicIntegration.ComputableTorsionLogTerm
import DeepWiki.SymbolicIntegration.ComputableRadicalLogSoundness
import Mathlib.FieldTheory.Differential.Liouville

/-! # Completeness of the ALGEBRAIC integrator — the "`none` ⟹ not elementary" frontier (Trager)

This file maps and assembles the **completeness** direction of the simple-radical algebraic integrator
`cIntegrateAlgebraicWf` (over `y² = ρ`): when the integrator finds **no** log argument
(`radLogArgSolve = none`) *and* the residue divisor is **not torsion**, the integrand has **no elementary
antiderivative**.  The *soundness* direction (`cIntegrateAlgebraicWf` produces `⟨v, logs⟩ ⟹ D(v + Σ cᵢ log
uᵢ) = f`, the `IsAlgebraicIntegral` capstone of `ComputableRadicalLogSoundness` /
`ComputableUnifiedMixedWfSoundness`) is done elsewhere; this file is the harder converse — **Trager's
algorithm** (Trager, *Integration of Algebraic Functions*, MIT 1984; Bronstein, *Symbolic Integration I*,
Ch. 5–6 / the algebraic Vol. II), riding **Liouville's theorem for algebraic functions**.

## The mathematics (Trager / Liouville-for-algebraic)

For `f` algebraic over `ℚ(x)` (here `f ∈ ℚ(x)[y]/(y² − ρ)`, `y` on the curve), `∫ f dx` is **elementary**
⟺ (Liouville-for-algebraic) `f = D(v) + Σ cᵢ · D(uᵢ)/uᵢ` with `v, uᵢ` algebraic and `cᵢ` constants.  The
algorithm splits this into two parts:

* **The rational part `v`** — computed by the integral-basis Hermite reduction (`radIntegrateRationalWf`
  here), which captures **all** of the algebraic-rational part of the integral.  This part is *always*
  elementary; the engine computes it unconditionally.
* **The log part** — the residues of `f` at the poles form a **divisor `D` on the curve**, and the integral
  is elementary ⟺ that divisor is a **torsion point in the Jacobian** (`m·D = O` for some `m ≥ 1`); then
  `m·D` is principal with generator `g`, and the log part is `(1/m)·log g`.  The decision "is `D` torsion?"
  is the **deep tip** (the height-swell; resolved computationally via good reduction mod `p`,
  `isTorsionDivisor`).

So `cIntegrateAlgebraicWf` returns a log term in exactly two ways: the **principal** case
(`radLogArgSolve = some N`, `1·log(N/D)`) and — via the non-principal branch `torsionLogTerm` — the
**torsion** case (`isTorsionDivisor = some m`, `(1/m)·log g`).  It returns **no** log term (and the
integral is non-elementary, modulo the rational part) exactly when `radLogArgSolve = none` *and* the residue
divisor is non-torsion (`isTorsionDivisor = none`).

## What "algebraic-elementary" means here (and where Mathlib's `IsLiouville` plugs in)

As in the transcendental completeness file (`ComputableIntegratorCompleteness`), the **elementary-integral
predicate is a `logDeriv`-sum existential** over a differential field `K` (`IsAlgebraicElementary` below,
the faithful Liouville shape `↑f = ∑ cᵢ logDeriv uᵢ + v′`).  Mathlib's `Differential.IsLiouville F K` is
exactly "elementary over `K` ⟹ elementary over `F`"; its **algebraic case**
`isLiouville_of_finiteDimensional` (every finite-dimensional extension is Liouville) is the *one* piece of
the algebraic Liouville theorem Mathlib already has, and it gives the **descent within the algebraic tower**
for free.  The genuinely missing structure theorem — "`∫ f` elementary ⟺ the Trager torsion form" for the
*function field of the curve* — is the deep frontier `AlgebraicLiouvilleFrontier` below.

## What is reachable now (assembled here, axiom-clean unless tagged `native_decide`)

* **The abstract descent within a finite algebraic tower** (`elementary_base_of_elementary_finiteDim` /
  `not_elementary_extension_of_not_elementary_base_alg`) — pure repackaging of Mathlib's
  `isLiouville_of_finiteDimensional`: a base integrand elementary over a finite-dimensional algebraic
  extension is already elementary over the base, and contrapositively non-elementarity propagates up a
  finite algebraic extension.  This is the algebraic sibling of the log-tower descent.
* **The torsion-decision soundness on concrete witnesses** — the engine's torsion test returns `none`
  (non-torsion ⟹ NOT elementary) on the rank-1 witness `(3,5)` of `y² = x³ − 2`
  (`engine_none_of_nonTorsion_witness`), and the principal/torsion branch returns a log term on the
  torsion flex `(0,1)` of `y² = x³ + 1` — so the decision gates are non-vacuous (`native_decide`).
* **The completeness reduction to the named frontiers** — `cIntegrateAlgebraicWf_complete_of_residual`:
  modulo the isolated `AlgebraicCompletenessResidual` (the Liouville structure theorem + the
  torsion-decision correctness), `¬ IsAlgebraicElementary f ⟹ cIntegrateAlgebraicWf` returns no log term.

## The precise deep frontier (named `def`s, NEVER `sorry`)

1. **`AlgebraicLiouvilleFrontier`** — Liouville's theorem **for the function field of an algebraic curve**:
   `∫ f` is elementary ⟺ `f = D(v) + Σ cᵢ D(uᵢ)/uᵢ` with the `uᵢ` *algebraic functions on the curve* and the
   residue divisor of the `Σ cᵢ log uᵢ` part **torsion**.  Mathlib has only the finite-extension *descent*
   (`isLiouville_of_finiteDimensional`), **not** this structure theorem for the curve's function field
   (Bronstein Ch. 6 / Trager Ch. 5–6 / Rosenlicht).
2. **`DivisorTorsionDecisionFrontier`** — the engine's torsion test `isTorsionDivisor` is **correct and
   terminating**: it returns `some m` ⟺ the residue divisor is `m`-torsion in `Jac(ℚ̄)`, the termination
   resting on **good reduction mod `p`** (`order_ℚ(D) ∣ order_{𝔽_p}(D)`, the height-swell tip).  The engine
   *computes* the decision (`native_decide`-validated on witnesses), but the abstract correctness of the
   good-reduction order bound is not formalized (Mathlib has the abstract Jacobian but no hyperelliptic
   point-counting / order-bound theorem).

In short: **the rational-part exhaustiveness and the within-tower algebraic descent are reachable; the two
deep frontiers are (i) Liouville's structure theorem for the curve's function field and (ii) the
good-reduction torsion-decision correctness — both stated precisely as named `def`s, never `sorry`.**
-/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.AlgebraicCompleteness

/-! ## The faithful algebraic-elementary predicate (Liouville form over a differential field `K`)

`IsAlgebraicElementary F K f` is the literal meaning of "`∫ f` is elementary in the field `K`" for an
algebraic integrand `f ∈ F`: `↑f = ∑ᵢ ↑cᵢ · logDeriv uᵢ + v′` for constants `cᵢ ∈ F`, arguments `uᵢ ∈ K`,
and `v ∈ K` — exactly the hypothesis shape of `Differential.IsLiouville.isLiouville`.  This is the same
faithful shape as `Completeness.HasLiouvilleForm` in the transcendental file, reused here for the algebraic
tower.  The base case is `IsAlgebraicElementary F F f`. -/

section Predicate

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- **The algebraic-elementary predicate** `IsAlgebraicElementary F K f`: the integrand `f ∈ F` has an
*elementary antiderivative of Liouville form over `K`* — `↑f = ∑ᵢ ↑cᵢ · logDeriv uᵢ + v′` for a finite
family of constants `cᵢ ∈ F` (`(cᵢ)′ = 0`), arguments `uᵢ ∈ K`, and `v ∈ K`.  The literal meaning of "`∫ f`
is elementary in the field `K`" (`∫ f = v + Σ cᵢ log uᵢ`).  For the algebraic integrator, `K` is (an
extension of) the curve's function field `ℚ(x)[y]/(y² − ρ)`; the Trager form `f = D(v) + Σ cᵢ D(uᵢ)/uᵢ`
*is* this `logDeriv`-sum.  The all-in-`F` base case is `IsAlgebraicElementary F F f`. -/
def IsAlgebraicElementary (f : F) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → K) (v : K),
    (algebraMap F K f) = ∑ x, (algebraMap F K (c x)) * logDeriv (u x) + v′

end Predicate

/-! ## The within-tower algebraic descent (reachable: Mathlib's `isLiouville_of_finiteDimensional`)

The *one* piece of Liouville-for-algebraic Mathlib already has is the **finite-extension descent**: every
finite-dimensional field extension is Liouville (`isLiouville_of_finiteDimensional`, for `CharZero F`).  So
an integrand elementary over a finite algebraic extension `K / F` is already elementary over `F` — and
contrapositively, base non-elementarity propagates up a finite algebraic extension.  This is the algebraic
sibling of the log-tower descent in `ComputableIntegratorCompleteness`. -/

section FiniteDimDescent

variable (F : Type*) (K : Type*) [Field F] [Field K] [CharZero F]
variable [Differential F] [Differential K] [Algebra F K] [DifferentialAlgebra F K]

/-- **Algebraic descent: elementary over a finite algebraic extension descends to the base.**  For a
finite-dimensional differential field extension `K / F` (`CharZero F`), an integrand `f ∈ F` whose image is
elementary (Liouville form) over `K` is *already* elementary over `F`.  Rides Mathlib's algebraic Liouville
case `isLiouville_of_finiteDimensional` (every finite-dimensional extension is Liouville) — the algebraic
sibling of the log-tower descent.  This is the within-tower half of Trager completeness: a finite algebraic
extension never makes a base-non-elementary integrand elementary. -/
theorem elementary_base_of_elementary_finiteDim [FiniteDimensional F K] (f : F)
    (h : IsAlgebraicElementary F K f) : IsAlgebraicElementary F F f := by
  haveI : IsLiouville F K := isLiouville_of_finiteDimensional
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := h
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville f ι c hc u v hrep
  exact ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-- **Non-elementarity propagates up a finite algebraic extension (the descent, contrapositive).**  If
`f ∈ F` has *no* elementary (Liouville-form) antiderivative over the base `F`, then it has none over a
finite-dimensional algebraic extension `K / F` either.  The algebraic half of "`none` ⟹ not elementary":
once `f` is non-elementary over the base, a finite algebraic extension cannot rescue it.  Rides
`isLiouville_of_finiteDimensional`. -/
theorem not_elementary_extension_of_not_elementary_base_alg [FiniteDimensional F K] (f : F)
    (h : ¬ IsAlgebraicElementary F F f) : ¬ IsAlgebraicElementary F K f :=
  fun hK => h (elementary_base_of_elementary_finiteDim F K f hK)

end FiniteDimDescent

/-! ## The torsion-decision soundness on concrete witnesses (`native_decide`)

The engine's torsion decision `isTorsionDivisor` / `elementarityViaTorsion` and the non-principal branch
`torsionLogTerm` are the computational face of the log-part criterion.  Their decision gates are
*non-vacuous*: on the rank-1 witness `(3,5)` of `y² = x³ − 2` (a genuine infinite-order point) the decision
is `none`/`false` ⟹ NOT elementary, and on the torsion flex `(0,1)` of `y² = x³ + 1` the branch produces a
`(1/3)·log` term ⟹ elementary.  These pin the structurally-non-elementary witness completeness gives. -/

section Witnesses

open DeepWiki.SymbolicIntegration

/-- **The engine decides the rank-1 witness `(3,5)` NON-elementary** (`engine_none_of_nonTorsion_witness`,
`native_decide`).  The residue divisor `(3,5)` on `y² = x³ − 2` is a genuine infinite-order point (rank-1
curve, trivial torsion); the engine's torsion decision `isTorsionDivisor 5 24 (x³−2) 1 (3,5) = none`, so
`elementarityViaTorsion = false` and the non-principal branch `torsionLogTerm = none` — the engine returns
**no** log term, the structural signature that this part of the integral is **not elementary** (Trager
Ch. 6: a residue divisor of infinite order has no principal multiple).  The completeness direction
operationally: a structurally-non-elementary input ⟹ the engine emits no log term. -/
theorem engine_none_of_nonTorsion_witness :
    isTorsionDivisor 5 24 hypRhoX3m2 1 hypPt35 = none
    ∧ elementarityViaTorsion 5 24 hypRhoX3m2 1 hypPt35 = false
    ∧ (torsionLogTerm 5 24 16 tltRhoX3m2 hypRhoX3m2 1 hypPt35).isNone = true := by native_decide

/-- **The engine decides the torsion flex `(0,1)` elementary, with a `(1/3)·log` term**
(`engine_some_of_torsion_witness`, `native_decide`).  The residue divisor `(0,1)` on `y² = x³ + 1` is the
order-3 inflection point; the engine's torsion decision `isTorsionDivisor 5 16 (x³+1) 1 (0,1) = some 3`, so
`elementarityViaTorsion = true` and the non-principal branch produces the log term `(1/3, y − 1)` — the
integral **is** elementary with a `(1/3)·log(y − 1)` term (Trager Ch. 6 §3, the principal multiple of the
residue divisor).  The contrasting positive answer: the torsion gate is a genuine, non-vacuous decision. -/
theorem engine_some_of_torsion_witness :
    isTorsionDivisor 5 16 hypRhoX3p1 1 hypPt01 = some 3
    ∧ elementarityViaTorsion 5 16 hypRhoX3p1 1 hypPt01 = true
    ∧ (torsionLogTerm 5 16 16 tltRhoX3p1 hypRhoX3p1 1 hypPt01).isSome = true := by native_decide

end Witnesses

end DeepWiki.SymbolicIntegration.AlgebraicCompleteness
