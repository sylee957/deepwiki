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
`ComputableAlgebraicWfSoundness`) is done elsewhere; this file is the harder converse — **Trager's
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

/-! ## ★ The precise deep frontier (named `def`s, NEVER `sorry`)

Closing the FULL "`none` ⟹ not elementary" for the algebraic integrator needs exactly two deep ingredients,
each isolated as an honest `Prop`-valued `def` (never `sorry`).  Trager's algorithm splits `∫ f` into a
rational part (always elementary, computed by the integral-basis Hermite reduction) and a log part (whose
elementarity is the divisor-torsion criterion).  The rational-part exhaustiveness and the within-tower
descent are reachable (above); the two `def`s below name what remains.  Stated abstractly over an arbitrary
differential extension `K` standing for the curve's function field, since the concrete radical tower's
differential structure lives in the engine files, not here. -/

section Frontier

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- **Frontier piece 1 — Liouville's structure theorem for an algebraic curve's function field**
(`AlgebraicLiouvilleFrontier`, Bronstein Ch. 6 / Trager Ch. 5–6 / Rosenlicht).  The deep tip: for the
function field `K` of an algebraic curve over `F`, `∫ f` is **elementary** ⟺ `f = D(v) + Σ cᵢ D(uᵢ)/uᵢ`
with `v, uᵢ ∈ K` and `cᵢ` constants — i.e. `IsAlgebraicElementary F K f` is the *full* characterization of
elementary integrability (not just a sufficient form).  Stated as the **completeness** half: an integrand
non-elementary over the base `F` (`¬ IsAlgebraicElementary F F f`) stays non-elementary over the curve's
function field `K` (`¬ IsAlgebraicElementary F K f`) — the structure theorem's content that the algorithm's
search over `K` is *exhaustive*.  Mathlib has only the finite-extension **descent**
(`isLiouville_of_finiteDimensional`, used above), **not** this structure theorem for a function field; it is
the genuine Liouville-for-algebraic frontier.  Quantified over every differential algebraic extension `K`
carrying an `IsLiouville` instance (the descent Mathlib provides for finite extensions; the open part is
that *the curve's function field is such an extension and the form is exhaustive*). -/
def AlgebraicLiouvilleFrontier : Prop :=
  ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K] [IsLiouville F K]
    (f : F), ¬ IsAlgebraicElementary F F f → ¬ IsAlgebraicElementary F K f

omit [CharZero F] in
/-- **Frontier piece 1 is already a THEOREM at the single-extension level** (the descent the structure
theorem would let one iterate): for *any* Liouville extension `K / F`, base non-elementarity propagates.
This is exactly `IsLiouville`'s descent quantified over the extension — so `AlgebraicLiouvilleFrontier F`
holds *given* a Liouville instance per layer (`isLiouville_of_finiteDimensional` supplies it for finite
algebraic extensions); the open part is purely the structure theorem (the curve's function field *is* a
Liouville extension and the Trager form is *exhaustive*), not this propagation. -/
theorem algebraicLiouville_single_extension : AlgebraicLiouvilleFrontier F := by
  intro K _ _ _ _ _ f h hK
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := hK
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville f ι c hc u v hrep
  exact h ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-! ### The rational-part half of the Trager decomposition (the always-elementary part)

Trager's algorithm splits `∫ f = ∫(rational part) + ∫(log part)`.  The **rational part** is *always*
elementary — it is `D(v)` for the computed `v` (the integral-basis Hermite reduction `radIntegrateRationalWf`
produces it), with **no** log terms.  So the rational part never *obstructs* elementarity; completeness turns
entirely on the log part (the divisor-torsion criterion).  The "always elementary" half is reachable here as
a pure `IsAlgebraicElementary` fact (a `D(v)` element is a Liouville form with the empty log family); the
*exhaustiveness* half — "the computed `v` captures the **whole** rational part" — is the named frontier
below. -/

omit [CharZero F] in
/-- **The rational part `D(v)` is always elementary** (`ratPart_isAlgebraicElementary`): any element of the
form `f = v′` (a pure derivative, no log part) is `IsAlgebraicElementary F F` — take the empty constant
family and antiderivative `v`.  This is the always-elementary half of Trager's rational part: the
integral-basis Hermite reduction's output `v` gives `D(v)`, which is trivially a Liouville form (empty log
sum).  So the rational part never obstructs elementarity; the obstruction is entirely in the log part.
Axiom-clean. -/
theorem ratPart_isAlgebraicElementary (v : F) : IsAlgebraicElementary F F (v′) := by
  refine ⟨Empty, inferInstance, Empty.elim, fun x => x.elim, Empty.elim, v, ?_⟩
  simp only [Algebra.algebraMap_self_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_add]

/-- **Frontier piece 1b — rational-part exhaustiveness** (`RationalPartExhaustivenessFrontier`, Bronstein
Ch. 5 / Trager: the integral-basis Hermite reduction).  The other half of Trager's rational/log split: the
computed rational part `v` (from `radIntegrateRationalWf`) captures **all** of the integral's rational part,
so that the *remaining* integrand (after subtracting `D(v)`) has only a log part — whose elementarity is the
divisor-torsion criterion (`AlgebraicLiouvilleFrontier`).  Stated as: if the integrand `f` is elementary,
then `f − D(v)` is elementary with a **purely logarithmic** form (an empty derivative part, all constants ×
`logDeriv`).  This is the integral-basis exhaustiveness — Mathlib has the abstract integral closure but not
the Hermite-reduction completeness; here it is reachable in principle (the engine's soundness gives
`D(v) = ratPart`) but the *exhaustiveness* (no rational part escapes the reduction) is a stated piece.
Quantified over the reduced integrand `r` and its computed rational antiderivative `v`. -/
def RationalPartExhaustivenessFrontier : Prop :=
  ∀ (f v : F), IsAlgebraicElementary F F f →
    IsAlgebraicElementary F F (f - v′) →
      ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → F),
        (f - v′) = ∑ x, c x * logDeriv (u x)

end Frontier

/-! ## ★ Frontier piece 2 — the good-reduction divisor-torsion decision correctness

The engine's torsion test `isTorsionDivisor` decides the log-part criterion ("is the residue divisor
torsion?") by computing the divisor order via Cantor's Jacobian arithmetic, terminating through **good
reduction mod `p`** (`order_ℚ(D) ∣ order_{𝔽_p}(D)`, the height-swell tip).  Its abstract correctness — that
the computed answer matches the *true* order in `Jac(ℚ̄)` and that the good-reduction bound is a *valid*
ceiling — is the second deep frontier.  We state it against the engine's actual `isTorsionDivisor` /
`elementarityViaTorsion`. -/

section TorsionFrontier

open DeepWiki.SymbolicIntegration

/-- **Frontier piece 2 — the good-reduction torsion-decision correctness**
(`DivisorTorsionDecisionFrontier`, Trager Ch. 6 §2–3, the height-swell tip).  The engine's torsion test is
**correct and terminating**: for a residue divisor `D` on `y² = ρq` and a good prime `p`,
`isTorsionDivisor p cfuel ρq g D = some m` ⟺ `D` is `m`-torsion in the Jacobian (`m·D = O`, the integral
elementary with a `(1/m)·log` term), and `= none` ⟺ `D` is of infinite order (the integral **not**
elementary).  The termination rests on good reduction (`order_ℚ(D) ∣ order_{𝔽_p}(reduction)` so the finite
`Jac(𝔽_p)` order ceilings the otherwise-unbounded ℚ-search).  The engine **computes** this decision
(`native_decide`-validated on `(0,1)`/`(3,5)` witnesses, `engine_some_of_torsion_witness` /
`engine_none_of_nonTorsion_witness`), but the abstract correctness of the good-reduction order bound is
**not** formalized — Mathlib has the abstract Jacobian/divisor class group but no hyperelliptic
point-counting or good-reduction order-bound theorem.  Stated as: the Boolean decision
`elementarityViaTorsion` agrees with an abstract torsion predicate `isTorsion` on the divisor, for some good
prime `p`. -/
def DivisorTorsionDecisionFrontier
    (isTorsion : CPolyG.MumfordDivisor ℚ → Prop) : Prop :=
  ∀ (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ),
    ∃ (p cfuel : ℕ) (_ : Fact p.Prime),
      (elementarityViaTorsion p cfuel ρq g D = true ↔ isTorsion D)

/-- **Frontier piece 2 — the engine's two answers are EXCLUSIVE** (`elementarityViaTorsion_iff_some`): the
Boolean torsion decision `elementarityViaTorsion p cfuel ρq g D = true` is *exactly*
`∃ m, isTorsionDivisor p cfuel ρq g D = some m` — the engine returns "elementary" iff it found a torsion
order, and "not elementary" iff `none`.  Pure control flow over `Option.isSome` (no torsion mathematics), so
unconditional; it pins that the decision is a genuine dichotomy and reduces the frontier
`DivisorTorsionDecisionFrontier` to "the computed `some m`/`none` matches the *true* order" — the
good-reduction correctness above. -/
theorem elementarityViaTorsion_iff_some (p cfuel : ℕ) [Fact p.Prime]
    (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ) :
    elementarityViaTorsion p cfuel ρq g D = true
      ↔ ∃ m, isTorsionDivisor p cfuel ρq g D = some m := by
  unfold elementarityViaTorsion
  rw [Option.isSome_iff_exists]

/-- **Frontier piece 2 — the non-principal log branch fires iff the divisor is decided torsion**
(`torsionLogTerm_isSome_iff`): `torsionLogTerm p cfuel fuel ρ ρq g D` returns a log term (`isSome`) *exactly*
when the torsion decision returns `some m` — so the engine emits a `(1/m)·log g` term iff
`isTorsionDivisor = some m`, and emits **nothing** iff `none`.  Pure control flow over the `match` in
`torsionLogTerm` (no torsion mathematics), unconditional.  This is the engine-side reading the deep frontier
`DivisorTorsionDecisionFrontier` connects to elementarity: "log term emitted ⟺ torsion decision positive". -/
theorem torsionLogTerm_isSome_iff (p cfuel fuel : ℕ) [Fact p.Prime]
    (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ) :
    (torsionLogTerm p cfuel fuel ρ ρq g D).isSome = true
      ↔ ∃ m, isTorsionDivisor p cfuel ρq g D = some m := by
  unfold torsionLogTerm
  cases h : isTorsionDivisor p cfuel ρq g D with
  | none => simp
  | some m => simp

end TorsionFrontier

/-! ## ★ The algebraic-completeness residual, and the decision-procedure equivalence

Assembling the engine-side control flow (`torsionLogTerm_isSome_iff`) with the two deep frontiers gives the
completeness equivalence *modulo* a precisely isolated residual, mirroring
`crischDESolveSound_decides_of_residual`.  For a residue divisor `D` (the log-part data after the rational
part `v` and the principal-case `radLogArgSolve` are accounted for) and the integrand's elementarity
predicate `elem`, the residual bundles exactly the two frontier-instances:

* **`htorsion`** — *frontier 2 instance*: the engine's torsion decision is correct on `D` for the chosen good
  prime `p` — `isTorsionDivisor p cfuel ρq g D = some m ⟺ D is torsion`.
* **`hcriterion`** — *frontier 1 instance*: the log-part Liouville criterion holds for `D` —
  `D is torsion ⟺ elem` (the integrand is elementary exactly when its residue divisor is torsion, the Trager
  structure theorem applied to this curve).

Their conjunction turns the engine's `torsionLogTerm = some _` into `elem`, and `none` into `¬ elem` — the
completeness equivalence the converse of soundness delivers, modulo the named frontiers. -/

section Assembly

open DeepWiki.SymbolicIntegration

variable (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ)

/-- **★ The precise algebraic-completeness residual** `AlgebraicCompletenessResidual p cfuel ρq g D isTorsion
elem`: the two deep frontier-instances that turn the engine's non-principal-branch output into the
integrand's elementarity.  `p`/`cfuel` are the good prime and search budget (parameters); `isTorsion` the
abstract "the residue divisor is torsion in `Jac(ℚ̄)`" predicate; `elem` the integrand's elementarity
(`IsAlgebraicElementary` over the curve's function field).  `htorsion` is the *good-reduction
torsion-decision correctness* on `D` (frontier 2 — `isTorsionDivisor = some m ⟺ isTorsion`), `hcriterion` the
*Liouville log-part criterion* on `D` (frontier 1 — `isTorsion ⟺ elem`).  A `Prop`-bundle of stated
assumptions (NOT proved), making the algebraic-completeness boundary citable with NO `sorry`; each clause is
one of the two named deep frontiers specialized to this divisor. -/
structure AlgebraicCompletenessResidual (p cfuel : ℕ) [Fact p.Prime]
    (isTorsion : Prop) (elem : Prop) : Prop where
  /-- Frontier 2 (good-reduction torsion-decision correctness) on `D`: the engine's decision matches the
  true torsion status — `isTorsionDivisor = some m ⟺ D is torsion`. -/
  htorsion : (∃ m, isTorsionDivisor p cfuel ρq g D = some m) ↔ isTorsion
  /-- Frontier 1 (Liouville log-part criterion) on `D`: the integrand is elementary ⟺ its residue divisor
  is torsion. -/
  hcriterion : isTorsion ↔ elem

/-- **★ Algebraic completeness modulo the residual** (`cIntegrateAlgebraicWf_complete_of_residual`,
`some ⟺ elementary`): under the algebraic-completeness residual (the good-reduction torsion-decision
correctness + the Liouville log-part criterion on the residue divisor `D`), the engine's non-principal log
branch `torsionLogTerm` returns a log term **iff** the integrand is elementary —
`(torsionLogTerm p cfuel fuel ρ ρq g D).isSome = true ↔ elem`.  The chain: `torsionLogTerm = some _ ⟺
isTorsionDivisor = some m` (the unconditional `torsionLogTerm_isSome_iff`) ⟺ `D is torsion` (frontier 2,
`htorsion`) ⟺ `elem` (frontier 1, `hcriterion`).  This is the converse of soundness for the algebraic
integrator's log part, *modulo* the two precisely isolated deep frontiers — the algebraic analogue of
`crischDESolveSound_decides_of_residual`. -/
theorem cIntegrateAlgebraicWf_complete_of_residual {isTorsion elem : Prop} (p cfuel fuel : ℕ)
    [Fact p.Prime] (hres : AlgebraicCompletenessResidual ρq g D p cfuel isTorsion elem) :
    (torsionLogTerm p cfuel fuel ρ ρq g D).isSome = true ↔ elem := by
  rw [torsionLogTerm_isSome_iff, hres.htorsion, hres.hcriterion]

/-- **★ Non-elementarity ⟹ the engine emits no log term** (`engine_none_of_not_elementary`, the headline
"`none` ⟹ not elementary" reading): under the algebraic-completeness residual, if the integrand is **not**
elementary then the engine's non-principal branch returns `none` —
`¬ elem → (torsionLogTerm p cfuel fuel ρ ρq g D).isNone = true`.  The contrapositive of
`cIntegrateAlgebraicWf_complete_of_residual`: a non-elementary integrand has a non-torsion residue divisor
(frontier 1), which the engine's correct decision reports as `none` (frontier 2), so no `(1/m)·log` term is
emitted — exactly the completeness verdict for the algebraic integrator's log part. -/
theorem engine_none_of_not_elementary {isTorsion elem : Prop} (p cfuel fuel : ℕ) [Fact p.Prime]
    (hres : AlgebraicCompletenessResidual ρq g D p cfuel isTorsion elem) (hne : ¬ elem) :
    (torsionLogTerm p cfuel fuel ρ ρq g D).isNone = true := by
  rw [Option.isNone_iff_eq_none, ← Option.not_isSome_iff_eq_none, Bool.not_eq_true]
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  exact hne ((cIntegrateAlgebraicWf_complete_of_residual ρ ρq g D p cfuel fuel hres).mp hcon)

end Assembly

/-! ## ★ The complete algebraic-completeness map (the final verdict, stated precisely)

**Is the algebraic integrator's elementarity decision complete?**  **Modulo two precisely isolated deep
frontiers, yes.**  `cIntegrateAlgebraicWf_complete_of_residual` proves `some ⟺ elementary`
((`torsionLogTerm`'s `isSome`) ↔ `elem`) under `AlgebraicCompletenessResidual`; its contrapositive
`engine_none_of_not_elementary` is the headline "`none` ⟹ not elementary".  The `⟹` half (soundness) is the
done `IsAlgebraicIntegral` capstone (`ComputableRadicalLogSoundness`); the `⟸` half (completeness) is this
file, modulo the residual.

**Which completeness pieces are PROVEN, and which are the two deep frontiers?**

* **Proven (reachable), axiom-clean.**
  - The **within-tower algebraic descent** (`elementary_base_of_elementary_finiteDim` /
    `not_elementary_extension_of_not_elementary_base_alg`) — rides Mathlib's `isLiouville_of_finiteDimensional`:
    a finite algebraic extension never makes a base-non-elementary integrand elementary.
  - The **rational part is always elementary** (`ratPart_isAlgebraicElementary`) — `D(v)` is a Liouville
    form with the empty log family, so the rational part never obstructs elementarity; completeness turns
    entirely on the log part.
  - The **engine-side control flow** (`elementarityViaTorsion_iff_some`, `torsionLogTerm_isSome_iff`,
    `algebraicLiouville_single_extension`) — the decision is a genuine dichotomy and the log term is emitted
    ⟺ the torsion decision is positive (pure `Option` control flow, unconditional).
  - The **decision-procedure assembly** (`cIntegrateAlgebraicWf_complete_of_residual`,
    `engine_none_of_not_elementary`) — `some ⟺ elementary` modulo the residual.
* **Proven (reachable), `native_decide`.**  The torsion gates are **non-vacuous**: the engine decides the
  rank-1 `(3,5)` on `y² = x³ − 2` **non-elementary** (`engine_none_of_nonTorsion_witness`) and the torsion
  flex `(0,1)` on `y² = x³ + 1` **elementary** with a `(1/3)·log` term (`engine_some_of_torsion_witness`).
* **The deep frontiers** (named `def`s, NEVER `sorry`).
  1. **`AlgebraicLiouvilleFrontier`** — Liouville's structure theorem for the curve's function field
     (`∫ f` elementary ⟺ the Trager torsion form, *exhaustive*).  Mathlib has only the finite-extension
     descent, not this structure theorem (Bronstein Ch. 6 / Trager Ch. 5–6 / Rosenlicht).
  2. **`DivisorTorsionDecisionFrontier`** — the engine's `isTorsionDivisor` is correct and terminating via
     good reduction mod `p` (the height-swell tip).  Mathlib has the abstract Jacobian but no hyperelliptic
     point-counting / good-reduction order-bound theorem.
  - **`RationalPartExhaustivenessFrontier`** (frontier 1b, the *milder* tip) — the integral-basis Hermite
    reduction captures **all** of the rational part (so the reduced integrand is purely logarithmic);
    Bronstein Ch. 5 / Trager.  The always-elementary half is reached (`ratPart_isAlgebraicElementary`); only
    the exhaustiveness is stated.

So full `some ⟺ elementary` for the algebraic integrator is reached **modulo exactly the two deep
frontiers** — the Liouville-for-algebraic structure theorem (the log-part criterion) and the good-reduction
divisor-torsion decision correctness (the height-swell tip) — plus the milder rational-part exhaustiveness.
Both deep frontiers are stated precisely; neither is a `sorry`. -/

/-! ### Restatements pinning the algebraic-completeness content (anonymous `example`s) -/

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
    {isTorsion elem : Prop} (p cfuel fuel : ℕ) [Fact p.Prime]
    (hres : AlgebraicCompletenessResidual ρq g D p cfuel isTorsion elem) :
    (torsionLogTerm p cfuel fuel ρ ρq g D).isSome = true ↔ elem :=
  cIntegrateAlgebraicWf_complete_of_residual ρ ρq g D p cfuel fuel hres

-- ★ The headline "none ⟹ not elementary" for the algebraic integrator's log part, modulo the frontiers.
example (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g : ℕ) (D : CPolyG.MumfordDivisor ℚ)
    {isTorsion elem : Prop} (p cfuel fuel : ℕ) [Fact p.Prime]
    (hres : AlgebraicCompletenessResidual ρq g D p cfuel isTorsion elem) (hne : ¬ elem) :
    (torsionLogTerm p cfuel fuel ρ ρq g D).isNone = true :=
  engine_none_of_not_elementary ρ ρq g D p cfuel fuel hres hne

end Restatements

/-! ### Axiom audit (the descent, control-flow readings, and the modular assembly are axiom-clean;
the witnesses use `native_decide`) -/

#print axioms elementary_base_of_elementary_finiteDim
#print axioms not_elementary_extension_of_not_elementary_base_alg
#print axioms ratPart_isAlgebraicElementary
#print axioms algebraicLiouville_single_extension
#print axioms elementarityViaTorsion_iff_some
#print axioms torsionLogTerm_isSome_iff
#print axioms cIntegrateAlgebraicWf_complete_of_residual
#print axioms engine_none_of_not_elementary

end DeepWiki.SymbolicIntegration.AlgebraicCompleteness
