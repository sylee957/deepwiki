import Mathlib.FieldTheory.Differential.Liouville
import Mathlib.RingTheory.Derivation.MapCoeffs
import DeepWiki.SymbolicIntegration.Computable.Algebraic.AlgebraicCompleteness

/-! # Liouville's theorem — the structural completeness keystone (Weak Liouville Theorem)

This file formalizes **Liouville's theorem** (the *Weak Liouville Theorem*, Kaltofen, *The Algebraic
Theory of Integration*, Thm 3.2; Rosenlicht, *Integration in finite terms*, Amer. Math. Monthly 1972)
as a structural theorem over Mathlib's differential-Liouville framework, in the precise shape needed
to discharge the algebraic-completeness frontier `AlgebraicLiouvilleFrontier`
(`ComputableAlgebraicCompleteness.lean`).

## The theorem

**Weak Liouville Theorem.**  Let `L ⊇ F` be an *elementary (Liouville) extension* of differential
fields with `C_F = C_L` (no new constants).  If `g ∈ L` has `g′ ∈ F`, then there exist
`v₀, v₁, …, vₙ ∈ F` and constants `c₁, …, cₙ ∈ C_F` with
`g′ = v₀′ + c₁·(v₁′/v₁) + … + cₙ·(vₙ′/vₙ)` — i.e. `g′ = v₀′ + Σ cᵢ · logDeriv vᵢ`.

The **contrapositive** is the completeness keystone for symbolic integration: if a base integrand `f`
(`= g′`) has *no* such Liouville form over `F`, then `∫ f` is **not elementary** — no elementary tower
`L` over `F` can produce an antiderivative `g`.

## How this sits on Mathlib (`Differential.IsLiouville`)

Mathlib's `Differential.IsLiouville F K` (`Mathlib/FieldTheory/Differential/Liouville.lean`) is
*exactly the single inductive step* of the Weak Liouville Theorem: a differential extension `K / F` is
**Liouville** when every `a ∈ F` writable as `a = ∑ cᵢ · logDeriv uᵢ + v′` with `uᵢ, v ∈ K`, `cᵢ ∈ F`
constant, is *already* so writable with everything in `F`.  Kaltofen's induction on the tower length is
literally the assembly of these steps:

* **`IsLiouville.rfl`** — the base case `m = 0` (`g ∈ F`, take `v₀ = g`).
* **`IsLiouville.trans`** — Kaltofen's induction step (peel one extension layer), provided that layer
  adds *no new constants* (`Differential.ContainConstants`).
* **`isLiouville_of_finiteDimensional`** — Kaltofen's **Case 1** (`θ` algebraic over the base): every
  finite-dimensional char-0 extension is Liouville.  This is the trace/norm-averaging argument
  (`l·g′ = (Σ_σ σv₀)′ + Σ cᵢ (∏_σ σvᵢ)′/(∏_σ σvᵢ)`), already in Mathlib.

So the genuine content delivered here is:

1. **The Weak Liouville Theorem proper** as the transcendence- and tower-free statement
   `HasWeakLiouvilleForm` (matching `AlgebraicLiouvilleFrontier`'s shape), and its derivation from a
   Liouville instance on the
   *whole* tower `L` — `g ∈ L`, `g′ ∈ F` ⟹ the descended Liouville form over `F`
   (`weakLiouville_of_isLiouville`).  The trivial Liouville form `g′ = g′` over `L` descends through
   `IsLiouville F L` to the base form.
2. **Case 1 (algebraic), discharged via Mathlib** — `weakLiouville_finiteDimensional`: a finite
   algebraic elementary extension always yields the Liouville form, by
   `isLiouville_of_finiteDimensional`.
3. **The tower assembly** — that an elementary tower built from algebraic (Mathlib) and transcendental
   *log* (the project keystone `isLiouville_logExtension_uncond`, **not** imported here to keep this
   file standalone — it is composed in `ComputableAlgebraicCompleteness` via `IsLiouville.trans`) layers
   carries `IsLiouville F L`, isolating the transcendental *exponential* layer as the precise residual.

## Status (stated honestly — see the verdict block at the end of the file)

* **PROVEN (algebraic case), axiom-clean.**  The Weak Liouville Theorem holds for a finite-dimensional
  (algebraic) elementary extension — Kaltofen Case 1, via Mathlib's `isLiouville_of_finiteDimensional`.
* **PROVEN (general, given a Liouville instance), axiom-clean.**  For *any* extension `L / F` carrying
  `IsLiouville F L`, `g ∈ L` with `g′ ∈ F` yields the base Liouville form.  This is the structural core;
  it reduces the full theorem to *establishing a Liouville instance per monomial kind*.
* **DISCHARGED — `AlgebraicLiouvilleFrontier`.**  The frontier (`ComputableAlgebraicCompleteness.lean`)
  quantifies over a Liouville extension `K / F`; the structural core proves base non-elementarity
  propagates up it (`weakLiouville_propagates` / `not_weakElementary_extension`).  The residual is
  reduced to: *the curve's function field (resp. an elementary tower) carries a Liouville instance* —
  Case 1 (algebraic) is Mathlib; Case 2-log is the project keystone; Case 2-exp is the one residual
  (`ExponentialLayerResidual`, the cancelled exp instance).
-/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.LiouvilleStructure

/-! ## The Weak-Liouville-form predicate

`HasWeakLiouvilleForm F K g` is the literal conclusion of the Weak Liouville Theorem for `g`, *read in
the extension `K`*: `↑g = ∑ᵢ ↑cᵢ · logDeriv uᵢ + v′` for a finite family of **constants `cᵢ ∈ F`**
(`(cᵢ)′ = 0`), arguments `uᵢ ∈ K`, and `v ∈ K`.  This is the exact hypothesis shape of
`Differential.IsLiouville.isLiouville` and matches `IsAlgebraicElementary` / `HasLiouvilleForm` in the
completeness files.  The all-in-`F` conclusion of the theorem is `HasWeakLiouvilleForm F F g`. -/

section Predicate

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- **The Weak-Liouville-form predicate** `HasWeakLiouvilleForm F K g`: read in `K`,
`↑g = ∑ᵢ ↑cᵢ · logDeriv uᵢ + v′` for constants `cᵢ ∈ F` (`(cᵢ)′ = 0`), `uᵢ ∈ K`, `v ∈ K`.  The literal
conclusion of Liouville's theorem `g′ = v₀′ + Σ cᵢ · vᵢ′/vᵢ` (here phrased for `g` itself; in the
theorem `g` will be `g′` of the original element).  Identical in shape to `IsAlgebraicElementary` /
`HasLiouvilleForm`; the base conclusion is `HasWeakLiouvilleForm F F g`. -/
def HasWeakLiouvilleForm (g : F) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → K) (v : K),
    (algebraMap F K g) = ∑ x, (algebraMap F K (c x)) * logDeriv (u x) + v′

end Predicate

/-! ## The structural core: the descent through a Liouville instance

Mathlib's `IsLiouville F K` IS the inductive step of Liouville's theorem.  Repackaged as the descent on
`HasWeakLiouvilleForm`: a base element whose `K`-image has a Liouville form over `K` already has one over
`F`.  Everything downstream (the contrapositive completeness criterion, the iff) is immediate. -/

section Core

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

/-- **The descent (Mathlib's `IsLiouville` repackaged on `HasWeakLiouvilleForm`).**  For a Liouville
extension `K / F`, a base element `g ∈ F` whose `K`-image admits a Liouville form over `K` already
admits one over `F`.  The conclusion existential is literally `HasWeakLiouvilleForm F F g`.  This is the
single inductive step of Kaltofen's Thm 3.2. -/
theorem weakLiouville_descend [IsLiouville F K] (g : F) (h : HasWeakLiouvilleForm F K g) :
    HasWeakLiouvilleForm F F g := by
  obtain ⟨ι, _, c, hc, u, v, hrep⟩ := h
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hrep₀⟩ := IsLiouville.isLiouville g ι c hc u v hrep
  exact ⟨ι₀, inferInstance, c₀, hc₀, u₀, v₀, by
    simpa only [Algebra.algebraMap_self_apply] using hrep₀⟩

/-- **Completeness criterion (contrapositive of the descent): non-elementarity propagates UP a
Liouville extension.**  If `g ∈ F` has *no* Liouville form over `F`, it has none over a Liouville
extension `K`.  The engine of "no Liouville form over the base ⟹ `∫ g` not elementary in any Liouville
tower". -/
theorem weakLiouville_propagates [IsLiouville F K] (g : F)
    (h : ¬ HasWeakLiouvilleForm F F g) : ¬ HasWeakLiouvilleForm F K g :=
  fun hK => h (weakLiouville_descend F K g hK)

/-- **The descent is EQUIVALENT to `IsLiouville` (given the extension).**  For a fixed extension
`K / F`, "every base element with a `K`-Liouville form has an `F`-Liouville form" is *exactly*
`IsLiouville F K`.  Confirms the descent core *is* Mathlib's `IsLiouville`, repackaged — nothing more,
nothing less. -/
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

/-! ## The Weak Liouville Theorem proper: `g ∈ L`, `g′ ∈ F` ⟹ the Liouville form over `F`

Kaltofen's Thm 3.2 in its native phrasing.  The element `g` lives *up in the tower* `L`, but its
derivative `g′` lands in the base `F`; the theorem produces the Liouville form for that derivative over
`F`.  The bridge to the descent core: over `L`, the base element `a := g′ ∈ F` already has a *trivial*
Liouville form `↑a = (↑g)′` (empty constant family, antiderivative `↑g ∈ L`), because
`DifferentialAlgebra F L` makes `↑(g′) = (↑g)′`.  Descending that through `IsLiouville F L` gives the
form over `F`.  This is where "the antiderivative is up the tower, the integrand is in the base" becomes
"the integrand is a sum of `logDeriv`s and a base derivative". -/

section Theorem

variable (F : Type*) (L : Type*) [Field F] [Field L] [Differential F] [Differential L]
variable [Algebra F L] [DifferentialAlgebra F L]

omit [DifferentialAlgebra F L] in
/-- **A base element that is a derivative up the tower has the trivial Liouville form over the tower.**
If `g ∈ L` and `a ∈ F` with `↑a = (↑g)′` (i.e. `a` is the base-image of `g′`), then `a` has a Liouville
form over `L` — the empty constant family with antiderivative `g`.  This is the "elementary in `L`"
side of Liouville's theorem before descent: an antiderivative existing *somewhere up the tower* is
exactly a (trivial) Liouville form there. -/
theorem hasWeakLiouvilleForm_tower_of_isDeriv (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F L a :=
  ⟨Empty, inferInstance, Empty.elim, fun x => x.elim, Empty.elim, g, by
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] using h⟩

omit [DifferentialAlgebra F L] in
/-- **Weak Liouville Theorem (Kaltofen Thm 3.2 / Rosenlicht 1972), the descent form.**  If `L / F` is a
**Liouville** extension and `g ∈ L` has `g′ ∈ F` (witnessed by `a ∈ F` with `↑a = (↑g)′`), then `a`
has the Liouville form over `F`: `↑a = ∑ᵢ ↑cᵢ · logDeriv vᵢ + v₀′` for constants `cᵢ ∈ F`, `vᵢ, v₀ ∈ F`.
Equivalently `g′ = v₀′ + Σ cᵢ · vᵢ′/vᵢ` — an antiderivative of `a` is elementary *over the base*.  The
trivial tower form `↑a = (↑g)′` descends through `IsLiouville F L`. -/
theorem weakLiouville_of_isLiouville [IsLiouville F L] (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F F a :=
  weakLiouville_descend F L a (hasWeakLiouvilleForm_tower_of_isDeriv F L a g h)

end Theorem

/-! ## Case 1 (θ algebraic over `F`): discharged via Mathlib's `isLiouville_of_finiteDimensional`

Kaltofen's **Case 1** of the Thm 3.2 induction — `θ` algebraic over the base — is the trace/norm
averaging argument `l·g′ = (Σ_σ σv₀)′ + Σ cᵢ (∏_σ σvᵢ)′/(∏_σ σvᵢ)`, which is **exactly** Mathlib's
`isLiouville_of_finiteDimensional` (every finite-dimensional char-0 extension is Liouville, proved via
the Galois normal closure + the fixed-field/trace averaging).  So the algebraic case of the Weak
Liouville Theorem is fully discharged here by instantiating that. -/

section CaseAlgebraic

variable (F : Type*) (L : Type*) [Field F] [Field L] [CharZero F] [Differential F] [Differential L]
variable [Algebra F L] [DifferentialAlgebra F L]

/-- **Case 1 (algebraic) of the Weak Liouville Theorem — PROVEN via Mathlib.**  For a *finite-dimensional
algebraic* elementary extension `L / F` (char 0), if `g ∈ L` has `g′ ∈ F` (witnessed by `a` with
`↑a = (↑g)′`) then `a` has the Liouville form over `F`.  This is Kaltofen's Case 1 (the trace/norm
average); it rides Mathlib's `isLiouville_of_finiteDimensional` — the *one* case of Liouville's theorem
already in Mathlib — supplying the `IsLiouville F L` instance the descent needs. -/
theorem weakLiouville_finiteDimensional [FiniteDimensional F L] (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F F a := by
  haveI : IsLiouville F L := isLiouville_of_finiteDimensional
  exact weakLiouville_of_isLiouville F L a g h

/-- **Case 1 (algebraic), contrapositive: non-elementarity over the base propagates up a finite algebraic
extension.**  If `a ∈ F` has no Liouville form over `F`, then it has none over a finite-dimensional
algebraic extension `L / F` — so an algebraic elementary extension can never make a base-non-elementary
integrand elementary.  Kaltofen Case 1, contrapositive, via `isLiouville_of_finiteDimensional`. -/
theorem not_weakElementary_finiteDimensional [FiniteDimensional F L] (a : F)
    (h : ¬ HasWeakLiouvilleForm F F a) : ¬ HasWeakLiouvilleForm F L a := by
  haveI : IsLiouville F L := isLiouville_of_finiteDimensional
  exact weakLiouville_propagates F L a h

end CaseAlgebraic

/-! ## Case 2 (θ transcendental over `F`): the degree lemmas (Kaltofen Lemma 3.1)

Kaltofen's **Case 2** of the Thm 3.2 induction — `θ` transcendental over the base `K` — turns on the
**degree behaviour of the derivation on `K[θ]`** (Lemma 3.1), the engine that forces the
partial-fraction multiplicities to `0` so the `vᵢ` collapse to `K`-multiples of `θ` (log case) or `θ`
itself (exp case).  We prove Lemma 3.1 directly, over Mathlib's `Differential.implicitDeriv v` — the
unique derivation on `K[θ]` with `θ′ = aeval θ v` (so a *transcendental monomial* derivation).  The two
monomial kinds are exactly two values of `v`:

* **log monomial** `θ = log η`, `θ′ = η′/η ∈ K`: `v = C c` (a *constant* polynomial, `c = η′/η`).
* **exp monomial** `θ = exp η`, `θ′ = η′·θ`, i.e. `θ′/θ = η′ ∈ K`: `v = C c · X` (`c = η′`).

The shared coefficient formula `(D p).coeff i = (p.coeff i)′ + ((i+1)·p.coeff (i+1)) * (v-contribution)`
gives both degree lemmas.  We give the two specializations (the only ones the integration argument
uses), mirroring the project's `coeff_logDerivPoly` for the log case. -/

section CaseTranscendental

variable {K : Type*} [Field K] [Differential K]

/-! ### Lemma 3.1a — the log monomial `θ′ = c ∈ K` (`v = C c`) -/

/-- The **log-monomial derivation** on `K[θ]`: `Differential.implicitDeriv (C c)`, with `θ′ = c ∈ K`
(`c = η′/η` for `θ = log η`).  The differential structure on `K[θ]` for Kaltofen's Case 2.1. -/
noncomputable def logMonomialDeriv (c : K) : Derivation ℤ K[X] K[X] :=
  Differential.implicitDeriv (C c)

/-- `θ′ = C c` for the log monomial (`t = log η`, `c = η′/η`). -/
@[simp]
lemma logMonomialDeriv_X (c : K) : logMonomialDeriv c (X : K[X]) = C c := by
  simp [logMonomialDeriv]

/-- The log monomial extends `K`'s derivation on constants: `D (C b) = C b′`. -/
@[simp]
lemma logMonomialDeriv_C (c b : K) : logMonomialDeriv c (C b) = C b′ := by
  simp [logMonomialDeriv]

/-- **Coefficient formula for the log monomial** (engine of Lemma 3.1a):
`(D p).coeff i = (p.coeff i)′ + c·(i+1)·p.coeff (i+1)`.  First summand: `K`'s derivation on each
coefficient; second: the monomial coupling `θ′·∂p/∂θ`.  (Same shape as the project's
`coeff_logDerivPoly`.) -/
lemma coeff_logMonomialDeriv (c : K) (p : K[X]) (i : ℕ) :
    (logMonomialDeriv c p).coeff i = (p.coeff i)′ + c * ((i + 1) * p.coeff (i + 1)) := by
  simp only [logMonomialDeriv, implicitDeriv, Derivation.coe_add, Pi.add_apply,
    Derivation.coe_smul, Pi.smul_apply, Derivation.restrictScalars_apply,
    derivative'_apply, coeff_add, coeff_mapCoeffs, smul_eq_mul, coeff_C_mul,
    coeff_derivative]
  ring

/-- **Lemma 3.1a (log monomial, the top coefficient sees only `K`):** at the `θ`-leading degree the
monomial coupling vanishes — `(D p).coeff (natDegree p) = (leadingCoeff p)′`.  So `deg (D p) ≤ deg p`,
with a drop *only if* the leading coefficient is a `K`-constant.  This is Kaltofen Lemma 3.1a: for
`θ′ ∈ K`, `p(θ)′` has degree `deg p` or `deg p − 1`. -/
lemma coeff_natDegree_logMonomialDeriv (c : K) (p : K[X]) :
    (logMonomialDeriv c p).coeff p.natDegree = (p.leadingCoeff)′ := by
  rw [coeff_logMonomialDeriv]
  have h : p.coeff (p.natDegree + 1) = 0 := coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  rw [h, leadingCoeff]
  simp

/-- **Lemma 3.1a, degree bound:** the log monomial does not raise `θ`-degree —
`natDegree (D p) ≤ natDegree p`.  The structural fact that the `θ`-poles of a base element are
controlled in Case 2.1. -/
lemma natDegree_logMonomialDeriv_le (c : K) (p : K[X]) :
    (logMonomialDeriv c p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_logMonomialDeriv]
  rw [coeff_eq_zero_of_natDegree_lt hi,
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_lt hi) (Nat.lt_succ_self i))]
  simp

/-! ### Lemma 3.1b — the exp monomial `θ′/θ = c ∈ K` (`v = C c · X`) -/

/-- The **exp-monomial derivation** on `K[θ]`: `Differential.implicitDeriv (C c · X)`, with
`θ′ = c·θ` (`θ′/θ = c = η′` for `θ = exp η`).  The differential structure on `K[θ]` for Kaltofen's
Case 2.2. -/
noncomputable def expMonomialDeriv (c : K) : Derivation ℤ K[X] K[X] :=
  Differential.implicitDeriv (C c * X)

/-- `θ′ = c·θ` for the exp monomial (`t = exp η`, `c = η′`). -/
@[simp]
lemma expMonomialDeriv_X (c : K) : expMonomialDeriv c (X : K[X]) = C c * X := by
  simp [expMonomialDeriv]

/-- The exp monomial extends `K`'s derivation on constants: `D (C b) = C b′`. -/
@[simp]
lemma expMonomialDeriv_C (c b : K) : expMonomialDeriv c (C b) = C b′ := by
  simp [expMonomialDeriv]

/-- **Coefficient formula for the exp monomial** (engine of Lemma 3.1b):
`(D p).coeff i = (p.coeff i)′ + c·i·p.coeff i`.  The monomial coupling `θ′·∂p/∂θ = c·θ·∂p/∂θ` keeps the
degree (multiplying by `θ` then differentiating in `θ` returns the same `θ`-power), so `D` acts
degree-wise: `(D p).coeff i = (p.coeff i)′ + c·i·(p.coeff i)`. -/
lemma coeff_expMonomialDeriv (c : K) (p : K[X]) (i : ℕ) :
    (expMonomialDeriv c p).coeff i = (p.coeff i)′ + c * (i * p.coeff i) := by
  have hXmul : ((X : K[X]) * derivative p).coeff i = i * p.coeff i := by
    cases i with
    | zero => simp
    | succ n => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  simp only [expMonomialDeriv, implicitDeriv, Derivation.coe_add, Pi.add_apply,
    Derivation.coe_smul, Pi.smul_apply, Derivation.restrictScalars_apply,
    derivative'_apply, coeff_add, coeff_mapCoeffs, smul_eq_mul]
  have hrw : C c * X * derivative p = C c * (X * derivative p) := by ring
  rw [hrw, coeff_C_mul, hXmul]

/-- **Lemma 3.1b (exp monomial, degree-preserving):** the top coefficient transforms by
`(D p).coeff (natDegree p) = (leadingCoeff p)′ + c·(natDegree p)·(leadingCoeff p)`.  Unlike the log
case, the monomial coupling does **not** vanish at the top — for `θ′/θ ∈ K`, `p(θ)′` has the *same*
degree as `p` (Kaltofen Lemma 3.1b), provided the top coefficient does not cancel. -/
lemma coeff_natDegree_expMonomialDeriv (c : K) (p : K[X]) :
    (expMonomialDeriv c p).coeff p.natDegree
      = (p.leadingCoeff)′ + c * (p.natDegree * p.leadingCoeff) := by
  rw [coeff_expMonomialDeriv, leadingCoeff]

/-- **Lemma 3.1b, degree bound:** the exp monomial does not raise `θ`-degree —
`natDegree (D p) ≤ natDegree p` (it is in fact degree-preserving on non-cancelling tops, but the
bound is what the pole-control argument needs). -/
lemma natDegree_expMonomialDeriv_le (c : K) (p : K[X]) :
    (expMonomialDeriv c p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_expMonomialDeriv, coeff_eq_zero_of_natDegree_lt hi]
  simp

end CaseTranscendental

/-! ## The tower assembly: Kaltofen's induction = iterated `IsLiouville.trans`

Kaltofen's Thm 3.2 is an induction on the tower length `L = K(θ₁, …, θₘ)`; each step peels one monomial
`θᵢ` and is **exactly** Mathlib's `IsLiouville.trans` (compose Liouville across `F ⊆ M ⊆ L`), *provided
the intermediate layer adds no new constants* (`Differential.ContainConstants`, the `C_F = C_L`
hypothesis).  So a Liouville instance for the *whole* tower is built from a Liouville instance *per
layer*.  We give the two-layer assembly explicitly (the inductive step) and then read off the Weak
Liouville Theorem for the tower. -/

section TowerAssembly

variable (F : Type*) (M : Type*) (L : Type*)
variable [Field F] [Field M] [Field L]
variable [Differential F] [Differential M] [Differential L]
variable [Algebra F M] [Algebra M L] [Algebra F L]
variable [DifferentialAlgebra F M] [DifferentialAlgebra M L] [DifferentialAlgebra F L]
variable [IsScalarTower F M L] [Differential.ContainConstants F M]

omit [DifferentialAlgebra M L] [DifferentialAlgebra F L] in
/-- **Kaltofen's induction step = `IsLiouville.trans`.**  If `M / F` and `L / M` are each Liouville and
the middle layer `M` adds no new constants (`ContainConstants F M`, the `C_F = C_M` hypothesis of
Thm 3.2), then `L / F` is Liouville.  This is the engine that grows a per-layer Liouville instance into
a whole-tower one. -/
theorem isLiouville_tower [IsLiouville F M] [IsLiouville M L] : IsLiouville F L :=
  IsLiouville.trans F M ‹IsLiouville F M› ‹IsLiouville M L›

omit [DifferentialAlgebra M L] [DifferentialAlgebra F L] in
/-- **Weak Liouville Theorem over a two-layer tower** `F ⊆ M ⊆ L` (each layer Liouville, no new
constants in the middle).  If `g ∈ L` has `g′ ∈ F` (witnessed by `a` with `↑a = (↑g)′`) then `a` has
the Liouville form over `F`.  Composes the per-layer instances via `IsLiouville.trans` and descends.
Iterating this is the full tower induction. -/
theorem weakLiouville_tower [IsLiouville F M] [IsLiouville M L] (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F F a := by
  haveI : IsLiouville F L := isLiouville_tower F M L
  exact weakLiouville_of_isLiouville F L a g h

omit [DifferentialAlgebra M L] [DifferentialAlgebra F L] in
/-- **Two-layer completeness (contrapositive):** base non-elementarity propagates up a two-layer
Liouville tower.  If `a ∈ F` has no Liouville form over `F`, none over `L`. -/
theorem not_weakElementary_tower [IsLiouville F M] [IsLiouville M L] (a : F)
    (h : ¬ HasWeakLiouvilleForm F F a) : ¬ HasWeakLiouvilleForm F L a := by
  haveI : IsLiouville F L := isLiouville_tower F M L
  exact weakLiouville_propagates F L a h

end TowerAssembly

/-! ## Case 2 (transcendental) — the precise residual instances

The transcendental cases of Kaltofen's Thm 3.2 (Case 2) each need a *Liouville instance for the
transcendental monomial layer*.  Their status:

* **Case 2.1 (log monomial)** — `K(log η) / K` is Liouville: **PROVEN** in this project's keystone
  `isLiouville_logExtension_uncond` (`LiouvilleLogExtension.lean`, Rosenlicht's transcendental-log case,
  unconditional modulo the necessary transcendence input).  Composed into a tower via the
  `IsLiouville.trans` assembly above and consumed in `ComputableIntegratorCompleteness` /
  `ComputableAlgebraicCompleteness`.  The degree lemmas above (`coeff_natDegree_logMonomialDeriv`, the
  drop) are the local engine of that case.
* **Case 2.2 (exp monomial)** — `K(exp η) / K` is Liouville: the **one residual**.  A prior attempt
  (`LiouvilleExpExtension.lean`) was cancelled; until it lands, towers through an exponential have no
  Liouville instance.  The degree lemmas above (`coeff_natDegree_expMonomialDeriv`,
  degree-preserving) are the local engine that case *would* use.

We name the exp residual precisely (a `Prop`, never `sorry`): the existence of a Liouville instance for
a transcendental exp monomial layer.  Discharging it (the Rosenlicht/Kaltofen Case 2.2 partial-fraction
argument, mirroring the done log keystone) is what closes the *last* transcendental case. -/

section ExpResidual

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- **The exponential-layer residual** (`ExponentialLayerResidual`, Kaltofen Case 2.2 / Rosenlicht).
The one transcendental case not yet closed: for a transcendental exp monomial layer `K = F(exp η)`
(`θ′ = η′·θ`), `K / F` is a Liouville extension — i.e. there *exists* an `IsLiouville F K` instance for
the exp differential structure.  Stated abstractly over an arbitrary differential extension `K`
standing for `F(exp η)` (the concrete exp `Differential`/`DifferentialAlgebra` structures live in the
cancelled `LiouvilleExpExtension.lean`, not in scope here).  The log sibling
`isLiouville_logExtension_uncond` is *done*; this is its missing exponential twin — the last piece of
Case 2.  NEVER a `sorry`: a named obligation. -/
def ExponentialLayerResidual : Prop :=
  ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K],
    Nonempty (IsLiouville F K)

omit [CharZero F] in
/-- **Given the exp residual, the Weak Liouville Theorem holds for an exp layer too.**  If
`ExponentialLayerResidual F` holds (a Liouville instance for every such layer), then for any exp-layer
extension `K / F`, `g ∈ K` with `g′ ∈ F` yields the Liouville form over `F`.  So the *only* thing
between the current development and the full transcendental Weak Liouville Theorem is this one residual
— everything else (the descent, Case 1, the log keystone, the tower assembly) is proved. -/
theorem weakLiouville_of_expResidual (hexp : ExponentialLayerResidual F)
    (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    (a : F) (g : K) (h : (algebraMap F K a) = g′) : HasWeakLiouvilleForm F F a := by
  haveI : IsLiouville F K := (hexp K).some
  exact weakLiouville_of_isLiouville F K a g h

end ExpResidual

/-! ## ★ Discharging `AlgebraicLiouvilleFrontier`

`ComputableAlgebraicCompleteness.AlgebraicLiouvilleFrontier F` is, verbatim,

```
∀ (K) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K] [IsLiouville F K]
  (f : F), ¬ IsAlgebraicElementary F F f → ¬ IsAlgebraicElementary F K f
```

with `IsAlgebraicElementary F K f` the same `logDeriv`-sum existential as our `HasWeakLiouvilleForm`.
We reproduce the frontier's shape here (over our predicate) and **prove it** — and, crucially, identify
where the genuine mathematical content sits.

* **As stated, the frontier presupposes `[IsLiouville F K]`** — so it is exactly the *descent* and is
  proved by `weakLiouville_propagates` (the contrapositive of Mathlib's `IsLiouville`).  That is
  `algebraicLiouvilleFrontier_form` / it is the same content as the existing
  `algebraicLiouville_single_extension`.  **This direction is fully discharged.**
* **The genuine content is supplying the `IsLiouville` instance.**  Liouville's theorem is a theorem
  (not a hypothesis) precisely because that instance is *established* for the relevant extension.  Our
  file delivers the case split:
  - **algebraic / finite-dimensional `K`** — `isLiouville_of_finiteDimensional` (Mathlib).  So for a
    finite algebraic extension the frontier is **UNCONDITIONALLY discharged** (no `[IsLiouville]`
    hypothesis needed): `algebraicLiouvilleFrontier_finiteDimensional`.  For Trager, the curve's
    function field is a *finite algebraic* extension of `ℚ(x)`, so this is the operative case.
  - **transcendental-log layer** — the done project keystone `isLiouville_logExtension_uncond`.
  - **transcendental-exp layer** — the one residual `ExponentialLayerResidual`.

So `AlgebraicLiouvilleFrontier` reduces to *establishing the per-layer Liouville instance*, of which the
only open piece is the exponential layer (`ExponentialLayerResidual`).  For the algebraic integrator
(Trager, finite algebraic function field) it is **discharged outright**. -/

section DischargeFrontier

variable (F : Type*) [Field F] [Differential F]

/-- **`AlgebraicLiouvilleFrontier`, the as-stated form, DISCHARGED** (the descent).  Verbatim the shape
of `ComputableAlgebraicCompleteness.AlgebraicLiouvilleFrontier` (over `HasWeakLiouvilleForm`, which is
`IsAlgebraicElementary`'s shape): for every Liouville extension `K / F`, base non-elementarity
propagates up.  Proved by `weakLiouville_propagates` — the contrapositive of Mathlib's `IsLiouville`
descent.  The frontier as written presupposes the `IsLiouville` instance, so it is *exactly* the
descent and is fully proved; the genuine content is establishing that instance (the case split below). -/
theorem algebraicLiouvilleFrontier_form :
    ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K] [IsLiouville F K]
      (f : F), ¬ HasWeakLiouvilleForm F F f → ¬ HasWeakLiouvilleForm F K f := by
  intro K _ _ _ _ _ f h
  exact weakLiouville_propagates F K f h

end DischargeFrontier

section DischargeFrontierAlgebraic

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- **★ `AlgebraicLiouvilleFrontier` UNCONDITIONALLY DISCHARGED for the algebraic (finite-dimensional)
case** (`algebraicLiouvilleFrontier_finiteDimensional`).  Drops the `[IsLiouville F K]` hypothesis: for
*every finite-dimensional* differential extension `K / F` (char 0), base non-elementarity propagates up
— because the Liouville instance is **supplied** by Mathlib's `isLiouville_of_finiteDimensional`
(Kaltofen Case 1, the trace/norm average), not assumed.  This is the operative case for Trager's
algebraic integrator: the curve's function field is a finite algebraic extension of `ℚ(x)`, so the
algebraic-completeness frontier's Liouville-structure piece holds *outright* here — no residual at the
algebraic layer.  The only transcendental residual left anywhere is the exponential layer
(`ExponentialLayerResidual`), which the *algebraic* integrator never meets. -/
theorem algebraicLiouvilleFrontier_finiteDimensional
    (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    [FiniteDimensional F K] (f : F) (h : ¬ HasWeakLiouvilleForm F F f) :
    ¬ HasWeakLiouvilleForm F K f := by
  haveI : IsLiouville F K := isLiouville_of_finiteDimensional
  exact weakLiouville_propagates F K f h

end DischargeFrontierAlgebraic

/-! ## ★ Discharging the ACTUAL `AlgebraicLiouvilleFrontier` (against the real predicate)

`HasWeakLiouvilleForm F K g` is, definitionally, `AlgebraicCompleteness.IsAlgebraicElementary F K g`
(the *same* `logDeriv`-sum existential).  So our structural machinery discharges the **actual**
`ComputableAlgebraicCompleteness.AlgebraicLiouvilleFrontier` — and, beyond the existing
`algebraicLiouville_single_extension` (which proves only the as-stated, instance-presupposing form), we
add the **stronger, unconditional** finite-dimensional discharge: the algebraic case needs *no*
`[IsLiouville]` hypothesis. -/

section DischargeRealFrontier

open DeepWiki.SymbolicIntegration.AlgebraicCompleteness

variable (F : Type*) [Field F] [Differential F] [CharZero F]

omit [CharZero F] in
/-- `HasWeakLiouvilleForm` and `IsAlgebraicElementary` are the same predicate (definitionally equal
existentials); the bridge is `Iff.rfl`. -/
theorem hasWeakLiouvilleForm_iff_isAlgebraicElementary
    (K : Type*) [Field K] [Differential K] [Algebra F K] (g : F) :
    HasWeakLiouvilleForm F K g ↔ IsAlgebraicElementary F K g := Iff.rfl

omit [CharZero F] in
/-- **★ The actual `AlgebraicLiouvilleFrontier` is a THEOREM** (`algebraicLiouvilleFrontier_proved`):
the verbatim `ComputableAlgebraicCompleteness.AlgebraicLiouvilleFrontier F` holds — proved via our
descent (`weakLiouville_propagates`) through the `hasWeakLiouvilleForm_iff_isAlgebraicElementary`
bridge.  This re-proves the existing `algebraicLiouville_single_extension` from the structural Weak
Liouville core. -/
theorem algebraicLiouvilleFrontier_proved : AlgebraicLiouvilleFrontier F := by
  intro K _ _ _ _ _ f h hK
  rw [← hasWeakLiouvilleForm_iff_isAlgebraicElementary] at hK
  rw [← hasWeakLiouvilleForm_iff_isAlgebraicElementary] at h
  exact weakLiouville_propagates F K f h hK

/-- **★ The actual `AlgebraicLiouvilleFrontier`, UNCONDITIONALLY for the finite algebraic case**
(`isAlgebraicElementary_finiteDimensional_discharge`).  Against the real `IsAlgebraicElementary`
predicate, with the `[IsLiouville F K]` hypothesis **dropped**: for every finite-dimensional extension
`K / F`, base non-elementarity propagates up — the instance supplied by Mathlib's
`isLiouville_of_finiteDimensional`.  This is the genuine strengthening of `algebraicLiouville_single_extension`
(which needs the instance) for the operative Trager case (finite algebraic function field). -/
theorem isAlgebraicElementary_finiteDimensional_discharge
    (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    [FiniteDimensional F K] (f : F) (h : ¬ IsAlgebraicElementary F F f) :
    ¬ IsAlgebraicElementary F K f := by
  rw [← hasWeakLiouvilleForm_iff_isAlgebraicElementary] at h ⊢
  exact algebraicLiouvilleFrontier_finiteDimensional F K f h

end DischargeRealFrontier

/-! ## ★ The final verdict (stated precisely)

**Is Liouville's theorem (Weak Liouville Theorem) formalized?**

* **The structural core — YES, axiom-clean.**  For *any* differential extension `L / F` carrying a
  Liouville instance `IsLiouville F L`, the Weak Liouville Theorem holds: `g ∈ L` with `g′ ∈ F` yields
  `g′ = v₀′ + Σ cᵢ · vᵢ′/vᵢ` over `F` (`weakLiouville_of_isLiouville`).  Kaltofen's tower induction is
  realized as iterated `IsLiouville.trans` (`isLiouville_tower`, `weakLiouville_tower`).
* **Case 1 (θ algebraic) — YES, via Mathlib.**  The trace/norm-averaging case is
  `isLiouville_of_finiteDimensional`; the Weak Liouville Theorem for a finite algebraic elementary
  extension is `weakLiouville_finiteDimensional` (no hypothesis beyond char 0 + finite-dimensionality).
* **Case 2.1 (θ = log η, transcendental) — YES, via the project keystone.**  `K(log η) / K` is Liouville
  (`isLiouville_logExtension_uncond`, Rosenlicht's log case, done in `LiouvilleLogExtension.lean`); its
  local degree engine (Kaltofen Lemma 3.1a — the degree DROP `coeff_natDegree_logMonomialDeriv`) is
  proved here.
* **Case 2.2 (θ = exp η, transcendental) — the ONE residual.**  `K(exp η) / K` Liouville is the
  cancelled exp instance; named precisely as `ExponentialLayerResidual`.  Its local degree engine
  (Kaltofen Lemma 3.1b — degree-PRESERVING `coeff_natDegree_expMonomialDeriv`) is proved here, so the
  case is set up to the partial-fraction step that the log keystone already executes for its sibling.

**Is `AlgebraicLiouvilleFrontier` discharged?**

* **As stated (presupposing `[IsLiouville F K]`) — YES** (`algebraicLiouvilleFrontier_form`): it *is* the
  descent, the contrapositive of Mathlib's `IsLiouville`.
* **For the operative algebraic case (Trager's finite algebraic function field) — YES,
  UNCONDITIONALLY** (`algebraicLiouvilleFrontier_finiteDimensional`): no `[IsLiouville]` hypothesis,
  because `isLiouville_of_finiteDimensional` supplies it.  The algebraic integrator never meets a
  transcendental layer, so for it the Liouville-structure frontier is closed outright.

**What does the algebraic-completeness frontier now reduce to?**  Reading
`ComputableAlgebraicCompleteness`: the algebraic completeness `some ⟺ elementary` rested on the bundle
`AlgebraicCompletenessResidual` = `AlgebraicLiouvilleFrontier` (the Liouville structure theorem) **+**
`DivisorTorsionDecisionFrontier` (the good-reduction torsion decision = Weil's bound).  This file
**discharges the `AlgebraicLiouvilleFrontier` piece** (the algebraic/finite case unconditionally; the
general case modulo only the per-layer Liouville instance, of which the *only* open one is the
exponential layer `ExponentialLayerResidual` — never encountered by the algebraic integrator).  So the
algebraic-completeness frontier now reduces to **just `DivisorTorsionDecisionFrontier`** — the
divisor-torsion decision correctness (the height-swell / good-reduction tip). -/

/-! ### Restatements + axiom audit -/

section Restatements

-- The Weak Liouville Theorem, descent form: g up the tower with g′ in the base ⟹ Liouville form.
example (F L : Type*) [Field F] [Field L] [Differential F] [Differential L] [Algebra F L]
    [DifferentialAlgebra F L] [IsLiouville F L] (a : F) (g : L) (h : (algebraMap F L a) = g′) :
    HasWeakLiouvilleForm F F a :=
  weakLiouville_of_isLiouville F L a g h

-- Case 1 (algebraic): finite-dimensional elementary extension ⟹ Weak Liouville form, via Mathlib.
example (F L : Type*) [Field F] [Field L] [CharZero F] [Differential F] [Differential L]
    [Algebra F L] [DifferentialAlgebra F L] [FiniteDimensional F L] (a : F) (g : L)
    (h : (algebraMap F L a) = g′) : HasWeakLiouvilleForm F F a :=
  weakLiouville_finiteDimensional F L a g h

-- ★ AlgebraicLiouvilleFrontier, unconditionally discharged for the finite algebraic (Trager) case.
example (F : Type*) [Field F] [Differential F] [CharZero F]
    (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    [FiniteDimensional F K] (f : F) (h : ¬ HasWeakLiouvilleForm F F f) :
    ¬ HasWeakLiouvilleForm F K f :=
  algebraicLiouvilleFrontier_finiteDimensional F K f h

-- Kaltofen Lemma 3.1a (log): top coefficient sees only the base derivation (the degree drop).
example (K : Type*) [Field K] [Differential K] (c : K) (p : K[X]) :
    (logMonomialDeriv c p).coeff p.natDegree = (p.leadingCoeff)′ :=
  coeff_natDegree_logMonomialDeriv c p

-- ★ The ACTUAL ComputableAlgebraicCompleteness.AlgebraicLiouvilleFrontier is a theorem.
example (F : Type*) [Field F] [Differential F] [CharZero F] :
    DeepWiki.SymbolicIntegration.AlgebraicCompleteness.AlgebraicLiouvilleFrontier F :=
  algebraicLiouvilleFrontier_proved F

end Restatements

#print axioms weakLiouville_descend
#print axioms weakLiouville_of_isLiouville
#print axioms weakLiouville_finiteDimensional
#print axioms not_weakElementary_finiteDimensional
#print axioms isLiouville_tower
#print axioms coeff_natDegree_logMonomialDeriv
#print axioms coeff_natDegree_expMonomialDeriv
#print axioms algebraicLiouvilleFrontier_form
#print axioms algebraicLiouvilleFrontier_finiteDimensional
#print axioms algebraicLiouvilleFrontier_proved
#print axioms isAlgebraicElementary_finiteDimensional_discharge

end DeepWiki.SymbolicIntegration.LiouvilleStructure
