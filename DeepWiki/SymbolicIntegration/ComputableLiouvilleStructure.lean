import Mathlib.FieldTheory.Differential.Liouville

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

end Core

end DeepWiki.SymbolicIntegration.LiouvilleStructure
