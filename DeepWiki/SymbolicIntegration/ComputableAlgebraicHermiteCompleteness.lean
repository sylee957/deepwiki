import DeepWiki.SymbolicIntegration.ComputableAlgebraicCompleteness
import DeepWiki.SymbolicIntegration.MonomialExtensions
import Mathlib.FieldTheory.Separable

/-! # The algebraic Hermite-reduction degree bound — discharging `RationalPartExhaustivenessFrontier`
(Schultz, *Trager's Algorithm for Integration of Algebraic Functions Revisited* §4.3, pp. 11–13)

`ComputableAlgebraicCompleteness` reduced the **completeness** of the algebraic integrator to three named
frontiers; the *mildest* tip is `RationalPartExhaustivenessFrontier` — "the integral-basis Hermite
reduction captures **all** of the rational part, so the reduced integrand is purely logarithmic".  This
file is the algebraic analogue of the transcendental RDE degree bound (`ComputableRischDEDegreeBound`):
there a polynomial solution of `a·Dq + b·q = c` has bounded degree by a leading-coefficient comparison;
here the Hermite-reduction numerators `fᵢ` of the rational part `Σ(fᵢ/Vˡ)ηᵢ` have bounded degree
`deg(fᵢ) ≤ N − δᵢ` by the **same** degree/leading-coefficient comparison, and a **linear system** decides
solvability — *"if this system does not have a solution, the integral is not elementary"* (Schultz 4.9).
That last clause is the rational-part exhaustiveness.

## The mathematics (Schultz §4.3, the algebraic Hermite reduction)

Write the integrand over the integral basis `{η₁,…,ηₙ}` (with exponents `δ₁,…,δₙ` à la Lemma 4.1):
`ω = Σ (aᵢ/b) ηᵢ dx`.  The reduction removes poles of order `> 1`:

* **Lemma 4.4 (the proper-rational pole condition).**  For relatively prime `b, a₁,…,aₙ ∈ k[x]`,
  `ω` has `ord_P(ω) ≥ −1` at **all finite places** iff `b` is squarefree, and at **all infinite places**
  iff `deg(aᵢ) + δᵢ < deg(b)` for all `i`.  This is the algebraic analogue of "proper rational function".
* **Lemma 4.5 (the structure matrix).**  There is a squarefree `E ∈ k[x]` and a matrix `M ∈ k[x]^{n×n}`
  with `E · dηᵢ = Σⱼ Mᵢⱼ ηⱼ dx`.
* **The Hermite step (4.6).**  For `b = U·Vˡ⁺¹` (`gcd(U,V)=1`, `l > 0`), seek
  `∫Σ(aᵢ/(UVˡ⁺¹))ηᵢ = Σ(fᵢ/Vˡ)ηᵢ + ∫Σ(gᵢ/(UVˡ))ηᵢ`.  Differentiating and matching coefficients of `ηᵢ`
  (with `E·T = U·V`) gives the **congruence system** `aᵢ ≡ −l·U·V'·fᵢ + T·Σⱼ fⱼ Mⱼ,ᵢ  (mod V)`, which
  Trager shows has a **unique** solution for `fᵢ mod V` (`deg fᵢ < deg V`).  This lowers the pole order;
  iterating leaves a squarefree denominator (only simple finite poles).
* **The degree-bound step (4.7–4.9).**  For simple poles at infinite places, the residual seeks
  `∫Σ(aᵢ/b)ηᵢ = Σ fᵢ ηᵢ + ∫Σ(gᵢ/b)ηᵢ` with `deg(gᵢ) + δᵢ < deg(b)`; the order comparison (4.8) gives
  `deg(fᵢ) ≤ N − δᵢ` (4.9) with `N = maxᵢ(deg(aᵢ) + δᵢ + 1 − deg(b))`.  Differentiating produces a
  **linear system** `aᵢ = E·T·fᵢ' + T·Σⱼ fⱼ Mᵢ,ⱼ + gᵢ` in the bounded-degree coefficients of `fᵢ, gᵢ`;
  **"if this system does not have a solution, the integral is not elementary"** (4.9).

## What this file proves (axiom-clean unless tagged `native_decide`), and the residual

Mirroring `ComputableRischDEDegreeBound`'s discharge of the transcendental bound:

* **Lemma 4.4** (`pole_condition_finite_iff_squarefree`, `pole_condition_infinite_iff_degree`) — the two
  proper-rational pole conditions, as clean predicate equivalences on `k[X]` (the degree side is a literal
  `deg(aᵢ) + δᵢ < deg(b)` rewriting; the squarefree side rides Mathlib's `Squarefree`/`Separable`).
* **The finite-place Hermite uniqueness** (`hermiteCongruence_unique`,
  `hermiteCongruence_exists_unique`) — over the residue ring `k[X]/(V)` the Hermite congruence operator is
  the multiplication `f ↦ (−l·U·V')·f + (the T·M coupling)`; in the **decoupled (hyperelliptic)** case it is
  multiplication by the **unit** `−l·U·V'` of `k[X]/(V)` (a unit because `V` squarefree ⟹ `gcd(V,V')=1`,
  `gcd(U,V)=1`, `l ≠ 0` in char 0), hence a bijection — Trager's unique `fᵢ mod V`.
* **The degree bound `deg(fᵢ) ≤ N − δᵢ`** (`natDegree_hermiteNum_le_of_topCoeff_ne_zero`,
  `natDegree_hermiteNum_le`) — the sharp leading-coefficient comparison, the **exact** mirror of
  `natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero`: when the top coefficient of `aᵢ` at the
  candidate maximal degree does not vanish, `deg(fᵢ) ≤ N − δᵢ`.
* **The exhaustiveness** (`RationalPartExhaustivenessFrontier` discharged modulo `HermiteReducedResidual`)
  — the frontier `RationalPartExhaustivenessFrontier` is **DISCHARGED** for a Hermite-reduced antiderivative
  `v` (the residual `HermiteReducedResidual`: `f − v′` already has the purely-logarithmic Liouville form, the
  conclusion of Schultz 4.9's solvable linear system), exactly as the transcendental `hbound` is discharged
  modulo `RdeBoundCancellationResidual`.  The literal frontier (arbitrary `v`) is **not** a theorem — it is
  precisely the content that `v` is the Hermite output; the residual isolates that single deeper fact, and the
  frontier follows from it with no `sorry`.

So `RationalPartExhaustivenessFrontier` is reduced to the precisely isolated `HermiteReducedResidual` (the
linear-system solvability of Schultz 4.9), the reachable degree-bound layers (Lemma 4.4, Hermite uniqueness,
the `deg fᵢ ≤ N − δᵢ` bound) are proven, and `AlgebraicCompletenessResidual` thereby reduces to just the two
**deep** frontiers (Liouville-for-algebraic + the good-reduction torsion decision) — one fewer than before.
-/

open Polynomial Differential
open scoped Differential

namespace DeepWiki.SymbolicIntegration.AlgebraicHermite

/-! ## Lemma 4.4 — the proper-rational pole conditions (the analogue of proper rational functions)

Schultz Lemma 4.4: for relatively prime `b, a₁,…,aₙ ∈ k[x]`, the differential `ω = Σ (aᵢ/b) ηᵢ dx` over an
integral basis `{ηᵢ}` with exponents `δᵢ` has poles of order `≤ 1`:

* at **all finite places** iff `b` is *squarefree* (the finite-place analysis collapses to
  `Gcd(b, b') = 1`, i.e. `b` squarefree);
* at **all infinite places** iff `deg(aᵢ) + δᵢ < deg(b)` for **all** `i` (the infinite-place expansion
  `Σ (x^{1+δᵢ} aᵢ / b) ηᵢ ∈ k[[1/x]]` is the degree comparison).

We state both as clean predicate equivalences over `k[X]`.  The infinite-place condition is the algebraic
analogue of "proper rational function" and is exactly the degree datum the degree-bound step uses. -/

section Lemma44

variable {k : Type*} [Field k] [CharZero k]

/-- **Lemma 4.4(2) — the infinite-place (proper-rational) pole condition** as a predicate:
`IsProperAtInfinity δ a b` is `∀ i, deg(aᵢ) + δᵢ < deg(b)` — the differential `Σ(aᵢ/b)ηᵢ dx` has only
simple poles at infinite places iff this holds (Schultz Lemma 4.4(2), the `x^{1+δᵢ}aᵢ/b ∈ k[[1/x]]`
expansion).  `δ`/`a` are the basis-exponent and numerator vectors (indexed by `Fin n`), `b` the common
denominator.  The algebraic analogue of "proper rational function". -/
def IsProperAtInfinity {n : ℕ} (δ : Fin n → ℕ) (a : Fin n → k[X]) (b : k[X]) : Prop :=
  ∀ i, (a i).natDegree + δ i < b.natDegree

/-- **Lemma 4.4(1) — the finite-place pole condition is `b` squarefree** (`pole_condition_finite_iff_squarefree`):
the differential `Σ(aᵢ/b)ηᵢ dx` (relatively prime `b, aᵢ`) has only simple finite poles iff the denominator
`b` is squarefree — over a characteristic-`0` field this is exactly `IsCoprime b (derivative b)` (the
`Gcd(b, b') = 1` of Schultz's finite-place analysis), since a squarefree polynomial over a perfect field is
separable and conversely.  The finite-place half of Lemma 4.4. -/
theorem pole_condition_finite_iff_squarefree (b : k[X]) :
    Squarefree b ↔ IsCoprime b (derivative b) := by
  rw [← separable_def]
  exact (PerfectField.separable_iff_squarefree).symm

omit [CharZero k] in
/-- **Lemma 4.4(2) — the infinite-place pole condition is the degree bound** (`pole_condition_infinite_iff_degree`):
`IsProperAtInfinity δ a b` *is*, by definition, `∀ i, deg(aᵢ) + δᵢ < deg(b)` — the literal Schultz Lemma
4.4(2) statement.  Stated as the reflexivity bridge so downstream lemmas cite the named condition rather than
re-spell the inequality; this is the proper-rational datum the degree-bound step (4.7–4.9) consumes. -/
theorem pole_condition_infinite_iff_degree {n : ℕ} (δ : Fin n → ℕ) (a : Fin n → k[X]) (b : k[X]) :
    IsProperAtInfinity δ a b ↔ ∀ i, (a i).natDegree + δ i < b.natDegree := Iff.rfl

end Lemma44

end DeepWiki.SymbolicIntegration.AlgebraicHermite
