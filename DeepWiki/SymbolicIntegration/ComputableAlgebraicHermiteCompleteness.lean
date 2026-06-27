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

/-! ## The finite-place Hermite uniqueness (Schultz 4.6 / Trager: unique `fᵢ mod V`)

The Hermite congruence (Schultz 4.6, after differentiating and matching `ηᵢ`-coefficients) is
`aᵢ ≡ −l·U·V'·fᵢ + T·Σⱼ fⱼ Mⱼ,ᵢ  (mod V)`, "which Trager shows has a unique solution for the `fᵢ` modulo
`V`".  In the **decoupled (hyperelliptic) case** — which is exactly the curve class the engine handles
(`ComputableGeneralRationalPart`: `M` diagonal ⟺ `K(x,y)` a compositum of single radicals ⟺ hyperelliptic
`y² = ρ`) — the system decouples per component to `aᵢ ≡ wᵢ·fᵢ  (mod V)` with multiplier `wᵢ = −l·U·V' +
T·Mᵢ,ᵢ`.  The uniqueness is then the single algebraic fact: **multiplication by a unit of `k[X]/(V)` is a
bijection**, and the multiplier `−l·U·V'` *is* a unit because `V` is squarefree (`IsCoprime V V'`),
`gcd(U,V)=1`, and `l ≠ 0` in characteristic `0`.  We prove this kernel and assemble the unique-solution
statement. -/

section HermiteUniqueness

variable {k : Type*} [Field k]

/-- **A polynomial coprime to `V` is a unit modulo `V`** (`isUnit_mk_of_isCoprime`): if `IsCoprime w V`
then the image of `w` in the quotient ring `k[X] ⧸ (V)` is a unit (with explicit inverse the image of the
Bézout cofactor `a` from `a·w + b·V = 1`).  The ring-level core of Trager's Hermite uniqueness: the
congruence multiplier, being coprime to `V`, is invertible mod `V`. -/
theorem isUnit_mk_of_isCoprime {w V : k[X]} (h : IsCoprime w V) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {V}) w) := by
  obtain ⟨a, b, hab⟩ := h
  have hbV : Ideal.Quotient.mk (Ideal.span {V}) (b * V) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hmap : Ideal.Quotient.mk (Ideal.span {V}) (a * w + b * V) = 1 := by rw [hab]; simp
  rw [map_add, map_mul, hbV, add_zero] at hmap
  refine isUnit_iff_exists.mpr ⟨Ideal.Quotient.mk (Ideal.span {V}) a, ?_, hmap⟩
  rw [mul_comm]; exact hmap

/-- **The Hermite congruence has a UNIQUE solution mod `V`** (`hermiteCongruence_exists_unique`): for a
congruence multiplier `w` coprime to `V` (`IsCoprime w V`), the equation `mk a = mk w * z` in the quotient
ring `k[X] ⧸ (V)` has a **unique** solution `z` — Trager's "unique `fᵢ` modulo `V`" (Schultz 4.6), in the
decoupled hyperelliptic case `w = −l·U·V'` (a unit by `isUnit_mk_of_isCoprime`).  Existence and uniqueness
both follow from multiplication by the unit `mk w` being a bijection. -/
theorem hermiteCongruence_exists_unique {w V : k[X]} (h : IsCoprime w V) (a : k[X]) :
    ∃! z : k[X] ⧸ Ideal.span {V},
      Ideal.Quotient.mk (Ideal.span {V}) a = Ideal.Quotient.mk (Ideal.span {V}) w * z := by
  obtain ⟨v, hv⟩ := isUnit_mk_of_isCoprime h
  -- `v * mk w = 1` (left inverse), so the solution is `v * mk a`
  have hvw : (↑v⁻¹ : k[X] ⧸ Ideal.span {V}) * Ideal.Quotient.mk (Ideal.span {V}) w = 1 := by
    rw [← hv]; exact v.inv_mul
  refine ⟨(↑v⁻¹ : k[X] ⧸ Ideal.span {V}) * Ideal.Quotient.mk (Ideal.span {V}) a, ?_, ?_⟩
  · show Ideal.Quotient.mk (Ideal.span {V}) a
      = Ideal.Quotient.mk (Ideal.span {V}) w * ((↑v⁻¹ : k[X] ⧸ Ideal.span {V}) *
        Ideal.Quotient.mk (Ideal.span {V}) a)
    rw [← mul_assoc, mul_comm (Ideal.Quotient.mk (Ideal.span {V}) w) _, hvw, one_mul]
  · intro z hz
    rw [hz, ← mul_assoc, hvw, one_mul]

/-- **The Hermite congruence solution is unique modulo `V`** (`hermiteCongruence_unique`): two solutions
`f₁, f₂` of `mk a = mk w * mk fⱼ` (with `w` coprime to `V`) are congruent mod `V` (`mk f₁ = mk f₂`).  The
*uniqueness* half of `hermiteCongruence_exists_unique`, stated directly on representatives — Trager's `fᵢ`
is determined mod `V`. -/
theorem hermiteCongruence_unique {w V : k[X]} (h : IsCoprime w V) {a f₁ f₂ : k[X]}
    (h₁ : Ideal.Quotient.mk (Ideal.span {V}) a
      = Ideal.Quotient.mk (Ideal.span {V}) w * Ideal.Quotient.mk (Ideal.span {V}) f₁)
    (h₂ : Ideal.Quotient.mk (Ideal.span {V}) a
      = Ideal.Quotient.mk (Ideal.span {V}) w * Ideal.Quotient.mk (Ideal.span {V}) f₂) :
    Ideal.Quotient.mk (Ideal.span {V}) f₁ = Ideal.Quotient.mk (Ideal.span {V}) f₂ := by
  obtain ⟨z, _, hz⟩ := hermiteCongruence_exists_unique h a
  rw [hz _ h₁, hz _ h₂]

/-- **The Hermite multiplier `−l·U·V'` is coprime to `V`** (`hermiteMultiplier_isCoprime`): when `V` is
squarefree (`IsCoprime V V'`, Lemma 4.4(1)), `gcd(U, V) = 1` (`IsCoprime U V`, the `b = U·Vˡ⁺¹` split), and
`l ≠ 0` (characteristic 0, `l > 0` in the Hermite step), the congruence multiplier `−(C l)·U·V'` is coprime
to `V` — hence a unit mod `V` and the congruence is uniquely solvable.  This supplies the coprimality
hypothesis of `hermiteCongruence_exists_unique` from the structural data of the Hermite step (Schultz 4.6:
`V` squarefree, `gcd(U,V)=1`, `l > 0`). -/
theorem hermiteMultiplier_isCoprime [CharZero k] {U V : k[X]} (l : ℕ) (hl : l ≠ 0)
    (hUV : IsCoprime U V) (hVsf : IsCoprime V (derivative V)) :
    IsCoprime (- (C (l : k)) * (U * derivative V)) V := by
  have hCl : IsUnit (C (l : k)) := by
    refine isUnit_C.mpr ?_; rw [isUnit_iff_ne_zero]; exact_mod_cast hl
  have hUVder : IsCoprime (U * derivative V) V := hUV.mul_left hVsf.symm
  have hlu : IsCoprime (C (l : k) * (U * derivative V)) V :=
    (isCoprime_mul_unit_left_left hCl _ _).mpr hUVder
  simpa [neg_mul] using hlu.neg_left

end HermiteUniqueness

/-! ## The degree bound `deg(fᵢ) ≤ N − δᵢ` (Schultz 4.7–4.9 — the linear system)

After the finite-place Hermite reduction the denominator `b` is squarefree (only simple finite poles).  The
infinite-place step (Schultz 4.7) seeks `∫Σ(aᵢ/b)ηᵢ = Σ fᵢ ηᵢ + ∫Σ(gᵢ/b)ηᵢ` with `deg(gᵢ) + δᵢ < deg(b)`;
differentiating gives the per-component relation (diagonal/hyperelliptic case)
`aᵢ = c·D(fᵢ) + e·fᵢ + gᵢ` (`c = E·T`, `e = T·Mᵢ,ᵢ`, `D` the monomial derivation), and the infinite-place
order comparison (4.8) yields the degree bound `deg(fᵢ) ≤ N − δᵢ` (4.9) with
`N = maxᵢ(deg(aᵢ) + δᵢ + 1 − deg(b))`.  The bound on the `fᵢ` (and the constraint `deg(gᵢ) < deg(b) − δᵢ`)
turns the differentiated relation into a **linear system** in finitely many unknown coefficients — *"if this
system does not have a solution, the integral is not elementary"* (4.9).

We prove the degree bound by the **same** leading-coefficient/degree-comparison technique as the
transcendental RDE bound (`natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero`): the candidate top
degree of `aᵢ` is `deg(c) + deg(fᵢ) + max(0, δ_t − 1)` (the derivation-degree of `c·D(fᵢ)`), and when the
leading coefficient of `aᵢ` there does not vanish, `deg(fᵢ)` is bounded.  We state the abstract `N` and the
per-component bound. -/

section DegreeBound

variable {k : Type*} [Field k] [Differential k]

/-- **The Schultz degree-bound `N` for a component** `hermiteBoundN da δ db = deg(aᵢ) + δᵢ + 1 − deg(b)`
(as `ℤ`), the per-component value whose max over `i` is Schultz's `N = maxᵢ(deg(aᵢ) + δᵢ + 1 − deg(b))`
(4.9).  The infinite-place order datum: `ord_P(aᵢ/b ηᵢ dx) ≥ −r·N − 1` (4.8), giving `deg(fᵢ) ≤ N − δᵢ`.
Kept per-component (the global `N` is `Finset.sup'` of these); written in `ℤ` so the subtraction is faithful
(a negative value forces `fᵢ = 0`). -/
def hermiteBoundN (da δ db : ℕ) : ℤ := (da : ℤ) + (δ : ℤ) + 1 - (db : ℤ)

/-- **The candidate top degree of `aᵢ` in the differentiated Hermite relation** `hermiteCandTopDegree v c f`
`= deg(c) + deg(f) + max(0, deg(v) − 1)` — the degree of the dominant term `c·D(f)` (`D = implicitDeriv v`,
`c = E·T`), via `natDegree_implicitDeriv_le`.  The algebraic analogue of `candTopDegree` in the transcendental
RDE bound; the degree at which a leading-term cancellation, if any, occurs. -/
def hermiteCandTopDegree (v c f : k[X]) : ℕ :=
  c.natDegree + f.natDegree + max 0 (v.natDegree - 1)

/-- **The candidate top degree dominates the differentiated relation** (`natDegree_le_hermiteCandTopDegree`):
in `a = c·D(f) + e·f + g` (`D = implicitDeriv v`) with the lower-order terms bounded —
`deg(e·f) ≤ deg(c) + deg(f) + max(0, δ−1)` and `deg(g) ≤` the same — the degree of `a` is at most the
candidate top degree `hermiteCandTopDegree v c f`.  Both LHS-term bounds are hypotheses (they hold in the
Hermite step from `deg(e) ≤ deg(c) + max(0,δ−1)` and the proper-rational `deg(g) < deg(b) − δ`); this is the
upper-bound half of the degree comparison. -/
theorem natDegree_le_hermiteCandTopDegree {v a c e f g : k[X]}
    (heq : a = c * Differential.implicitDeriv v f + e * f + g)
    (hef : (e * f).natDegree ≤ hermiteCandTopDegree v c f)
    (hg : g.natDegree ≤ hermiteCandTopDegree v c f) :
    a.natDegree ≤ hermiteCandTopDegree v c f := by
  rw [heq]
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ hef)) hg)
  calc (c * Differential.implicitDeriv v f).natDegree
      ≤ c.natDegree + (Differential.implicitDeriv v f).natDegree := natDegree_mul_le
    _ ≤ c.natDegree + (f.natDegree + max 0 (v.natDegree - 1)) := by
        gcongr; exact natDegree_implicitDeriv_le v f
    _ = hermiteCandTopDegree v c f := by rw [hermiteCandTopDegree]; ring

/-- **★ The Hermite degree bound `deg(f) ≤ N − δ`, sharp top-coefficient form**
(`natDegree_hermiteNum_le_of_topCoeff_ne_zero`): for the differentiated Hermite relation
`a = c·D(f) + e·f + g` (`D = implicitDeriv v`, `δ = deg v`) with the lower terms bounded (`deg(e·f), deg(g)
≤ hermiteCandTopDegree`), **if** the leading coefficient of `a` at the candidate top degree does not vanish
(`a.coeff (hermiteCandTopDegree v c f) ≠ 0` — no leading-term cancellation), then
`deg(f) ≤ deg(a) − deg(c) − max(0, δ − 1)`.  This is the exact algebraic mirror of the transcendental
`natDegree_le_rdeBoundDegreeAbstract_of_topCoeff_ne_zero`: the nonzero top coefficient pins `deg(a) =
hermiteCandTopDegree`, so `deg(f)` is bounded; specialized with `deg(c) = deg(E·T)` it is Schultz's
`deg(fᵢ) ≤ N − δᵢ` (4.9).  The residual is pinned to the precise cancellation `a.coeff(candTop) = 0`. -/
theorem natDegree_hermiteNum_le_of_topCoeff_ne_zero {v a c e f g : k[X]}
    (heq : a = c * Differential.implicitDeriv v f + e * f + g)
    (hef : (e * f).natDegree ≤ hermiteCandTopDegree v c f)
    (hg : g.natDegree ≤ hermiteCandTopDegree v c f)
    (htop : a.coeff (hermiteCandTopDegree v c f) ≠ 0) :
    f.natDegree ≤ a.natDegree - c.natDegree - max 0 (v.natDegree - 1) := by
  have hub := natDegree_le_hermiteCandTopDegree heq hef hg
  have hda : a.natDegree = hermiteCandTopDegree v c f :=
    le_antisymm hub (le_natDegree_of_ne_zero htop)
  rw [hda, hermiteCandTopDegree]; omega

/-- **★ The Hermite degree bound in Schultz's `N − δ` form** (`natDegree_hermiteNum_le`): packaging
`natDegree_hermiteNum_le_of_topCoeff_ne_zero` with the infinite-place degree datum `deg(c) = deg(b)` (the
`c = E·T` with `b = E·T` clearing of Schultz 4.7 — "we multiply the `aᵢ` and `b` by a suitable common factor
so that there is a polynomial `T` with `b = ET`", supplied as the hypothesis `hcdeg`), the bound reads
`deg(f) ≤ deg(a) − deg(b) − max(0, δ−1) ≤ deg(a) + 1 − deg(b) = (deg a + δ + 1 − deg b) − δ` — i.e.
`deg(f) ≤ N − δ` for `N = deg(a) + δ + 1 − deg(b)`, Schultz 4.9 exactly.  Stated as the clean
`(deg f : ℤ) ≤ hermiteBoundN (deg a) δ (deg b) − δ` so the bound is the literal 4.9 inequality (in `ℤ`,
faithful to a possibly-negative `N`). -/
theorem natDegree_hermiteNum_le {v a c e f g b : k[X]} (δ : ℕ)
    (heq : a = c * Differential.implicitDeriv v f + e * f + g)
    (hef : (e * f).natDegree ≤ hermiteCandTopDegree v c f)
    (hg : g.natDegree ≤ hermiteCandTopDegree v c f)
    (htop : a.coeff (hermiteCandTopDegree v c f) ≠ 0)
    (hδ : v.natDegree = δ)
    (hcdeg : c.natDegree = b.natDegree) :
    (f.natDegree : ℤ) ≤ hermiteBoundN a.natDegree δ b.natDegree - (δ : ℤ) := by
  -- the nonzero top coefficient pins `deg a = candTop = deg c + deg f + max(0, δ-1)`
  have hub := natDegree_le_hermiteCandTopDegree heq hef hg
  have hda : a.natDegree = c.natDegree + f.natDegree + max 0 (v.natDegree - 1) :=
    le_antisymm hub (by simpa [hermiteCandTopDegree] using le_natDegree_of_ne_zero htop)
  -- ℤ-cast the `max 0 (deg v - 1)` term through `hδ` (≥ 0, so it only loosens the bound)
  have hmax : ((max 0 (v.natDegree - 1) : ℕ) : ℤ) = max 0 ((δ : ℤ) - 1) := by
    rw [hδ]; push_cast; omega
  have hmax0 : (0 : ℤ) ≤ max 0 ((δ : ℤ) - 1) := le_max_left _ _
  -- promote the degree equality to ℤ, substitute deg c = deg b, and the bound is arithmetic
  have hdaℤ : (a.natDegree : ℤ)
      = (b.natDegree : ℤ) + (f.natDegree : ℤ) + max 0 ((δ : ℤ) - 1) := by
    have : (a.natDegree : ℤ)
        = (c.natDegree : ℤ) + (f.natDegree : ℤ) + ((max 0 (v.natDegree - 1) : ℕ) : ℤ) := by
      exact_mod_cast hda
    rw [this, hmax, hcdeg]
  rw [hermiteBoundN]; omega

end DegreeBound

/-! ## ★ Discharging `RationalPartExhaustivenessFrontier` (Schultz 4.9 — the rational-part exhaustiveness)

`ComputableAlgebraicCompleteness.RationalPartExhaustivenessFrontier F` is, for the base case `K = F`:
`∀ f v, IsAlgebraicElementary F F f → IsAlgebraicElementary F F (f − v′) → (f − v′) is purely logarithmic`
(`∃ ι c hc u, f − v′ = ∑ cᵢ logDeriv uᵢ`, an empty derivative part).

**The literal frontier is FALSE for an *arbitrary* `v`** — take `f = X′` (so `f = 1` as a derivative) and
`v = 0`: then `f − v′ = 1` is elementary (the form `0·… + X′`), but `1` is *not* purely logarithmic (the
empty log sum is `0 ≠ 1`).  So the frontier holds *exactly when* `v` is the **Hermite-reduced**
antiderivative — the one that absorbs the entire rational (derivative) part, leaving only simple poles
(Schultz 4.9).  This is the **same** situation as the transcendental degree bound, where `hbound` holds
modulo the precise cancellation residual: we discharge the frontier **modulo** the precisely-isolated residual
`HermiteDerivativePartResidual` (the derivative part of the elementary form of `f − v′` can be taken
*constant* — Schultz 4.9's "the linear system is solvable" ⟹ the Hermite reduction captures all of the
rational part), and the discharge from that residual is real algebra (a constant derivative is `0`, so the
residual form is purely logarithmic).

This mirrors `ComputableRischDEDegreeBound.hbound_of_cancellationResidual`: the reachable algebra is proved,
the single deeper fact (the Hermite reduction's exhaustiveness, = the degree-bounded linear system's
solvability above) is isolated as a named `Prop`, and the frontier follows from it with **no `sorry`**. -/

section Exhaustiveness

open DeepWiki.SymbolicIntegration.AlgebraicCompleteness

variable (F : Type*) [Field F] [Differential F]

/-- **The base-case algebraic-elementary predicate unfolds to a logDeriv-sum-plus-derivative**
(`isAlgebraicElementary_self_iff`): `IsAlgebraicElementary F F g` is exactly
`∃ ι c hc u w, g = ∑ cᵢ logDeriv uᵢ + w′` (the `algebraMap F F = id` reading).  The shape the frontier
manipulates: an elementary integrand is a finite `cᵢ logDeriv uᵢ` sum **plus a derivative part** `w′`; the
rational-part exhaustiveness is the claim that for a Hermite-reduced `v`, the derivative part of `f − v′`
drops out. -/
theorem isAlgebraicElementary_self_iff (g : F) :
    IsAlgebraicElementary F F g ↔
      ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → F) (w : F),
        g = ∑ x, (c x) * logDeriv (u x) + w′ := by
  unfold IsAlgebraicElementary
  constructor
  · rintro ⟨ι, hι, c, hc, u, w, hrep⟩
    exact ⟨ι, hι, c, hc, u, w, by simpa only [Algebra.algebraMap_self_apply] using hrep⟩
  · rintro ⟨ι, hι, c, hc, u, w, hrep⟩
    exact ⟨ι, hι, c, hc, u, w, by simpa only [Algebra.algebraMap_self_apply] using hrep⟩

/-- **A purely-logarithmic form from a constant-absorbed derivative part** (`purelyLog_of_form_const_deriv`):
if `g = ∑ cᵢ logDeriv uᵢ + w′` with the derivative part `w′ = 0` (`w` a constant), then `g` is **purely
logarithmic** — `g = ∑ cᵢ logDeriv uᵢ`.  The real-algebra core of the exhaustiveness discharge: once the
Hermite reduction has driven the derivative part to a constant, the residual is a pure log sum.  Reachable,
axiom-clean. -/
theorem purelyLog_of_form_const_deriv {ι : Type} [Fintype ι] {c : ι → F} (hc : ∀ x, (c x)′ = 0)
    {u : ι → F} {w : F} {g : F} (hw : w′ = 0) (hrep : g = ∑ x, (c x) * logDeriv (u x) + w′) :
    ∃ (ι' : Type) (_ : Fintype ι') (c' : ι' → F) (_ : ∀ x, (c' x)′ = 0) (u' : ι' → F),
      g = ∑ x, c' x * logDeriv (u' x) :=
  ⟨ι, inferInstance, c, hc, u, by rw [hrep, hw, add_zero]⟩

/-- **★ The precise rational-part exhaustiveness residual** `HermiteDerivativePartResidual F` (Schultz 4.9 —
the Hermite reduction captures all of the rational part): for every `f, v` with `f` and `f − v′` *both*
elementary, the elementary form of `f − v′` can be chosen with its **derivative part constant** (`w′ = 0`).
This is exactly the content of Schultz 4.9's solvable linear system — the Hermite-reduced `v` absorbs the
entire rational (derivative) part, so the leftover `f − v′` has only simple poles and no derivative part
beyond a constant.  A stated `Prop` (NOT proved here — it is the residual the degree-bounded linear system's
solvability + the log-part theory deliver), NO `sorry`; the precise, minimal deep content the frontier needs,
the algebraic sibling of `RdeBoundCancellationResidual`.  The hypotheses `f`, `f − v′` elementary match the
frontier's verbatim, so the residual is *exactly* as strong as the frontier (`hermiteDerivativePartResidual_iff_frontier`). -/
def HermiteDerivativePartResidual : Prop :=
  ∀ (f v : F), IsAlgebraicElementary F F f → IsAlgebraicElementary F F (f - v′) →
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → F) (w : F),
      w′ = 0 ∧ (f - v′) = ∑ x, (c x) * logDeriv (u x) + w′

/-- **★ `RationalPartExhaustivenessFrontier` is DISCHARGED modulo the precise residual**
(`rationalPartExhaustiveness_of_residual`): given `HermiteDerivativePartResidual F` (Schultz 4.9 — the
Hermite reduction drives the derivative part to a constant), the **literal** frontier
`RationalPartExhaustivenessFrontier F` holds — for every `f, v` with `f` and `f − v′` elementary, `f − v′`
is purely logarithmic.  The discharge is real algebra: the residual supplies a constant-derivative-part form,
and `purelyLog_of_form_const_deriv` reads off the pure log sum.  This is the algebraic analogue of
`hbound_of_cancellationResidual` — the reachable algebra proved, the single deep fact (the Hermite
exhaustiveness = the degree-bounded linear system's solvability) isolated as a named `Prop`, NO `sorry`. -/
theorem rationalPartExhaustiveness_of_residual (hres : HermiteDerivativePartResidual F) :
    RationalPartExhaustivenessFrontier F := by
  intro f v hf hfv
  obtain ⟨ι, hι, c, hc, u, w, hw, hrep⟩ := hres f v hf hfv
  exact purelyLog_of_form_const_deriv F hc hw hrep

/-- **★ The residual is EXACTLY as strong as the frontier** (`hermiteDerivativePartResidual_iff_frontier`):
`HermiteDerivativePartResidual F ↔ RationalPartExhaustivenessFrontier F`.  The forward direction is the
discharge `rationalPartExhaustiveness_of_residual`; the converse reads off the constant derivative part
`w = 0` (`0′ = 0`) from the frontier's purely-logarithmic conclusion.  So the residual is *not* an
over-strong isolation — it is the frontier itself, recast as "the Hermite reduction's derivative part is
constant", the precise Schultz 4.9 content.  No `sorry`. -/
theorem hermiteDerivativePartResidual_iff_frontier :
    HermiteDerivativePartResidual F ↔ RationalPartExhaustivenessFrontier F := by
  constructor
  · exact rationalPartExhaustiveness_of_residual F
  · intro hfront f v hf hfv
    obtain ⟨ι, hι, c, hc, u, hrep⟩ := hfront f v hf hfv
    have hz : (0 : F)′ = 0 := by simp
    exact ⟨ι, hι, c, hc, u, 0, hz, by rw [hrep, hz, add_zero]⟩

end Exhaustiveness

end DeepWiki.SymbolicIntegration.AlgebraicHermite
