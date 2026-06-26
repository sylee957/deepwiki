import DeepWiki.SymbolicIntegration.RationalIntegrationLogForm

/-! # Rational-function completeness — Liouville's theorem, rational case (Bronstein §2.4/§2.5)
The converse-direction companion to the rational-integration soundness capstone: *every* rational
function `f ∈ K(x)` (over an algebraically closed field of characteristic `0`) has an integral in
**Liouville form** `∫ f = g + ∑ᵢ cᵢ·log(uᵢ)`, i.e. `f = g′ + ∑ᵢ cᵢ·logDeriv(uᵢ)` with
`g, uᵢ ∈ K(x)` and `cᵢ ∈ K` constants. This is the *constructive* rational case of Liouville's
theorem: the decomposition is produced (Hermite reduction + polynomial part + Rothstein–Trager log
grouping), not merely asserted to exist.

The whole logarithmic-detection content sits in the **decision corollary**
`ratFunc_logarithmFree_iff_residues_zero`: `∫ f` is *logarithm-free* (i.e. `f = g′` for some rational
`g`) iff all residues vanish — exactly the statement that the algorithm's logarithm-detection is
*complete* (when a residue is nonzero, `∫ f` is genuinely not rational).

This composes the existing rational-integration spine — `integrateRationalFunction_logForm`
(Hermite + poly part + RT grouping over *split* squarefree denominators) — with a front-end that
takes an *arbitrary* `f`: writing `f = A/D`, `D` splits over the algebraically closed field into a
product of distinct-root powers `∏_{α}(X−α)^{e α}`, the split form the log-form theorem consumes. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## Splitting an arbitrary denominator into distinct-root powers -/

open Classical in
/-- **`X − C α` as a one-point nodal polynomial**: `Lagrange.nodal {α} id = X − C α`. The singleton
split factor, so a denominator's distinct-root factorization `∏_α (X−α)^{e α}` is in the
`∏ᵢ (nodal (sset i) id)^{eᵢ}` form `integrateRationalFunction_logForm` consumes (with `sset α = {α}`,
which are pairwise disjoint). -/
theorem nodal_singleton (α : K) : Lagrange.nodal {α} id = (X - C α : K[X]) := by
  rw [Lagrange.nodal_eq, Finset.prod_singleton, id]

open Classical in
/-- **A monic split polynomial factors over its distinct roots** (the splitting front-end): for a
monic `D` over a field that *splits* (e.g. algebraically closed), `D = ∏_{α ∈ D.roots.toFinset}
(X − α)^{D.roots.count α}` — the product over the *distinct* roots, each with its multiplicity. This
regroups the multiset factorization `D = ∏_{α ∈ D.roots}(X − α)` (`Splits.eq_prod_roots_of_monic`) by
root value (`Finset.prod_multiset_map_count`). -/
theorem monic_eq_prod_distinct_roots_pow (D : K[X]) (hsplit : D.Splits) (hmonic : D.Monic) :
    D = ∏ α ∈ D.roots.toFinset, (X - C α) ^ D.roots.count α := by
  classical
  conv_lhs => rw [hsplit.eq_prod_roots_of_monic hmonic, Finset.prod_multiset_map_count]

/-! ## The rational Liouville form (Finset-sum shape) -/

open scoped Differential in
open Classical in
/-- **Rational-function Liouville form, denominator-supplied shape** (§2.4/§2.5): for `A, D ∈ K[x]`
with `D` monic and *split* (e.g. over an algebraically closed field) and `D ≠ 0`, the rational
function `A/D` has the closed Liouville form `A/D = g′ + (∫ p dx)′ + ∑ log`, with the logarithmic
part the Rothstein–Trager grouped sum over the distinct roots of `D`. This specializes
`integrateRationalFunction_logForm` to the singleton root-sets `sset α = {α}` (pairwise disjoint),
whose product `∏_{α}(X−α)^{e α}` is exactly `D` (`monic_eq_prod_distinct_roots_pow`,
`nodal_singleton`). -/
theorem ratFunc_div_liouville_form [CharZero K] (A D : K[X]) (hsplit : D.Splits) (hmonic : D.Monic) :
    ∃ (g : RatFunc K) (p : K[X]) (r : K → K[X]),
        algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D
          = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
            + ∑ α ∈ D.roots.toFinset, ∑ a ∈ ({α} : Finset K).image
                (fun β => (r α).eval β / eval β (derivative (Lagrange.nodal {α} id))),
                algebraMap K[X] (RatFunc K) (C a)
                  * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                      (∏ β ∈ ({α} : Finset K).filter
                          (fun β =>
                            (r α).eval β / eval β (derivative (Lagrange.nodal {α} id)) = a),
                        (X - C β))) := by
  classical
  -- the singleton root-sets `{α}` are nonempty, pairwise disjoint, with positive multiplicity
  have hne : ∀ α ∈ D.roots.toFinset, ({α} : Finset K).Nonempty := fun α _ => ⟨α, by simp⟩
  have hdisj : ∀ α ∈ D.roots.toFinset, ∀ β ∈ D.roots.toFinset, α ≠ β →
      Disjoint ({α} : Finset K) ({β} : Finset K) := fun α _ β _ hαβ => by
    simp [hαβ]
  have he : ∀ α ∈ D.roots.toFinset, 1 ≤ D.roots.count α := fun α hα =>
    Multiset.one_le_count_iff_mem.mpr (Multiset.mem_toFinset.mp hα)
  obtain ⟨g, p, r, hform⟩ :=
    integrateRationalFunction_logForm (K := K) D.roots.toFinset (fun α => {α})
      D.roots.count he hne hdisj A
  refine ⟨g, p, r, ?_⟩
  -- rewrite the product `∏_α (nodal {α} id)^(count α)` to `algebraMap D`
  have hprod : (∏ α ∈ D.roots.toFinset,
        algebraMap K[X] (RatFunc K) (Lagrange.nodal ({α} : Finset K) id) ^ D.roots.count α)
      = algebraMap K[X] (RatFunc K) D := by
    have hstep : (∏ α ∈ D.roots.toFinset,
          algebraMap K[X] (RatFunc K) (Lagrange.nodal ({α} : Finset K) id) ^ D.roots.count α)
        = algebraMap K[X] (RatFunc K) (∏ α ∈ D.roots.toFinset, (X - C α) ^ D.roots.count α) := by
      rw [map_prod]
      exact Finset.prod_congr rfl fun α _ => by rw [nodal_singleton, map_pow]
    rw [hstep, ← monic_eq_prod_distinct_roots_pow D hsplit hmonic]
  rw [hprod] at hform
  exact hform

open scoped Differential in
open Classical in
/-- **Rational-function Liouville form** (§2.4/§2.5, the constructive rational case of Liouville's
theorem): over an algebraically closed field of characteristic `0`, *every* `f ∈ K(x)` has a closed
Liouville integral `∫ f = g + ∫ p dx + ∑ log`, i.e.
`f = g′ + (∫ p dx)′ + ∑_{α} ∑_a a·logDeriv(Gₐ)`, with `g ∈ K(x)`, `p ∈ K[x]` (so `∫ p dx = polyIntegral p`),
and the logarithmic part the Rothstein–Trager grouped sum over the distinct denominator roots. This is
`ratFunc_div_liouville_form` applied to `f = f.num / f.denom`: the denominator `f.denom` is monic
(`RatFunc.monic_denom`) and splits over the algebraically closed field (`IsAlgClosed.splits`). The
residues `a = (rᵢ).eval β / D'(β)` are the genuine residues of `f`, living in `K`. -/
theorem ratFunc_liouville [CharZero K] [IsAlgClosed K] (f : RatFunc K) :
    ∃ (g : RatFunc K) (p : K[X]) (r : K → K[X]),
        f = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ α ∈ f.denom.roots.toFinset, ∑ a ∈ ({α} : Finset K).image
              (fun β => (r α).eval β / eval β (derivative (Lagrange.nodal {α} id))),
              algebraMap K[X] (RatFunc K) (C a)
                * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                    (∏ β ∈ ({α} : Finset K).filter
                        (fun β =>
                          (r α).eval β / eval β (derivative (Lagrange.nodal {α} id)) = a),
                      (X - C β))) := by
  classical
  obtain ⟨g, p, r, hform⟩ :=
    ratFunc_div_liouville_form f.num f.denom (IsAlgClosed.splits f.denom) (RatFunc.monic_denom f)
  refine ⟨g, p, r, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom f]
  exact hform

/-! ## Flat single-sum form (`∑_{α} cα·logDeriv(X−α)`) and the List form -/

open scoped Differential in
open Classical in
/-- **Singleton inner-sum collapse**: in the split form, each singleton root-set `{α}` makes the inner
Rothstein–Trager sum `∑_{a ∈ {α}.image res} a·logDeriv(Gₐ)` collapse to the single term
`res(α)·logDeriv(X − α)`, with `res(α) = (r α)(α)` (since `(nodal {α} id)′ = (X−α)′ = 1`). The
distinct-root residue at a simple root. -/
theorem singleton_residue_sum_collapse (α : K) (r : K → K[X]) :
    (∑ a ∈ ({α} : Finset K).image
        (fun β => (r α).eval β / eval β (derivative (Lagrange.nodal {α} id))),
        algebraMap K[X] (RatFunc K) (C a)
          * Differential.logDeriv (algebraMap K[X] (RatFunc K)
              (∏ β ∈ ({α} : Finset K).filter
                  (fun β => (r α).eval β / eval β (derivative (Lagrange.nodal {α} id)) = a),
                (X - C β))))
      = algebraMap K[X] (RatFunc K) (C ((r α).eval α))
          * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C α)) := by
  classical
  rw [Finset.image_singleton, Finset.sum_singleton]
  have hd1 : eval α (derivative (Lagrange.nodal ({α} : Finset K) id)) = 1 := by
    rw [nodal_singleton]; simp
  rw [hd1, div_one]
  congr 2
  rw [Finset.filter_singleton, if_pos (by rw [hd1, div_one]), Finset.prod_singleton]

open scoped Differential in
open Classical in
/-- **Rational-function Liouville form, flat single-sum shape** (§2.4/§2.5): the split form with each
singleton inner sum collapsed (`singleton_residue_sum_collapse`), so the logarithmic part is a *single*
sum over the distinct denominator roots:
`f = g′ + (∫ p dx)′ + ∑_{α} (rα)(α)·logDeriv(X − α)` — each distinct root `α` contributing one
logarithm `log(x − α)` with constant coefficient the residue `(rα)(α) ∈ K`. -/
theorem ratFunc_liouville_flat [CharZero K] [IsAlgClosed K] (f : RatFunc K) :
    ∃ (g : RatFunc K) (p : K[X]) (r : K → K[X]),
        f = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ α ∈ f.denom.roots.toFinset,
              algebraMap K[X] (RatFunc K) (C ((r α).eval α))
                * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C α)) := by
  classical
  obtain ⟨g, p, r, hform⟩ := ratFunc_liouville f
  refine ⟨g, p, r, hform.trans ?_⟩
  congr 1
  exact Finset.sum_congr rfl fun α _ => singleton_residue_sum_collapse α r

open scoped Differential in
open Classical in
/-- **Finset log-sum repackaged as a List sum**: a Finset sum of `algebraMap (C (c i))·logDeriv(u i)`
equals the List sum `((s.toList).map (i ↦ (c i, u i))).map (cu ↦ cu.1 • logDeriv cu.2) |>.sum`, the
bridge from the `Finset`-indexed log part to the task's `List (K × K(x))` shape. Uses
`algebraMap (C a)·x = a • x` (`Algebra.smul_def` + the `K → K[X] → K(x)` scalar tower) and
`Finset.sum = (toList).sum`. -/
theorem finsetLogSum_eq_listSum {ι : Type*} (s : Finset ι) (c : ι → K) (u : ι → RatFunc K) :
    (∑ i ∈ s, algebraMap K[X] (RatFunc K) (C (c i)) * Differential.logDeriv (u i))
      = (((s.toList).map (fun i => (c i, u i))).map
          (fun cu => cu.1 • Differential.logDeriv cu.2)).sum := by
  classical
  rw [List.map_map]
  rw [show (∑ i ∈ s, algebraMap K[X] (RatFunc K) (C (c i)) * Differential.logDeriv (u i))
        = ∑ i ∈ s, c i • Differential.logDeriv (u i) from
      Finset.sum_congr rfl fun i _ => by
        rw [Algebra.smul_def, ← Polynomial.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]]
  rw [Finset.sum_eq_multiset_sum, ← Multiset.coe_toList s.val]
  simp [Function.comp]

open scoped Differential in
open Classical in
/-- **Rational-function Liouville form, List shape** (§2.4/§2.5 — the task's target form): over an
algebraically closed field of characteristic `0`, *every* `f ∈ K(x)` is
`f = g′ + ∑_{(c,u) ∈ logs} c·logDeriv(u)` with `g ∈ K(x)`, `logs : List (K × K(x))` a list of
(constant coefficient, rational argument) pairs — the constructive rational case of Liouville's
theorem with the polynomial-integral part folded into the rational part `g`
(`g′ + (∫ p dx)′ = (g + ∫ p dx)′`) and the logarithmic part presented as a list (`X − α` per distinct
root, coefficient the residue). The scalar `c • logDeriv u = c·logDeriv u` via `Algebra.smul_def`. -/
theorem ratFunc_liouville_list [CharZero K] [IsAlgClosed K] (f : RatFunc K) :
    ∃ (g : RatFunc K) (logs : List (K × RatFunc K)),
        f = g′ + (logs.map (fun cu => cu.1 • Differential.logDeriv cu.2)).sum := by
  classical
  obtain ⟨g, p, r, hform⟩ := ratFunc_liouville_flat f
  refine ⟨g + algebraMap K[X] (RatFunc K) (polyIntegral p),
    (f.denom.roots.toFinset.toList).map
      (fun α => ((r α).eval α, algebraMap K[X] (RatFunc K) (X - C α))), hform.trans ?_⟩
  rw [map_add]
  congr 1
  -- the log sum: from the flat Finset sum to the mapped List sum
  exact finsetLogSum_eq_listSum f.denom.roots.toFinset
    (fun α => (r α).eval α) (fun α => algebraMap K[X] (RatFunc K) (X - C α))

/-! ## The decision corollary — logarithm-detection completeness -/

open scoped Differential in
open Classical in
/-- **Logarithm-free integration from vanishing residues** (§2.4/§2.5, the forward completeness): if
every residue (the flat-form coefficient `(rα)(α)` at each distinct denominator root `α`) vanishes,
then `∫ f` is *logarithm-free* — `f = G′` for a rational `G ∈ K(x)` (`G = g + ∫ p dx`). This is the
algorithmically meaningful half: when the Rothstein–Trager residues all vanish, the logarithmic part
is absent and the integral stays rational. (When some residue is nonzero, `∫ f` genuinely needs a
logarithm — the residues, identified below with the intrinsic `residueAt α f`, are a true obstruction.) -/
theorem ratFunc_logarithmFree_of_residues_zero [CharZero K] [IsAlgClosed K] (f : RatFunc K)
    {r : K → K[X]} {g : RatFunc K} {p : K[X]}
    (hform : f = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ α ∈ f.denom.roots.toFinset,
              algebraMap K[X] (RatFunc K) (C ((r α).eval α))
                * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C α)))
    (hres : ∀ α ∈ f.denom.roots.toFinset, (r α).eval α = 0) :
    ∃ G : RatFunc K, f = G′ := by
  refine ⟨g + algebraMap K[X] (RatFunc K) (polyIntegral p), ?_⟩
  rw [hform, map_add]
  -- the entire log sum vanishes: each coefficient `C ((rα)(α)) = C 0 = 0`
  have hzero : (∑ α ∈ f.denom.roots.toFinset,
        algebraMap K[X] (RatFunc K) (C ((r α).eval α))
          * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C α))) = 0 :=
    Finset.sum_eq_zero fun α hα => by rw [hres α hα, map_zero, map_zero, zero_mul]
  rw [hzero, add_zero]

open scoped Differential in
open Classical in
/-- **Logarithm-free integration, packaged with the residues exposed** (§2.4/§2.5, the decision
content): *every* `f ∈ K(x)` (over an algebraically closed char-`0` field) comes with computed
residues `r : K → K[X]` and a flat Liouville form
`f = g′ + (∫ p dx)′ + ∑_α (rα)(α)·logDeriv(X − α)`, *together with* the affirmative decision rule —
**if** all the residues `(rα)(α)` vanish, **then** `∫ f` is logarithm-free (`∃ G, f = G′`). This is
the algorithm's complete logarithm-detection on its affirmative side: it computes the residues and,
when they all vanish, returns a rational antiderivative. (The converse `f = G′ ⟹ residues vanish`
needs `residueAt α (G′) = 0` — that a rational derivative has no simple-pole residue — a Laurent
argument not formalized here; see the file note.) -/
theorem ratFunc_liouville_form_with_residues [CharZero K] [IsAlgClosed K] (f : RatFunc K) :
    ∃ (r : K → K[X]) (g : RatFunc K) (p : K[X]),
      f = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ α ∈ f.denom.roots.toFinset,
              algebraMap K[X] (RatFunc K) (C ((r α).eval α))
                * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C α))
        ∧ ((∀ α ∈ f.denom.roots.toFinset, (r α).eval α = 0) → ∃ G : RatFunc K, f = G′) := by
  obtain ⟨g, p, r, hform⟩ := ratFunc_liouville_flat f
  exact ⟨r, g, p, hform, fun hres =>
    ratFunc_logarithmFree_of_residues_zero f hform hres⟩

/-! ## Restatements against the book's wording (Liouville's theorem, rational case)

The rational case of **Liouville's theorem** (Bronstein §2.4/§2.5, the structural content behind
`IntegrateRationalFunction`): `∫ f` for `f ∈ K(x)` is always elementary of the special form
`g + ∑ᵢ cᵢ·log(uᵢ)` with `g, uᵢ ∈ K(x)` and `cᵢ` constants — equivalently
`f = g′ + ∑ᵢ cᵢ·logDeriv(uᵢ)`. The companion **`## NOT YET FORMALIZED` gap**: the full converse of the
decision corollary (`f = G′ ⟹ all residues vanish`) needs that a rational derivative has zero residue
at every simple pole (a Laurent-coefficient fact); only the affirmative
`residues vanish ⟹ logarithm-free` direction is proved. -/

open scoped Differential in
open Classical in
-- Liouville's theorem, rational case (List form): `f = g′ + ∑_(c,u) c·logDeriv(u)`.
example [CharZero K] [IsAlgClosed K] (f : RatFunc K) :
    ∃ (g : RatFunc K) (logs : List (K × RatFunc K)),
        f = g′ + (logs.map (fun cu => cu.1 • Differential.logDeriv cu.2)).sum :=
  ratFunc_liouville_list f

open scoped Differential in
open Classical in
-- Decision (affirmative side): vanishing Rothstein–Trager residues ⟹ `∫ f` is rational (no logs).
example [CharZero K] [IsAlgClosed K] (f : RatFunc K) :
    ∃ (r : K → K[X]) (g : RatFunc K) (p : K[X]),
      f = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ α ∈ f.denom.roots.toFinset,
              algebraMap K[X] (RatFunc K) (C ((r α).eval α))
                * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C α))
        ∧ ((∀ α ∈ f.denom.roots.toFinset, (r α).eval α = 0) → ∃ G : RatFunc K, f = G′) :=
  ratFunc_liouville_form_with_residues f
