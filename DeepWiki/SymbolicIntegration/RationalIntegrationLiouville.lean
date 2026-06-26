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
