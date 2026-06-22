import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.MonomialExtensions

/-! # `IntegrateRationalFunction` in closed log-form (Bronstein §2.4/§2.5)
The culmination of rational-function integration: `∫ A/D = (rational part) + ∫ p dx + ∑ a·log(Gₐ)`,
assembled as a single derivative identity in `K(x) = RatFunc K`. Combines the §2.5 reduction
`integrateRationalFunction_reduction` (Hermite + polynomial-division split, leaving a sum of proper
fractions over squarefree denominators) with the Rothstein–Trager residue-grouped log sum
`ratFunc_eq_sum_residue_grouped` applied to each such fraction. The denominators are parameterized in
split form `Dᵢ = ∏_{α∈sᵢ}(X−α) = Lagrange.nodal sᵢ id` (so each `Dᵢ` is squarefree and distinct `Dᵢ`
are coprime exactly when the root-sets are disjoint), and the remainders `rᵢ` are assumed *proper*
(`deg rᵢ < #sᵢ`) — the Hermite-reduction properness the reduction lemma does not itself expose. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Differential in
open Classical in
/-- **Log-form of a proper-fraction sum over split squarefree denominators** (§2.4/§2.5): the
residue-grouping step alone. Given the reduction's output — a rational derivative `g′`, a
polynomial-integral derivative `(∫ p dx)′`, and a sum of proper fractions `∑ᵢ rᵢ/Dᵢ` over split
squarefree denominators `Dᵢ = Lagrange.nodal (sset i) id` with each `rᵢ` proper (`deg rᵢ < #sset i`) —
rewrite each `rᵢ/Dᵢ` by `ratFunc_eq_sum_residue_grouped` into its Rothstein–Trager log sum
`∑_a a·logDeriv(Gᵢₐ)`, `Gᵢₐ = ∏_{α∈sset i, res(α)=a}(X−α)`, yielding the closed log-form
`g′ + (∫ p dx)′ + ∑ᵢ ∑_a a·logDeriv(Gᵢₐ)`. -/
theorem sum_proper_fraction_eq_logForm {ι : Type*} (s : Finset ι) (sset : ι → Finset K)
    (r : ι → K[X]) (g : RatFunc K) (p : K[X])
    (hproper : ∀ i ∈ s, (r i).degree < (sset i).card) :
    g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
        + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i)
            / algebraMap K[X] (RatFunc K) (Lagrange.nodal (sset i) id)
      = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
        + ∑ i ∈ s, ∑ a ∈ (sset i).image
            (fun α => (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id))),
            algebraMap K[X] (RatFunc K) (C a)
              * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                  (∏ α ∈ (sset i).filter
                      (fun α => (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id)) = a),
                    (X - C α))) := by
  rw [Finset.sum_congr rfl
    (fun i hi => ratFunc_eq_sum_residue_grouped (sset i) (r i) (hproper i hi))]

open scoped Differential in
open Classical in
/-- **`IntegrateRationalFunction` in closed log-form** (§2.4/§2.5, eq 2.4 — the culmination): for a
numerator `A` over a denominator whose squarefree factors are given in split form
`Dᵢ = Lagrange.nodal (sset i) id = ∏_{α∈sset i}(X−α)` (the root-sets `sset i` pairwise disjoint, so the
`Dᵢ` are squarefree and pairwise coprime, `eᵢ ≥ 1`, char `0`), there exist a rational part `g`, a
polynomial-integral part `p`, and proper remainders `rᵢ` such that — *provided the remainders are
proper* (`deg rᵢ < #sset i`) — the integrand has the closed log-form
`A/∏ᵢ Dᵢ^{eᵢ} = g′ + (∫ p dx)′ + ∑ᵢ ∑_a a·logDeriv(Gᵢₐ)`, where `Gᵢₐ = ∏_{α∈sset i, res(α)=a}(X−α)`
collects the roots of `Dᵢ` with residue `a`. Runs `integrateRationalFunction_reduction` internally
(its `Squarefree`/`IsCoprime` side conditions discharged from the split form via
`squarefree_prod_X_sub_C`/`isCoprime_prod_X_sub_C_of_disjoint` and `nodal_eq`), then applies
`sum_proper_fraction_eq_logForm`. The properness premise `hproper` is on the *produced* `rᵢ`: Hermite
reduction is supposed to leave proper remainders, but `integrateRationalFunction_reduction` does not
currently expose the bound, so it is taken as a hypothesis on its output. -/
theorem integrateRationalFunction_logForm [CharZero K] {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (sset : ι → Finset K) (e : ι → ℕ) (he : ∀ i ∈ s, 1 ≤ e i)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (sset i) (sset j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
      (∀ i ∈ s, (r i).degree < (sset i).card) →
        algebraMap K[X] (RatFunc K) A
            / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (Lagrange.nodal (sset i) id) ^ e i
          = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
            + ∑ i ∈ s, ∑ a ∈ (sset i).image
                (fun α => (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id))),
                algebraMap K[X] (RatFunc K) (C a)
                  * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                      (∏ α ∈ (sset i).filter
                          (fun α =>
                            (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id)) = a),
                        (X - C α))) := by
  have hsf : ∀ i ∈ s, Squarefree (Lagrange.nodal (sset i) id) := fun i _ => by
    rw [Lagrange.nodal_eq]; exact squarefree_prod_X_sub_C (sset i)
  have hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      IsCoprime (Lagrange.nodal (sset i) id) (Lagrange.nodal (sset j) id) := fun i hi j hj hij => by
    rw [Lagrange.nodal_eq, Lagrange.nodal_eq]
    exact isCoprime_prod_X_sub_C_of_disjoint (hdisj i hi j hj hij)
  obtain ⟨g, p, r, hred⟩ :=
    integrateRationalFunction_reduction s hs (fun i => Lagrange.nodal (sset i) id) e hsf he hcop A
  refine ⟨g, p, r, fun hproper => ?_⟩
  rw [hred]
  exact sum_proper_fraction_eq_logForm s sset r g p hproper

open scoped Differential in
open Classical in
/-- **§2.5 log-form, single squarefree denominator** (the `e = 1`, no-rational-part case): for a proper
fraction `R/V` with `V = Lagrange.nodal s id = ∏_{α∈s}(X−α)` split squarefree and `deg R < #s`, the
log-form has neither a rational part nor a polynomial-integral part:
`R/V = ∑_a a·logDeriv(Gₐ)`, `Gₐ = ∏_{α∈s, res(α)=a}(X−α)`. Here Hermite reduction is trivial (`V`
already squarefree) and `R` is already proper, so this is `ratFunc_eq_sum_residue_grouped` packaged as
the §2.5 log-form; `∫ R/V = ∑_a a·log(Gₐ)`. -/
theorem ratFunc_logForm_split_squarefree (s : Finset K) (R : K[X]) (hR : R.degree < s.card) :
    algebraMap K[X] (RatFunc K) R / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = ∑ a ∈ s.image (fun α => R.eval α / eval α (derivative (Lagrange.nodal s id))),
          algebraMap K[X] (RatFunc K) (C a)
            * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                (∏ α ∈ s.filter (fun α => R.eval α / eval α (derivative (Lagrange.nodal s id)) = a),
                  (X - C α))) :=
  ratFunc_eq_sum_residue_grouped s R hR

open scoped Differential in
open Classical in
-- §2.5 log-form, single split squarefree denominator: `R/V = ∑_a a·logDeriv(Gₐ)`.
example (s : Finset K) (R : K[X]) (hR : R.degree < s.card) :
    algebraMap K[X] (RatFunc K) R / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = ∑ a ∈ s.image (fun α => R.eval α / eval α (derivative (Lagrange.nodal s id))),
          algebraMap K[X] (RatFunc K) (C a)
            * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                (∏ α ∈ s.filter (fun α => R.eval α / eval α (derivative (Lagrange.nodal s id)) = a),
                  (X - C α))) :=
  ratFunc_logForm_split_squarefree s R hR

open scoped Differential in
open Classical in
-- The full §2.5 closed log-form: rational part + polynomial-integral part + sum of log-derivatives.
example [CharZero K] {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (sset : ι → Finset K) (e : ι → ℕ)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (sset i) (sset j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
      (∀ i ∈ s, (r i).degree < (sset i).card) →
        algebraMap K[X] (RatFunc K) A
            / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (Lagrange.nodal (sset i) id) ^ e i
          = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
            + ∑ i ∈ s, ∑ a ∈ (sset i).image
                (fun α => (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id))),
                algebraMap K[X] (RatFunc K) (C a)
                  * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                      (∏ α ∈ (sset i).filter
                          (fun α =>
                            (r i).eval α / eval α (derivative (Lagrange.nodal (sset i) id)) = a),
                        (X - C α))) :=
  integrateRationalFunction_logForm s hs sset e he hdisj A

end DeepWiki.SymbolicIntegration
