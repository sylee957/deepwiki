import DeepWiki.SymbolicIntegration.RationalIntegrationLogForm
import DeepWiki.SymbolicIntegration.RecognizingLogDeriv

/-! # Rational-function completeness — Liouville's theorem, rational case (Bronstein §2.4/§2.5)
The converse-direction companion to the rational-integration soundness capstone: *every* rational
function `f ∈ K(x)` (over an algebraically closed field of characteristic `0`) has an integral in
**Liouville form** `∫ f = g + ∑ᵢ cᵢ·log(uᵢ)`, i.e. `f = g′ + ∑ᵢ cᵢ·logDeriv(uᵢ)` with
`g, uᵢ ∈ K(x)` and `cᵢ ∈ K` constants. This is the *constructive* rational case of Liouville's
theorem: the decomposition is produced (Hermite reduction + polynomial part + Rothstein–Trager log
grouping), not merely asserted to exist.

The logarithmic-detection content is the **decision iff** `ratFunc_logarithmFree_iff_residues_zero`:
`∫ f` is *logarithm-free* (`f = g′` for a rational `g`) **iff** all the Rothstein–Trager residues
vanish. The `←` (affirmative) `ratFunc_logarithmFree_of_residues_zero` drops the log part when the
residues vanish; the `→` (converse) rests on the Laurent fact `residueAt α (g′) = 0` — a rational
derivative has no simple-pole residue, proved here elementarily (`residueAt_derivative_eq_zero`,
casing on whether `α` is a pole, no Laurent/Hahn-series machinery) — together with reading the residue
`(rα)(α)` off the simple-pole log sum (`residueAt_logSum_eq_coeff`). The residue functional `residueAt`
and its toolkit are imported from `RecognizingLogDeriv`.

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

/-! ## A rational derivative has no simple-pole residue (the converse ingredient)
The Laurent fact behind the *converse* of the decision corollary: `residueAt α (G′) = 0` for every
`G ∈ K(x)`. In the Laurent expansion `G = ∑ⱼ cⱼ(x−α)^j`, `G′ = ∑ⱼ j·cⱼ(x−α)^{j−1}`, whose
`(x−α)^{−1}`-coefficient is the `j = 0` term `0·c₀ = 0` — a derivative never produces a simple-pole
residue. Formalized through `residueAt α f = ((X−α)·f)(α)`: writing `G = n/d` (`n = num G`,
`d = denom G`, coprime), `(X − α)·G′ = (X − α)(n′d − nd′)/d²`; either `α` is *not* a pole (`d(α) ≠ 0`)
and the explicit `(X − α)` factor in the numerator vanishes at `α`, or `α` *is* a pole (`d(α) = 0`)
and `(X − α)·G′` still has a genuine pole there, so `RatFunc.eval` reads `0`. -/

open scoped Classical in
/-- **`RatFunc.eval` reads `0` at a genuine pole**: if `x = g/h ∈ K(x)` with the *numerator* `g`
nonzero at `α` (`g(α) ≠ 0`) but the denominator `h` vanishing there (`h(α) = 0`, `h ≠ 0`), then `α` is
a true pole and `RatFunc.eval id α x = 0` (division by the vanished reduced denominator). The pole-case
companion to `eval_algebraMap_div` (which needs `h(α) ≠ 0`): from the cross-multiplication
`num x · h = g · denom x`, evaluating at `α` gives `0 = g(α)·(denom x)(α)`, so `(denom x)(α) = 0`. -/
theorem eval_algebraMap_div_eq_zero_of_pole (α : K) (g h : K[X]) (hg : g.eval α ≠ 0)
    (hh : h.eval α = 0) (hh0 : h ≠ 0) :
    RatFunc.eval (RingHom.id K) α
        (algebraMap K[X] (RatFunc K) g / algebraMap K[X] (RatFunc K) h) = 0 := by
  set x : RatFunc K := algebraMap K[X] (RatFunc K) g / algebraMap K[X] (RatFunc K) h with hx
  -- cross-multiplication `num x · h = g · denom x`, from `num x / denom x = g / h`
  have hcross : RatFunc.num x * h = g * RatFunc.denom x := by
    have hd := RatFunc.denom_ne_zero x
    have heq : algebraMap K[X] (RatFunc K) (RatFunc.num x)
          / algebraMap K[X] (RatFunc K) (RatFunc.denom x)
        = algebraMap K[X] (RatFunc K) g / algebraMap K[X] (RatFunc K) h :=
      (RatFunc.num_div_denom x).trans hx
    rw [div_eq_div_iff
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hd)
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hh0),
      ← map_mul, ← map_mul] at heq
    exact RatFunc.algebraMap_injective K heq
  -- evaluate the cross-mult at `α`: `0 = g(α)·(denom x)(α)`, so `(denom x)(α) = 0`
  have heval : (RatFunc.num x).eval α * h.eval α = g.eval α * (RatFunc.denom x).eval α := by
    simpa only [eval_mul] using congrArg (Polynomial.eval α) hcross
  rw [hh, mul_zero] at heval
  have hdenom : (RatFunc.denom x).eval α = 0 :=
    (mul_eq_zero.mp heval.symm).resolve_left hg
  -- `RatFunc.eval` divides by the vanished reduced denominator → `0`
  exact RatFunc.eval_eq_zero_of_eval₂_denom_eq_zero
    (by rw [Polynomial.eval₂_id]; exact hdenom)

open scoped Classical in
open scoped Differential in
/-- **A rational derivative has zero residue at every simple pole** (the converse ingredient,
Bronstein §2.4/§2.5): `residueAt α (G′) = 0` for all `G ∈ K(x)` and `α ∈ K`. The Laurent statement —
the `(x−α)^{−1}`-coefficient of `G′` is the `j = 0` term `0·c₀ = 0` — made elementary through
`residueAt α f = ((X−α)·f)(α)` and the quotient rule `G′ = (n′d − nd′)/d²` (`n = num G`, `d = denom G`):
casing on whether `α` is a pole, either `d(α) ≠ 0` and the numerator's explicit `(X−α)` factor kills
the value, or `d(α) = 0` and `(X−α)·G′` retains a genuine pole so `RatFunc.eval` reads `0`
(`eval_algebraMap_div_eq_zero_of_pole`, the numerator `(X−α)(n′d − nd′)` being nonzero at `α` exactly
when `d(α) = 0`, as `gcd(n,d) = 1` forces `n(α) ≠ 0` and char `0` keeps the multiplicity `m+1 ≠ 0`). -/
theorem residueAt_derivative_eq_zero [CharZero K] (G : RatFunc K) (α : K) :
    residueAt α (G′) = 0 := by
  set n := RatFunc.num G with hn
  set d := RatFunc.denom G with hd
  have hd0 : d ≠ 0 := RatFunc.denom_ne_zero G
  -- `G = n/d`, so `G′ = (n′d − nd′)/d²` and `(X−α)·G′ = (X−α)(n′d − nd′)/d²`
  have hGmk : G′ = ratFuncDeriv G := rfl
  have hGdiv : G = RatFunc.mk n d := by rw [RatFunc.mk_eq_div, RatFunc.num_div_denom]
  have hderiv : G′ = algebraMap K[X] (RatFunc K) (derivative n * d - n * derivative d)
      / algebraMap K[X] (RatFunc K) (d ^ 2) := by
    rw [hGmk, hGdiv, ratFuncDeriv_mk, RatFunc.mk_eq_div]
  set N := (X - C α) * (derivative n * d - n * derivative d) with hN
  set D := d ^ 2 with hD
  have hxG : algebraMap K[X] (RatFunc K) (X - C α) * G′
      = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D := by
    rw [hderiv, hN, map_mul, mul_div_assoc']
  rw [residueAt, hxG]
  by_cases hdα : d.eval α = 0
  · -- pole case: `α` is a root of `d`.  Cancel the common `(X−α)`-powers from `N/D`, leaving a
    -- numerator nonzero at `α` over a denominator vanishing at `α` → a genuine pole, `eval = 0`.
    -- `n(α) ≠ 0`: `gcd(n, d) = 1`, so `α` can't be a common root
    have hnα : n.eval α ≠ 0 := by
      intro hnα0
      have hcop : IsCoprime n d := RatFunc.isCoprime_num_denom G
      exact (Polynomial.not_isUnit_X_sub_C α)
        (hcop.isUnit_of_dvd' (dvd_iff_isRoot.mpr hnα0) (dvd_iff_isRoot.mpr hdα))
    -- `d = (X − α)^(m+1) · d₁`, `m + 1 = rootMultiplicity α d ≥ 1`, `d₁(α) ≠ 0`
    have hk1 : 1 ≤ d.rootMultiplicity α :=
      (rootMultiplicity_pos hd0).mpr (by rw [Polynomial.IsRoot]; exact hdα)
    obtain ⟨m, hkm⟩ : ∃ m, d.rootMultiplicity α = m + 1 := ⟨d.rootMultiplicity α - 1, by omega⟩
    obtain ⟨d₁, hdeq, hndvd⟩ := d.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hd0 α
    rw [hkm] at hdeq
    have hd₁ : d₁.eval α ≠ 0 := fun h0 => hndvd (dvd_iff_isRoot.mpr h0)
    -- reduced numerator `M = n′(X−α)d₁ − n((m+1)·d₁ + (X−α)d₁′)`, value at `α` is `−(m+1)·n(α)·d₁(α) ≠ 0`
    set M := derivative n * ((X - C α) * d₁) - n * (C ((m : K) + 1) * d₁ + (X - C α) * derivative d₁)
      with hM
    set Dred := (X - C α) ^ (m + 1) * d₁ ^ 2 with hDred
    -- cancel `(X−α)^(m+1)`: `N/D = M/Dred` in `K(x)`, from the polynomial factorization
    have hpolyN : N = (X - C α) ^ (m + 1) * M := by
      rw [hN, hM, hdeq, derivative_mul, derivative_pow, derivative_X_sub_C, mul_one,
        Nat.add_sub_cancel]
      push_cast
      ring
    have hpolyD : D = (X - C α) ^ (m + 1) * Dred := by
      rw [hD, hDred, hdeq]; ring
    have hMα : M.eval α ≠ 0 := by
      rw [hM]
      simp only [eval_sub, eval_mul, eval_add, eval_C, eval_sub, eval_X, sub_self,
        zero_mul, mul_zero, add_zero]
      -- `M(α) = 0 − n(α)·((m+1)·d₁(α)) = −(m+1)·n(α)·d₁(α)`
      rw [zero_sub, neg_ne_zero, mul_ne_zero_iff]
      exact ⟨hnα, mul_ne_zero (Nat.cast_add_one_ne_zero m) hd₁⟩
    have hDredα : Dred.eval α = 0 := by
      rw [hDred, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
        zero_pow (Nat.succ_ne_zero m), zero_mul]
    have hDred0 : Dred ≠ 0 := by
      rw [hDred]; exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero α))
        (pow_ne_zero 2 (fun h0 => hd₁ (by rw [h0, eval_zero])))
    -- rewrite `N/D` to `M/Dred` by canceling `algebraMap((X−α)^(m+1))`
    have hpkne : algebraMap K[X] (RatFunc K) ((X - C α) ^ (m + 1)) ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (pow_ne_zero _ (X_sub_C_ne_zero α))
    rw [hpolyN, hpolyD, map_mul, map_mul, mul_div_mul_left _ _ hpkne]
    exact eval_algebraMap_div_eq_zero_of_pole α M Dred hMα hDredα hDred0
  · -- regular case: `d(α) ≠ 0`, so `D(α) = d(α)² ≠ 0`; `N(α)` has the `(X−α)` factor → `0`
    have hDα : D.eval α ≠ 0 := by rw [hD, eval_pow]; exact pow_ne_zero 2 hdα
    rw [eval_algebraMap_div α N D hDα]
    have hNα : N.eval α = 0 := by rw [hN, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
    rw [hNα, zero_div]

/-! ## Identifying the flat-form residue with the intrinsic `residueAt α f`
For the backward direction of the iff, the flat-form coefficient `(rα)(α)` must be recognised as the
intrinsic residue `residueAt α f`.  Applying `residueAt α` to the flat Liouville form kills `g′` and
`(∫p dx)′` (`residueAt_derivative_eq_zero`) and reads `(rα)(α)` off the log sum (each
`cβ·logDeriv(X−β)` has residue `cβ` at `α = β`, `0` elsewhere — additive through pole-free witnesses). -/

open scoped Classical in
/-- **Pole-free witness for a Finset sum**: if each once-multiplied term `(X − α)·tᵢ = aᵢ/bᵢ` is
pole-free at `α` (`bᵢ(α) ≠ 0`), the sum `∑ᵢ tᵢ` also has a pole-free witness — `(X − α)·∑ᵢ tᵢ = Aₛ/Bₛ`
with `Bₛ(α) ≠ 0` and `Aₛ(α)/Bₛ(α) = ∑ᵢ aᵢ(α)/bᵢ(α)`. Finset induction summing fractions over the
running common denominator; this packages the regular-at-`α` witness `residueAt_sum_of_witnesses`
consumes. -/
theorem exists_witness_sum {ι : Type*} (α : K) (s : Finset ι) (t : ι → RatFunc K)
    (a b : ι → K[X]) (hb : ∀ i ∈ s, (b i).eval α ≠ 0)
    (hwit : ∀ i ∈ s, algebraMap K[X] (RatFunc K) (X - C α) * t i
      = algebraMap K[X] (RatFunc K) (a i) / algebraMap K[X] (RatFunc K) (b i)) :
    ∃ A B : K[X], B.eval α ≠ 0 ∧ A.eval α / B.eval α = ∑ i ∈ s, (a i).eval α / (b i).eval α ∧
      algebraMap K[X] (RatFunc K) (X - C α) * (∑ i ∈ s, t i)
        = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) B := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨0, 1, by simp, by simp, ?_⟩
    simp [map_zero, map_one]
  | insert j s hjs ih =>
    obtain ⟨A, B, hBα, hval, hAB⟩ :=
      ih (fun i hi => hb i (Finset.mem_insert_of_mem hi))
        (fun i hi => hwit i (Finset.mem_insert_of_mem hi))
    have hbj : (b j).eval α ≠ 0 := hb j (Finset.mem_insert_self j s)
    have hwitj := hwit j (Finset.mem_insert_self j s)
    refine ⟨a j * B + A * b j, b j * B, by rw [eval_mul]; exact mul_ne_zero hbj hBα, ?_, ?_⟩
    · rw [Finset.sum_insert hjs, ← hval, eval_add, eval_mul, eval_mul, eval_mul,
        div_add_div _ _ hbj hBα, mul_comm (eval α (b j)) (eval α A)]
    · have hbjne : algebraMap K[X] (RatFunc K) (b j) ≠ 0 :=
        (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
          (fun h0 => hbj (by rw [h0, eval_zero]))
      have hBne : algebraMap K[X] (RatFunc K) B ≠ 0 :=
        (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
          (fun h0 => hBα (by rw [h0, eval_zero]))
      rw [Finset.sum_insert hjs, mul_add, hwitj, hAB, map_add, map_mul, map_mul, map_mul,
        div_add_div _ _ hbjne hBne, mul_comm (algebraMap K[X] (RatFunc K) A)]

open scoped Classical in
/-- **Additivity of the residue over a pole-free witness sum**: a Finset sum `∑ᵢ tᵢ` whose each
once-multiplied term `(X − α)·tᵢ = aᵢ/bᵢ` is pole-free at `α` (`bᵢ(α) ≠ 0`) has residue
`residueAt α (∑ᵢ tᵢ) = ∑ᵢ aᵢ(α)/bᵢ(α)` — the residue functional is additive on simple-pole terms. The
sum's own pole-free witness (`exists_witness_sum`) lets `residueAt_of_mul_X_sub_C` read the value. -/
theorem residueAt_sum_of_witnesses {ι : Type*} (α : K) (s : Finset ι) (t : ι → RatFunc K)
    (a b : ι → K[X]) (hb : ∀ i ∈ s, (b i).eval α ≠ 0)
    (hwit : ∀ i ∈ s, algebraMap K[X] (RatFunc K) (X - C α) * t i
      = algebraMap K[X] (RatFunc K) (a i) / algebraMap K[X] (RatFunc K) (b i)) :
    residueAt α (∑ i ∈ s, t i) = ∑ i ∈ s, (a i).eval α / (b i).eval α := by
  obtain ⟨A, B, hBα, hval, hAB⟩ := exists_witness_sum α s t a b hb hwit
  rw [residueAt_of_mul_X_sub_C α (∑ i ∈ s, t i) A B hBα hAB, hval]

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

open scoped Classical in
open scoped Differential in
/-- **Logarithm-free ⟹ all residues vanish** (§2.4/§2.5, the *converse* completeness — intrinsic form):
if `∫ f` is logarithm-free (`f = G′` for a rational `G ∈ K(x)`), then the residue `residueAt α f` at
every `α ∈ K` vanishes. Immediate from `residueAt_derivative_eq_zero` (a rational derivative has no
simple-pole residue): `residueAt α f = residueAt α (G′) = 0`. The genuine obstruction direction — a
nonzero residue forces a logarithm — completing the logarithm-free decision to an iff
(`ratFunc_logarithmFree_iff_residueAt_zero`). -/
theorem ratFunc_residues_zero_of_logarithmFree [CharZero K] (f : RatFunc K)
    (hf : ∃ G : RatFunc K, f = G′) (α : K) : residueAt α f = 0 := by
  obtain ⟨G, rfl⟩ := hf
  exact residueAt_derivative_eq_zero G α

open scoped Classical in
open scoped Differential in
/-- **Residue of the flat log-sum picks off its coefficient**: for the Rothstein–Trager log sum
`∑_{β∈s} cβ·logDeriv(X − β)` (`cβ = (rβ)(β)`) over a Finset `s` of *distinct* points, the residue at a
member `α ∈ s` is exactly its coefficient `cα` — `residueAt α (∑β cβ·logDeriv(X − β)) = cα`. Each term
`cβ·logDeriv(X − β) = cβ/(X − β)` has a simple pole, where `residueAt` is exact: the `β = α` term
cancels to the constant `cα` (witness `cα/1`), every `β ≠ α` term is regular at `α` with value `0`
(witness `cβ(X − α)/(X − β)`). Summed through `residueAt_sum_of_witnesses`. -/
theorem residueAt_logSum_eq_coeff (s : Finset K) (r : K → K[X]) (α : K) (hα : α ∈ s) :
    residueAt α (∑ β ∈ s, algebraMap K[X] (RatFunc K) (C ((r β).eval β))
        * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C β)))
      = (r α).eval α := by
  classical
  -- per-term pole-free witnesses: `(X−α)·(cβ·logDeriv(X−β)) = aβ/bβ` with `bβ(α) ≠ 0`
  set a : K → K[X] := fun β => if β = α then C ((r α).eval α) else C ((r β).eval β) * (X - C α)
    with ha
  set b : K → K[X] := fun β => if β = α then 1 else X - C β with hb
  have hbα : ∀ β ∈ s, (b β).eval α ≠ 0 := by
    intro β _
    by_cases hβ : β = α
    · simp [hb, hβ]
    · simp only [hb, if_neg hβ, eval_sub, eval_X, eval_C]
      exact sub_ne_zero.mpr (Ne.symm hβ)
  have hwit : ∀ β ∈ s, algebraMap K[X] (RatFunc K) (X - C α)
        * (algebraMap K[X] (RatFunc K) (C ((r β).eval β))
            * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C β)))
      = algebraMap K[X] (RatFunc K) (a β) / algebraMap K[X] (RatFunc K) (b β) := by
    intro β _
    -- `logDeriv(X−β) = 1/(X−β)`
    have hlog : Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C β))
        = 1 / algebraMap K[X] (RatFunc K) (X - C β) := by
      rw [logDeriv_algebraMap_eq, derivative_X_sub_C, map_one]
    have hXβne : algebraMap K[X] (RatFunc K) (X - C β) ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero β)
    by_cases hβ : β = α
    · subst hβ
      simp only [ha, hb, if_pos rfl, map_one, div_one]
      rw [hlog, mul_one_div, mul_div_assoc', mul_comm, mul_div_assoc, div_self hXβne, mul_one]
    · simp only [ha, hb, if_neg hβ]
      rw [hlog, mul_one_div, map_mul, mul_comm (algebraMap K[X] (RatFunc K) (C ((r β).eval β))),
        mul_div_assoc]
  rw [residueAt_sum_of_witnesses α s _ a b hbα hwit]
  -- evaluate the witness sum: only the `β = α` term is nonzero, contributing `cα`
  rw [Finset.sum_eq_single α]
  · simp [ha, hb]
  · intro β _ hβ
    simp only [ha, hb, if_neg hβ, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero,
      zero_div]
  · intro hαs; exact absurd hα hαs

open scoped Classical in
open scoped Differential in
/-- **Logarithm-free ⟹ flat-form residues vanish** (§2.4/§2.5, the *converse* completeness on the
flat-form coefficients): if `∫ f` is logarithm-free (`f = G′`) and `f` has the canonical flat Liouville
form with coefficients `cα = (rα)(α)`, then every `cα` (at a denominator root `α`) vanishes. The log
sum `∑α cα·logDeriv(X − α) = f − g′ − (∫p dx)′ = (G − g − ∫p)′` is itself a rational *derivative*, so
its residue at each `α` is `0` (`residueAt_derivative_eq_zero`); but that residue equals the
coefficient `cα` (`residueAt_logSum_eq_coeff`, the log sum having only simple poles). -/
theorem ratFunc_residues_zero_of_logarithmFree_flat [CharZero K] [IsAlgClosed K] (f : RatFunc K)
    {r : K → K[X]} {g : RatFunc K} {p : K[X]}
    (hform : f = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ α ∈ f.denom.roots.toFinset,
              algebraMap K[X] (RatFunc K) (C ((r α).eval α))
                * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C α)))
    (hf : ∃ G : RatFunc K, f = G′) (α : K) (hα : α ∈ f.denom.roots.toFinset) :
    (r α).eval α = 0 := by
  obtain ⟨G, hG⟩ := hf
  -- the log sum equals the rational derivative `(G − g − ∫p)′`
  set LogSum := ∑ β ∈ f.denom.roots.toFinset,
      algebraMap K[X] (RatFunc K) (C ((r β).eval β))
        * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C β)) with hLogSum
  have hLogDeriv : LogSum
      = (G - g - algebraMap K[X] (RatFunc K) (polyIntegral p))′ := by
    have hd1 : (G - g - algebraMap K[X] (RatFunc K) (polyIntegral p))′
        = (G - g)′ - (algebraMap K[X] (RatFunc K) (polyIntegral p))′ :=
      map_sub Differential.deriv _ _
    have hd2 : (G - g)′ = G′ - g′ := map_sub Differential.deriv _ _
    rw [hd1, hd2]
    have : G′ = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′ + LogSum := by
      rw [← hG, hform]
    rw [this]; ring
  -- `cα = residueAt α LogSum = residueAt α (derivative) = 0`
  rw [← residueAt_logSum_eq_coeff f.denom.roots.toFinset r α hα, ← hLogSum, hLogDeriv,
    residueAt_derivative_eq_zero]

open scoped Differential in
open Classical in
/-- **Logarithm-free integration, packaged with the residues exposed** (§2.4/§2.5, the decision
content): *every* `f ∈ K(x)` (over an algebraically closed char-`0` field) comes with computed
residues `r : K → K[X]` and a flat Liouville form
`f = g′ + (∫ p dx)′ + ∑_α (rα)(α)·logDeriv(X − α)`, *together with* the affirmative decision rule —
**if** all the residues `(rα)(α)` vanish, **then** `∫ f` is logarithm-free (`∃ G, f = G′`). This is
the algorithm's complete logarithm-detection on its affirmative side: it computes the residues and,
when they all vanish, returns a rational antiderivative. (The full *iff* — `f = G′` ⟺ residues vanish —
is `ratFunc_logarithmFree_iff_residues_zero`, the converse via `residueAt_derivative_eq_zero`.) -/
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

open scoped Differential in
open Classical in
/-- **The full rational logarithm-free decision** (§2.4/§2.5, the iff completing the Rothstein–Trager
detection): *every* `f ∈ K(x)` (over an algebraically closed char-`0` field) comes with computed
residues `r : K → K[X]` and a flat Liouville form `f = g′ + (∫ p dx)′ + ∑_α (rα)(α)·logDeriv(X − α)`,
for which `∫ f` is *logarithm-free* (`∃ G, f = G′`) **iff** every residue `(rα)(α)` vanishes. The `←`
(affirmative) is `ratFunc_logarithmFree_of_residues_zero` — vanishing residues drop the log part; the
`→` (converse) is `ratFunc_residues_zero_of_logarithmFree_flat` — a nonzero residue is a genuine
obstruction, since the log sum (`= f − g′ − (∫p)′`, a rational derivative when `f = G′`) has residue
`(rα)(α)` at each `α` (`residueAt_logSum_eq_coeff`), forced to `0` by `residueAt_derivative_eq_zero`. -/
theorem ratFunc_logarithmFree_iff_residues_zero [CharZero K] [IsAlgClosed K] (f : RatFunc K) :
    ∃ (r : K → K[X]) (g : RatFunc K) (p : K[X]),
      f = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ α ∈ f.denom.roots.toFinset,
              algebraMap K[X] (RatFunc K) (C ((r α).eval α))
                * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C α))
        ∧ ((∃ G : RatFunc K, f = G′) ↔ (∀ α ∈ f.denom.roots.toFinset, (r α).eval α = 0)) := by
  obtain ⟨g, p, r, hform⟩ := ratFunc_liouville_flat f
  refine ⟨r, g, p, hform, ?_, fun hres => ratFunc_logarithmFree_of_residues_zero f hform hres⟩
  intro hf α hα
  exact ratFunc_residues_zero_of_logarithmFree_flat f hform hf α hα

/-! ## Restatements against the book's wording (Liouville's theorem, rational case)

The rational case of **Liouville's theorem** (Bronstein §2.4/§2.5, the structural content behind
`IntegrateRationalFunction`): `∫ f` for `f ∈ K(x)` is always elementary of the special form
`g + ∑ᵢ cᵢ·log(uᵢ)` with `g, uᵢ ∈ K(x)` and `cᵢ` constants — equivalently
`f = g′ + ∑ᵢ cᵢ·logDeriv(uᵢ)`. The **decision is an iff**: `∫ f` is logarithm-free iff all the
Rothstein–Trager residues vanish — both the affirmative `residues vanish ⟹ logarithm-free` and the
converse `f = G′ ⟹ residues vanish` directions are proved (the latter on a rational derivative having
zero residue at every simple pole). -/

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

open scoped Differential in
open Classical in
-- Decision (full iff): `∫ f` logarithm-free (`f = G′`) ⟺ all Rothstein–Trager residues vanish.
example [CharZero K] [IsAlgClosed K] (f : RatFunc K) :
    ∃ (r : K → K[X]) (g : RatFunc K) (p : K[X]),
      f = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ α ∈ f.denom.roots.toFinset,
              algebraMap K[X] (RatFunc K) (C ((r α).eval α))
                * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C α))
        ∧ ((∃ G : RatFunc K, f = G′) ↔ (∀ α ∈ f.denom.roots.toFinset, (r α).eval α = 0)) :=
  ratFunc_logarithmFree_iff_residues_zero f

open scoped Differential in
open Classical in
-- A rational derivative has no simple-pole residue: `residueAt α (G′) = 0` (the converse ingredient).
example [CharZero K] (G : RatFunc K) (α : K) : residueAt α (G′) = 0 :=
  residueAt_derivative_eq_zero G α
