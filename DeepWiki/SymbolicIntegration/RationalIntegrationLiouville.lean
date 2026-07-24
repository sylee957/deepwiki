import DeepWiki.SymbolicIntegration.RationalIntegrationLogForm
import DeepWiki.SymbolicIntegration.RecognizingLogDeriv

/-! # Rational-function Liouville form
Liouville-form decompositions and logarithm-free residue criteria for rational functions. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## Splitting an arbitrary denominator into distinct-root powers -/

open Classical in
/-- A singleton nodal polynomial is `X - C α`. -/
theorem nodal_singleton (α : K) : Lagrange.nodal {α} id = (X - C α : K[X]) := by
  rw [Lagrange.nodal_eq, Finset.prod_singleton, id]

open Classical in
/-- A monic split polynomial is the product of distinct linear factors to their multiplicities. -/
theorem monic_eq_prod_distinct_roots_pow (D : K[X]) (hsplit : D.Splits) (hmonic : D.Monic) :
    D = ∏ α ∈ D.roots.toFinset, (X - C α) ^ D.roots.count α := by
  classical
  conv_lhs => rw [hsplit.eq_prod_roots_of_monic hmonic, Finset.prod_multiset_map_count]

/-! ## The rational Liouville form (Finset-sum shape) -/

open scoped Differential in
open Classical in
/-- A quotient by a monic split denominator admits a grouped-log Liouville form. -/
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
/-- Every rational function over an algebraically closed field has a grouped-log Liouville form. -/
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
/-- The grouped logarithmic sum for a singleton root set collapses to one log-derivative term. -/
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
/-- Every rational function has a flat Liouville form indexed by denominator roots. -/
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
/-- A `Finset` logarithmic derivative sum agrees with the corresponding mapped `List` sum. -/
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
/-- Every rational function has a Liouville form with logarithmic terms stored as a list. -/
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

/-! ## Residues of rational derivatives
Rational derivatives have zero simple-pole residue, and finite log sums expose their coefficients. -/

open scoped Classical in
/-- `RatFunc.eval` is zero at a quotient whose numerator is nonzero and denominator vanishes. -/
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
/-- A rational derivative has zero residue at every point. -/
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

/-! ## Flat-form coefficients
The residue functional reads the coefficient of a matching simple logarithmic derivative term. -/

open scoped Classical in
/-- Pole-free witnesses for summands combine to a pole-free witness for their `Finset` sum. -/
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
/-- The residue of a `Finset` sum equals the sum of residues read from pole-free witnesses. -/
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
/-- Vanishing flat-form residues make the rational function a rational derivative. -/
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
/-- If a rational function is a rational derivative, then every intrinsic residue vanishes. -/
theorem ratFunc_residues_zero_of_logarithmFree [CharZero K] (f : RatFunc K)
    (hf : ∃ G : RatFunc K, f = G′) (α : K) : residueAt α f = 0 := by
  obtain ⟨G, rfl⟩ := hf
  exact residueAt_derivative_eq_zero G α

open scoped Classical in
open scoped Differential in
/-- The residue of a flat logarithmic derivative sum at a member point is its coefficient. -/
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
/-- If a flat Liouville form is logarithm-free, then all flat-form coefficients vanish. -/
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
/-- Every rational function has flat residues whose vanishing gives a rational antiderivative. -/
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
/-- Every rational function has flat residues detecting whether it is a rational derivative. -/
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
