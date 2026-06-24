import DeepWiki.SymbolicIntegration.SubresultantCorrectness
import DeepWiki.SymbolicIntegration.LrtMonicLogs
import Mathlib.LinearAlgebra.Lagrange

/-! # Correctness of the computable Rothstein–Trager resultant (`rtResultantCompute ↔ rtResultant`)
The computable `rtResultantCompute` (`RtResultantCompute`) recovers the bivariate Rothstein–Trager
resultant `R(t) = res_x(D, A − t·D')` by **evaluation + Lagrange interpolation** on `CPoly = List ℚ`.
This file proves it realizes the noncomputable `rtResultant` (`RationalIntegrationAlgorithms`) through
the `toPoly` bridge, on all inputs:

* `cinterpolate` correctness: `toPoly (cinterpolate pts)` evaluates to `yₖ` at `xₖ` and has degree
  `< #pts` (`toPoly_cinterpolate_eval`, `natDegree_toPoly_cinterpolate_lt`), via the Lagrange-basis
  numerator `clagNum`.
* point-agreement: `cresultant fuel D (A − aₖ·D')` is the specialization of `rtResultant` at `aₖ`
  (`cresultant_eq` + `rtResultant_eval`, `cresultant_sample_eq_eval`).
* `toPoly_rtResultantCompute_eq_rtResultant`: the two polynomials agree (degree `< deg D + 1`, equal at
  `deg D + 1` nodes, hence equal by `Lagrange.eq_of_degrees_lt_of_eval_index_eq`).

It then discharges the single remaining hypothesis `hLne` of Example 2.4.1's LRT closure, via the honest
`ℚ[t]` equation `rtResultant (toPoly cA241)(toPoly cD241) = 45796·(4t²+1)³` and the multiplicity-3
regularity of the LRT subresultant at the residue `α = i/2`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### `clagNum`: the Lagrange-basis numerator `∏ (x − xⱼ)` -/

/-- **`clagNum` realizes `∏ (X − C xⱼ)`**: `toPoly (clagNum xs) = ∏_{x ∈ xs} (X − C x)`. -/
theorem toPoly_clagNum (xs : List ℚ) :
    toPoly (clagNum xs) = (xs.map (fun x => Polynomial.X - Polynomial.C x)).prod := by
  induction xs with
  | nil => simp [clagNum, toPoly_cons]
  | cons x xs ih =>
    rw [clagNum, toPoly_cmul, ih, List.map_cons, List.prod_cons]
    have : toPoly [(-x), 1] = Polynomial.X - Polynomial.C x := by
      rw [toPoly_cons, toPoly_cons, toPoly_nil, map_neg, map_one]; ring
    rw [this]

/-- **`toPoly` of the `cinterpolate` accumulator fold** is the running sum: folding `cadd acc (f p)`
over `pts` maps under `toPoly` to `toPoly init + ∑ p, toPoly (f p)`. -/
theorem toPoly_foldl_cadd (f : ℚ × ℚ → CPoly) (pts : List (ℚ × ℚ)) (init : CPoly) :
    toPoly (pts.foldl (fun acc p => cadd acc (f p)) init)
      = toPoly init + (pts.map (fun p => toPoly (f p))).sum := by
  induction pts generalizing init with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih, toPoly_cadd, List.map_cons, List.sum_cons]
    ring

/-- The `cinterpolate` denominator fold `∏ acc·(xk − xⱼ)` equals the list product `∏ (xk − xⱼ)`,
threaded through an arbitrary starting accumulator. -/
theorem foldl_mul_sub_eq_prod' (xk : ℚ) (others : List ℚ) (init : ℚ) :
    others.foldl (fun acc xj => acc * (xk - xj)) init
      = init * (others.map (fun xj => xk - xj)).prod := by
  induction others generalizing init with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons]; ring

/-- The `cinterpolate` denominator fold `∏ acc·(xk − xⱼ)` equals the list product `∏ (xk − xⱼ)`. -/
theorem foldl_mul_sub_eq_prod (xk : ℚ) (others : List ℚ) :
    others.foldl (fun acc xj => acc * (xk - xj)) 1
      = (others.map (fun xj => xk - xj)).prod := by
  rw [foldl_mul_sub_eq_prod', one_mul]

/-- The product `∏_{xⱼ ∈ others} (xk − xⱼ)` is nonzero when every `xⱼ ≠ xk`. -/
theorem prod_sub_ne_zero {xk : ℚ} {others : List ℚ} (hne : ∀ xj ∈ others, xj ≠ xk) :
    (others.map (fun xj => xk - xj)).prod ≠ 0 := by
  rw [Ne, List.prod_eq_zero_iff]
  intro hy
  rw [List.mem_map] at hy
  obtain ⟨xj, hxj, hxeq⟩ := hy
  exact hne xj hxj (sub_eq_zero.mp hxeq).symm

/-- **Eval of a Lagrange term polynomial at a node** `x`: `(C (yk/denom) · ∏(X − C xⱼ)).eval x =
(yk/denom)·∏(x − xⱼ)`. -/
theorem eval_term_poly (xk yk x : ℚ) (others : List ℚ) :
    (toPoly (cscale (yk / (others.foldl (fun acc xj => acc * (xk - xj)) 1))
        (clagNum others))).eval x
      = (yk / (others.map (fun xj => xk - xj)).prod)
        * (others.map (fun xj => x - xj)).prod := by
  rw [toPoly_cscale, toPoly_clagNum, eval_mul, eval_C, foldl_mul_sub_eq_prod]
  congr 1
  rw [eval_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro xj _
  simp [Function.comp, eval_sub, eval_X, eval_C]

/-- **Eval of a Lagrange term at its own node**: the `cinterpolate` term for `(xk, yk)`, with
`others` the abscissas distinct from `xk`, evaluates to `yk` at `xk` (the denominator is the same
product, and is nonzero since each `xⱼ ≠ xk`). -/
theorem eval_term_at_self (xk yk : ℚ) (others : List ℚ) (hne : ∀ xj ∈ others, xj ≠ xk) :
    (toPoly (cscale (yk / (others.foldl (fun acc xj => acc * (xk - xj)) 1))
        (clagNum others))).eval xk = yk := by
  rw [eval_term_poly, div_mul_cancel₀]
  exact prod_sub_ne_zero hne

/-- **Eval of a Lagrange term at another node `x ∈ others`** is `0`: the numerator product
`∏_{xⱼ ∈ others}(x − xⱼ)` contains the vanishing factor `(x − x)`. -/
theorem eval_term_at_other (xk yk x : ℚ) (others : List ℚ) (hx : x ∈ others) :
    (toPoly (cscale (yk / (others.foldl (fun acc xj => acc * (xk - xj)) 1))
        (clagNum others))).eval x = 0 := by
  rw [eval_term_poly]
  have : (others.map (fun xj => x - xj)).prod = 0 := by
    rw [List.prod_eq_zero_iff, List.mem_map]
    exact ⟨x, hx, sub_self x⟩
  rw [this, mul_zero]

/-! ### `cinterpolate` evaluation and degree -/

/-- The `cinterpolate` local `term` function for a points list with abscissas `xs`. -/
private def cinterpTerm (xs : List ℚ) (p : ℚ × ℚ) : CPoly :=
  cscale (p.2 / ((xs.filter (· != p.1)).foldl (fun acc xj => acc * (p.1 - xj)) 1))
    (clagNum (xs.filter (· != p.1)))

/-- **`cinterpolate` as a normalized sum of terms**: `toPoly (cinterpolate pts) =
∑_{(xk,yk) ∈ pts} toPoly (term (xk,yk))`. -/
theorem toPoly_cinterpolate (pts : List (ℚ × ℚ)) :
    toPoly (cinterpolate pts)
      = (pts.map (fun p => toPoly (cinterpTerm (pts.map Prod.fst) p))).sum := by
  rw [cinterpolate, toPoly_cnorm, toPoly_foldl_cadd]
  simp [cinterpTerm]

/-- Summing `if p.1 = xk then p.2 else 0` over a points list with distinct abscissas picks out the
unique entry `(xk, yk)`. -/
theorem sum_ite_eq_of_nodup_fst (pts : List (ℚ × ℚ)) (hnodup : (pts.map Prod.fst).Nodup)
    {xk yk : ℚ} (hmem : (xk, yk) ∈ pts) :
    (pts.map (fun p => if p.1 = xk then p.2 else 0)).sum = yk := by
  induction pts with
  | nil => simp at hmem
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons]
    rw [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hpnotin, hpsnodup⟩ := hnodup
    rcases List.mem_cons.mp hmem with hpeq | hpps
    · -- p = (xk, yk)
      obtain rfl := hpeq
      rw [if_pos rfl]
      have hzero : (ps.map (fun q => if q.1 = xk then q.2 else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro z hz
        rw [List.mem_map] at hz
        obtain ⟨q, hq, rfl⟩ := hz
        rw [if_neg]
        intro hqxk
        exact hpnotin (by rw [List.mem_map]; exact ⟨q, hq, hqxk⟩)
      rw [hzero, add_zero]
    · -- (xk, yk) ∈ ps, so p.1 ≠ xk (else p.1 = xk would be in (ps.map fst))
      have hp1 : p.1 ≠ xk := by
        intro h
        exact hpnotin (by rw [h, List.mem_map]; exact ⟨(xk, yk), hpps, rfl⟩)
      rw [if_neg hp1, zero_add]
      exact ih hpsnodup hpps

/-- **`cinterpolate` evaluation correctness**: for a points list with **distinct abscissas**, the
interpolant evaluates to `yk` at each node `xk` — `R(xk) = yk` for `(xk, yk) ∈ pts`. The on-node term
contributes `yk`, every off-node term vanishes (its numerator contains the factor `(xk − xk)`). -/
theorem toPoly_cinterpolate_eval (pts : List (ℚ × ℚ)) (hnodup : (pts.map Prod.fst).Nodup)
    {xk yk : ℚ} (hmem : (xk, yk) ∈ pts) :
    (toPoly (cinterpolate pts)).eval xk = yk := by
  rw [toPoly_cinterpolate]
  rw [show (List.map (fun p => toPoly (cinterpTerm (pts.map Prod.fst) p)) pts).sum.eval xk
      = (Polynomial.evalRingHom xk)
          (List.map (fun p => toPoly (cinterpTerm (pts.map Prod.fst) p)) pts).sum from rfl,
    map_list_sum, List.map_map]
  set xs := pts.map Prod.fst with hxs
  -- per-term evaluation at `xk`: `yk` on-node, `0` off-node
  have key : ∀ p ∈ pts,
      ((Polynomial.evalRingHom xk) ∘ fun p => toPoly (cinterpTerm xs p)) p
        = if p.1 = xk then p.2 else 0 := by
    rintro ⟨a, b⟩ hp
    simp only [Function.comp_apply, Polynomial.coe_evalRingHom, cinterpTerm]
    by_cases hak : a = xk
    · subst hak
      rw [if_pos rfl]
      apply eval_term_at_self
      intro xj hxj
      rw [List.mem_filter] at hxj
      simpa [bne, Bool.not_eq_true'] using hxj.2
    · rw [if_neg hak]
      apply eval_term_at_other
      rw [List.mem_filter]
      exact ⟨by rw [hxs, List.mem_map]; exact ⟨(xk, yk), hmem, rfl⟩,
        by simp only [bne_iff_ne, ne_eq]; exact fun h => hak h.symm⟩
  rw [List.map_congr_left key]
  exact sum_ite_eq_of_nodup_fst pts hnodup hmem

/-- **Per-term degree bound**: each `cinterpolate` term `C(yk/denom)·∏_{xⱼ ∈ others}(X − C xⱼ)` has
`natDegree ≤ |others|` (the numerator is a product of `|others|` linear factors). -/
theorem natDegree_cinterpTerm_le (xs : List ℚ) (p : ℚ × ℚ) :
    (toPoly (cinterpTerm xs p)).natDegree ≤ (xs.filter (· != p.1)).length := by
  obtain ⟨a, b⟩ := p
  simp only [cinterpTerm, toPoly_cscale, toPoly_clagNum]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_map]
  refine (List.sum_le_card_nsmul _ 1 ?_).trans ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨xj, _, rfl⟩ := hx
    simp only [Function.comp_apply]
    exact natDegree_X_sub_C_le xj
  · simp

/-- A filtered list is no longer than the original. -/
theorem length_filter_le' (l : List ℚ) (q : ℚ → Bool) : (l.filter q).length ≤ l.length :=
  List.length_filter_le q l

/-- **`cinterpolate` degree bound**: the interpolant has degree `< |pts|`. Each term has degree
`≤ |others| = |pts.map fst| − (number of entries equal to xk) ≤ |pts| − 1`, since `xk` appears in the
abscissa list and is filtered out. The bound that, with the `|pts|` node values, determines the
interpolant uniquely. -/
theorem degree_toPoly_cinterpolate_lt (pts : List (ℚ × ℚ)) (hne : pts ≠ []) :
    (toPoly (cinterpolate pts)).degree < (pts.length : WithBot ℕ) := by
  rw [toPoly_cinterpolate]
  have hlen : 1 ≤ pts.length := List.length_pos_iff.mpr hne
  refine lt_of_le_of_lt (degree_list_sum_le_of_forall_degree_le _ ((pts.length : ℕ) - 1 : ℕ) ?_) ?_
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    apply Polynomial.degree_le_of_natDegree_le
    refine le_trans (natDegree_cinterpTerm_le (pts.map Prod.fst) q) ?_
    -- |xs.filter (≠ q.1)| ≤ |pts| − 1, since q.1 ∈ xs is removed
    have hq1 : q.1 ∈ pts.map Prod.fst := List.mem_map.mpr ⟨q, hq, rfl⟩
    have hfilt : ((pts.map Prod.fst).filter (· != q.1)).length
        < (pts.map Prod.fst).length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨q.1, hq1, by simp⟩
    rw [List.length_map] at hfilt
    omega
  · rw [Nat.cast_lt]; omega

/-! ### Degree bound for a determinant with column-degree bounds, and for `rtResultant` -/

open Polynomial in
/-- **`natDegree` of a `ℚ[X]`-matrix determinant** is bounded by the sum of per-column degree
bounds: if every entry of column `j` has `natDegree ≤ b j`, then `natDegree (det M) ≤ ∑ j, b j`. Each
`det` term is a product of one entry per column, so its degree is `≤ ∑ b j`. -/
theorem natDegree_det_le_sum_col {ι : Type*} [DecidableEq ι] [Fintype ι]
    (M : Matrix ι ι ℚ[X]) (b : ι → ℕ) (hb : ∀ i j, (M i j).natDegree ≤ b j) :
    (M.det).natDegree ≤ ∑ j, b j := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro σ _
  rw [Function.comp_apply]
  refine (natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  exact Finset.sum_le_sum (fun i _ => hb (σ i) i)

open Polynomial in
/-- **Coefficient of the `rtResultant` second polynomial has `t`-degree `≤ 1`**: each `t`-coefficient
of `A.map C − C X · D'.map C` is `C (A.coeff k) − X · C (D'.coeff k)`, degree `≤ 1` in `t`. -/
theorem natDegree_coeff_rtResultant_g_le (A D : ℚ[X]) (k : ℕ) :
    ((A.map (C : ℚ →+* ℚ[X]) - C Polynomial.X * (derivative D).map (C : ℚ →+* ℚ[X])).coeff
      k).natDegree ≤ 1 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_C]; exact Nat.zero_le 1
  · refine (Polynomial.natDegree_mul_le (p := (Polynomial.X : ℚ[X]))
      (q := Polynomial.C ((derivative D).coeff k))).trans ?_
    rw [Polynomial.natDegree_X, Polynomial.natDegree_C]

open Polynomial in
/-- **`rtResultant` has degree `≤ deg D` in `t`**: the Sylvester matrix of `D.map C` (constant
`t`-entries) and `A.map C − C X · D'.map C` (degree-`≤ 1` `t`-entries) has only the `deg D` columns from
the second polynomial carrying a `t`, so its determinant has `t`-degree `≤ deg D`. The degree side of
the interpolation uniqueness (`deg D + 1` nodes determine `R(t)`). -/
theorem natDegree_rtResultant_le (A D : ℚ[X]) :
    (rtResultant A D).natDegree ≤ D.natDegree := by
  rw [rtResultant, resultant]
  -- column-degree bound: first `m = deg D` columns (from `g`) ≤ 1, last `deg D − 1` (from `f`) = 0
  refine le_trans (natDegree_det_le_sum_col _
    (fun j => j.addCases (fun _ => 1) (fun _ => 0)) ?_) ?_
  · -- per-entry bound
    intro i j
    rw [Polynomial.sylvester, Matrix.of_apply]
    refine j.addCases (fun j₁ => ?_) (fun j₁ => ?_)
    · -- column from the second poly `g`: entry `g.coeff (i − j₁)` or 0, degree ≤ 1
      simp only [Fin.addCases_left]
      split_ifs with h
      · exact natDegree_coeff_rtResultant_g_le A D _
      · simp
    · -- column from `f = D.map C`: entry is a constant in `t`, degree 0
      simp only [Fin.addCases_right]
      split_ifs with h
      · rw [Polynomial.coeff_map, Polynomial.natDegree_C]
      · simp
  · -- ∑ b j = deg D
    rw [Fin.sum_univ_add]; simp

/-! ### Point-agreement: `cresultant` sample = `rtResultant` specialization -/

open Polynomial in
/-- **`toPoly` of the sample second polynomial**: `toPoly (A − a·D') = toPoly A − C a · derivative (toPoly D)`
where `D' = cderiv D` (the computable derivative realizes `ℚ[X]` derivative). -/
theorem toPoly_sample (A D : CPoly) (a : ℚ) :
    toPoly (csub A (cscale a (cderiv D)))
      = toPoly A - Polynomial.C a * derivative (toPoly D) := by
  rw [toPoly_csub, toPoly_cscale, toPoly_cderiv]

open Polynomial in
/-- **Point-agreement** (monic `D`): the computable resultant sample `cresultant fuel D (A − a·D')`
equals the specialization of the noncomputable Rothstein–Trager resultant at `a`,
`(rtResultant (toPoly A) (toPoly D)).eval a`. The two formal degrees `(deg D, deg D − 1)` (used by
`rtResultant`) and `(cdeg D, cdeg (A − a·D'))` (used by `cresultant`) are reconciled by
`resultant_add_right_deg`; the augmentation factor `lc(D)^k = 1` since `D` is monic. -/
theorem cresultant_sample_eq_eval (A D : CPoly) (a : ℚ)
    (hDmonic : (toPoly D).Monic) (hAD : (toPoly A).natDegree < (toPoly D).natDegree)
    (fuel : ℕ)
    (hfuel : (cnorm D).length + (cnorm (csub A (cscale a (cderiv D)))).length + 2 ≤ fuel) :
    cresultant fuel D (csub A (cscale a (cderiv D)))
      = (rtResultant (toPoly A) (toPoly D)).eval a := by
  set Aa := csub A (cscale a (cderiv D)) with hAa
  have hDpos : 0 < (toPoly D).natDegree := lt_of_le_of_lt (Nat.zero_le _) hAD
  -- `toPoly Aa = toPoly A − C a · D'`
  have htAa : toPoly Aa = toPoly A - Polynomial.C a * derivative (toPoly D) := toPoly_sample A D a
  -- actual degree bound: `deg Aa ≤ deg D − 1`
  have hAadeg : (toPoly Aa).natDegree ≤ (toPoly D).natDegree - 1 := by
    rw [htAa]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · omega
    · refine (natDegree_C_mul_le _ _).trans ?_
      exact (natDegree_derivative_le (toPoly D)).trans (by omega)
  rw [cresultant_eq fuel D Aa hfuel, rtResultant_eval, cdeg_eq_natDegree D, cdeg_eq_natDegree Aa,
    ← htAa]
  -- reconcile formal degree `deg D − 1` to actual `deg Aa` via `resultant_add_right_deg` (lc D = 1)
  obtain ⟨k, hk⟩ : ∃ k, (toPoly D).natDegree - 1 = (toPoly Aa).natDegree + k :=
    ⟨(toPoly D).natDegree - 1 - (toPoly Aa).natDegree, by omega⟩
  rw [hk, Polynomial.resultant_add_right_deg (toPoly D) (toPoly Aa) (toPoly D).natDegree
    (toPoly Aa).natDegree k le_rfl,
    show (toPoly D).coeff (toPoly D).natDegree = (toPoly D).leadingCoeff from rfl,
    hDmonic.leadingCoeff, one_pow, one_mul]

/-! ### The agreement `toPoly (rtResultantCompute …) = rtResultant …` -/

open Polynomial in
/-- **`rtResultantCompute` realizes `rtResultant`** (monic `D`, `deg A < deg D`, sufficient fuel): the
computable Rothstein–Trager resultant equals the noncomputable one through the `toPoly` bridge,
`toPoly (rtResultantCompute fuel A D) = rtResultant (toPoly A) (toPoly D)`. Both are polynomials of
degree `≤ deg D` agreeing at the `deg D + 1` integer nodes `0, …, deg D` (point-agreement
`cresultant_sample_eq_eval`), hence equal by Lagrange uniqueness
(`Lagrange.eq_of_degrees_lt_of_eval_index_eq`). The fuel hypothesis is the per-sample bound that
`cresultant_eq` needs at each node. -/
theorem toPoly_rtResultantCompute_eq_rtResultant (A D : CPoly) (fuel : ℕ)
    (hDmonic : (toPoly D).Monic) (hAD : (toPoly A).natDegree < (toPoly D).natDegree)
    (hfuel : ∀ k ∈ Finset.range (cdeg D + 1),
      (cnorm D).length + (cnorm (csub A (cscale (k : ℚ) (cderiv D)))).length + 2 ≤ fuel) :
    toPoly (rtResultantCompute fuel A D) = rtResultant (toPoly A) (toPoly D) := by
  classical
  -- the abscissa list `xs`, exactly as `rtResultantCompute`'s inner `do`-block builds it
  set xs : List ℚ := (do let a ← List.range (cdeg D + 1); pure (a : ℚ)) with hxs
  set pts : List (ℚ × ℚ) :=
    xs.map (fun k : ℚ => (k, cresultant fuel D (csub A (cscale k (cderiv D))))) with hpts
  have hcompute : rtResultantCompute fuel A D = cinterpolate pts := rfl
  -- `xs = (range (n+1)).map (↑·)`, a clean cast-mapped range
  have hxsmap : xs = (List.range (cdeg D + 1)).map (fun a : ℕ => (a : ℚ)) := by
    rw [hxs]; exact List.flatMap_pure_eq_map _ _
  have hfst : pts.map Prod.fst = xs := by
    rw [hpts, List.map_map, List.map_id'']
    intro x; rfl
  have hxsnodup : xs.Nodup := by
    rw [hxsmap]
    refine (List.nodup_range (n := cdeg D + 1)).map ?_
    intro a b h
    simpa using h
  have hnodup : (pts.map Prod.fst).Nodup := by rw [hfst]; exact hxsnodup
  have hne : pts ≠ [] := by
    rw [hpts, hxsmap]; simp [List.range_succ]
  have hlen : pts.length = cdeg D + 1 := by
    rw [hpts, hxsmap]; simp [List.length_map, List.length_range]
  -- the two polynomials, degree bounds
  rw [hcompute]
  symm
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (R := ℚ) (ι := ℕ)
    (s := Finset.range (cdeg D + 1)) (v := fun k => (k : ℚ))
    (f := rtResultant (toPoly A) (toPoly D))
    (g := toPoly (cinterpolate pts)) ?_ ?_ ?_ ?_
  · -- `Set.InjOn (Nat.cast) (range (n+1))`
    intro a _ b _ h
    simp only at h
    exact_mod_cast h
  · -- `degree (rtResultant) < #(range (n+1))`
    rw [Finset.card_range, Nat.cast_withBot]
    refine lt_of_le_of_lt (Polynomial.degree_le_natDegree) ?_
    rw [Nat.cast_withBot, WithBot.coe_lt_coe]
    have h1 := natDegree_rtResultant_le (toPoly A) (toPoly D)
    have h2 := cdeg_eq_natDegree D
    omega
  · -- `degree (toPoly (cinterpolate pts)) < #(range (n+1))`
    rw [Finset.card_range, Nat.cast_withBot]
    have := degree_toPoly_cinterpolate_lt pts hne
    rw [hlen] at this
    simpa [Nat.cast_withBot] using this
  · -- agree at the integer nodes
    intro i hi
    rw [Finset.mem_range] at hi
    -- the node `(↑i, yᵢ) ∈ pts`
    have hixs : (i : ℚ) ∈ xs := by
      rw [hxsmap, List.mem_map]; exact ⟨i, List.mem_range.mpr hi, rfl⟩
    have hmem : ((i : ℚ), cresultant fuel D (csub A (cscale (i : ℚ) (cderiv D)))) ∈ pts := by
      rw [hpts, List.mem_map]
      exact ⟨(i : ℚ), hixs, rfl⟩
    rw [toPoly_cinterpolate_eval pts hnodup hmem]
    -- `cresultant sample = rtResultant eval` by point-agreement
    rw [cresultant_sample_eq_eval A D (i : ℚ) hDmonic hAD fuel
      (hfuel i (Finset.mem_range.mpr hi))]

/-! ### Example 2.4.1: the honest `ℚ[t]` Rothstein–Trager resultant `= 45796·(4t²+1)³` -/

open Polynomial in
/-- **`toPoly cD241` is monic** (`D = x⁶−5x⁴+5x²+4` has leading coefficient 1). -/
theorem monic_toPoly_cD241 : (toPoly cD241).Monic := by
  rw [Monic, ← clead_eq_leadingCoeff]; decide

open Polynomial in
/-- **`deg A < deg D` for Example 2.4.1** (`deg A = 4 < 6 = deg D`). -/
theorem natDegree_cA241_lt_cD241 : (toPoly cA241).natDegree < (toPoly cD241).natDegree := by
  rw [← cdeg_eq_natDegree, ← cdeg_eq_natDegree]; decide

open Polynomial in
/-- **The dense `CPoly` `[45796,0,549552,0,2198208,0,2930944]` reads as `45796·(4t²+1)³`** in `ℚ[t]`. -/
theorem toPoly_ex241_value :
    toPoly ([45796, 0, 549552, 0, 2198208, 0, 2930944] : CPoly)
      = Polynomial.C 45796 * (Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 1) ^ 3 := by
  simp only [toPoly_cons, toPoly_nil, map_ofNat, map_one, map_zero]
  ring

open Polynomial in
/-- **Example 2.4.1, the honest `ℚ[t]` Rothstein–Trager resultant** (§2.4, p.48, eq 2.7): the
*noncomputable* `rtResultant (toPoly cA241) (toPoly cD241)` equals `45796·(4t²+1)³` as an honest
polynomial in `ℚ[t]`. Routes the `native_decide`-validated computation (`rtResultant_ex241`) through the
proven agreement `toPoly_rtResultantCompute_eq_rtResultant` (monic `D`, `deg A < deg D`, fuel 30) and the
closed-form read `toPoly_ex241_value`. This is the honest equation behind the residue multiplicities. -/
theorem rtResultant_ex241_eq :
    rtResultant (toPoly cA241) (toPoly cD241)
      = Polynomial.C 45796 * (Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 1) ^ 3 := by
  rw [← toPoly_rtResultantCompute_eq_rtResultant cA241 cD241 30 monic_toPoly_cD241
    natDegree_cA241_lt_cD241 (by native_decide), rtResultant_ex241, toPoly_ex241_value]

end DeepWiki.SymbolicIntegration.Compute

namespace DeepWiki.SymbolicIntegration

open Polynomial

/-! ### `rtResultant` under an injective base change -/

/-- **`rtResultant` commutes with an injective base change** `σ : K →+* L`:
`rtResultant (A.map σ) (D.map σ) = (rtResultant A D).map σ`. The injectivity preserves the formal
`x`-degrees `(deg D, deg D − 1)` (`natDegree_map_eq_of_injective`); `resultant_map_map` then pushes `σ`
through the Sylvester determinant, and `σ` commutes with `derivative`/`C`/`X`. -/
theorem rtResultant_map_of_injective {K L : Type*} [Field K] [Field L] (σ : K →+* L)
    (hσ : Function.Injective σ) (A D : K[X]) :
    rtResultant (A.map σ) (D.map σ) = (rtResultant A D).map σ := by
  rw [rtResultant, rtResultant]
  have hdeg : (D.map σ).natDegree = D.natDegree := Polynomial.natDegree_map_eq_of_injective hσ D
  -- rewrite each operand of the LHS resultant as `(operand over K[X]).map (mapRingHom σ)`
  -- the key commuting square `C ∘ σ = mapRingHom σ ∘ C`
  have hcomm : (C : L →+* L[X]).comp σ = (Polynomial.mapRingHom σ).comp (C : K →+* K[X]) := by
    ext k; simp
  have hop1 : (D.map σ).map (C : L →+* L[X])
      = (D.map (C : K →+* K[X])).map (Polynomial.mapRingHom σ) := by
    rw [Polynomial.map_map, Polynomial.map_map, hcomm]
  have hop2 : (A.map σ).map (C : L →+* L[X])
        - C Polynomial.X * (derivative (D.map σ)).map (C : L →+* L[X])
      = ((A.map (C : K →+* K[X])
          - C Polynomial.X * (derivative D).map (C : K →+* K[X]))).map
            (Polynomial.mapRingHom σ) := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C,
      Polynomial.coe_mapRingHom, Polynomial.map_map, derivative_map, Polynomial.map_map,
      Polynomial.map_map, hcomm]
    simp
  rw [hdeg, hop1, hop2]
  rw [Polynomial.resultant_map_map (f := D.map (C : K →+* K[X]))
    (g := A.map (C : K →+* K[X]) - C Polynomial.X * (derivative D).map (C : K →+* K[X]))
    (Polynomial.mapRingHom σ) (m := D.natDegree) (n := D.natDegree - 1)]
  rw [Polynomial.coe_mapRingHom]

/-! ### Root multiplicity of `C c · p³` at a simple root of `p` -/

/-- `rootMultiplicity β (p^n) = n · rootMultiplicity β p` for `p ≠ 0`. -/
theorem rootMultiplicity_pow {F : Type*} [Field F] {p : F[X]} (hp0 : p ≠ 0) (β : F) (n : ℕ) :
    Polynomial.rootMultiplicity β (p ^ n) = n * Polynomial.rootMultiplicity β p := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero m hp0) hp0), ih]
    ring

theorem rootMultiplicity_C_mul_pow_of_separable {F : Type*} [Field F] {c : F} (hc : c ≠ 0)
    {p : F[X]} (hsep : p.Separable) {β : F} (hβ : p.IsRoot β) (n : ℕ) :
    Polynomial.rootMultiplicity β (Polynomial.C c * p ^ n) = n := by
  have hp0 : p ≠ 0 := hsep.ne_zero
  have hpn0 : p ^ n ≠ 0 := pow_ne_zero n hp0
  have hCc0 : (Polynomial.C c : F[X]) ≠ 0 := by simpa [Polynomial.C_eq_zero] using hc
  -- `rootMult β (C c · pⁿ) = rootMult β (C c) + rootMult β (pⁿ)`
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hCc0 hpn0)]
  -- `rootMult β (C c) = 0`
  have hCmult : Polynomial.rootMultiplicity β (Polynomial.C c) = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    simp [Polynomial.IsRoot, hc]
  -- `rootMult β p = 1` (simple root of a separable polynomial)
  have hp1 : Polynomial.rootMultiplicity β p = 1 := by
    have hle := Polynomial.rootMultiplicity_le_one_of_separable hsep β
    have hge : 1 ≤ Polynomial.rootMultiplicity β p :=
      (Polynomial.rootMultiplicity_pos hp0).mpr hβ
    omega
  rw [hCmult, zero_add, rootMultiplicity_pow hp0, hp1, mul_one]

open scoped Classical in
/-- **`cD241` is separable** (`x⁶−5x⁴+5x²+4` is squarefree): the computable extended gcd of `D` and
`D'` is the constant `[4]` (`native_decide`), so the Bézout cofactors scaled by `1/4` witness
`a·D + b·D' = 1` (`separable_def'`). -/
theorem separable_toPoly_cD241 : (Compute.toPoly Compute.cD241).Separable := by
  rw [separable_def']
  have hbez := Compute.toPoly_cgcdExt 30 Compute.cD241 (Compute.cderiv Compute.cD241)
  rw [Compute.toPoly_cderiv] at hbez
  have hg : Compute.toPoly (Compute.cgcdExt 30 Compute.cD241 (Compute.cderiv Compute.cD241)).1
      = C 4 := by
    have : (Compute.cgcdExt 30 Compute.cD241 (Compute.cderiv Compute.cD241)).1 = [4] := by
      native_decide
    rw [this]; simp [Compute.toPoly_cons, Compute.toPoly_nil]
  rw [hg] at hbez
  refine ⟨C (4:ℚ)⁻¹ * Compute.toPoly (Compute.cgcdExt 30 Compute.cD241
            (Compute.cderiv Compute.cD241)).2.1,
          C (4:ℚ)⁻¹ * Compute.toPoly (Compute.cgcdExt 30 Compute.cD241
            (Compute.cderiv Compute.cD241)).2.2, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, hbez, ← C_mul]
  norm_num

/-- **`toPoly cR241 = 4t²+1` is separable** over `ℚ` (degree-2, distinct roots `±i/2`): it is
irreducible over `ℚ` (`irreducible_toPoly_cR241`) and `ℚ` has characteristic zero
(`Irreducible.separable`). -/
theorem separable_toPoly_cR241 : (Compute.toPoly Compute.cR241).Separable :=
  Compute.irreducible_toPoly_cR241.separable

/-! ### The multiplicity-3 nonvanishing of the LRT subresultant at the residue `α = i/2` -/

open scoped Classical in
/-- **The residue `β` is a multiplicity-3 root of the base-changed `rtResultant`** (Ex 2.4.1): over a
field `L` with an injective `τ : ℚ →+* L` and `β` a root of `(4t²+1).map τ`, the multiplicity of `β` in
`rtResultant (cA241.map τ) (cD241.map τ)` is exactly 3. From `rtResultant_map_of_injective` and the honest
equation `rtResultant_ex241_eq`, `rtResultant (…τ) = C(τ 45796)·((4t²+1).map τ)³`, and `(4t²+1).map τ` is
separable (so `β` is a simple root), so `rootMultiplicity_C_mul_pow_of_separable` gives `3`. -/
theorem rootMultiplicity_rtResultant_map_ex241 {L : Type*} [Field L] (τ : ℚ →+* L)
    (hτ : Function.Injective τ) {β : L}
    (hβ : ((Compute.toPoly Compute.cR241).map τ).IsRoot β) :
    Polynomial.rootMultiplicity β
        (rtResultant ((Compute.toPoly Compute.cA241).map τ) ((Compute.toPoly Compute.cD241).map τ))
      = 3 := by
  rw [rtResultant_map_of_injective τ hτ, Compute.rtResultant_ex241_eq]
  -- `(C 45796·(C4·X²+C1)³).map τ = C (τ 45796) · ((C4·X²+C1).map τ)³`
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow]
  set p := (Polynomial.C (4:ℚ) * Polynomial.X ^ 2 + Polynomial.C 1).map τ with hp
  -- `p = (toPoly cR241).map τ` (both `4t²+1`), so `p` is separable and `β` is a root
  have hpeq : p = (Compute.toPoly Compute.cR241).map τ := by
    rw [hp, Compute.toPoly_cR241]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_ofNat, map_ofNat, map_one]
    ring
  have hpsep : p.Separable := by rw [hpeq]; exact separable_toPoly_cR241.map
  have hpβ : p.IsRoot β := by rw [hpeq]; exact hβ
  have hc : τ 45796 ≠ 0 := by
    simpa using (map_ne_zero_iff τ hτ).mpr (by norm_num : (45796 : ℚ) ≠ 0)
  exact rootMultiplicity_C_mul_pow_of_separable hc hpsep hpβ 3

/-! ### `lrtSubresultant` under an injective base change, and the eval-commute -/

/-- **`lrtSubresultant` commutes with an injective base change** `ι : F →+* G` (lifted to the
`F[X]`-coefficients by `mapRingHom ι`): `(lrtSubresultant A D j).map (mapRingHom ι) =
lrtSubresultant (A.map ι) (D.map ι) j`. Injectivity preserves the formal `x`-degrees; `subresultant_map`
pushes `ι` through the Sylvester submatrix determinants, and `ι` commutes with `derivative`/`C`/`X`. -/
theorem lrtSubresultant_map_of_injective {F G : Type*} [Field F] [Field G] (ι : F →+* G)
    (hι : Function.Injective ι) (A D : F[X]) (j : ℕ) :
    (lrtSubresultant A D j).map (Polynomial.mapRingHom ι) = lrtSubresultant (A.map ι) (D.map ι) j := by
  rw [lrtSubresultant, lrtSubresultant]
  have hdeg : (D.map ι).natDegree = D.natDegree := Polynomial.natDegree_map_eq_of_injective hι D
  have hcomm : (C : G →+* G[X]).comp ι = (Polynomial.mapRingHom ι).comp (C : F →+* F[X]) := by
    ext k; simp
  -- rewrite the RHS operands as `(operand over F[X]).map (mapRingHom ι)`
  have hop1 : (D.map ι).map (C : G →+* G[X])
      = (D.map (C : F →+* F[X])).map (Polynomial.mapRingHom ι) := by
    rw [Polynomial.map_map, Polynomial.map_map, hcomm]
  have hop2 : (A.map ι).map (C : G →+* G[X])
          - C Polynomial.X * (derivative (D.map ι)).map (C : G →+* G[X])
      = (A.map (C : F →+* F[X])
          - C Polynomial.X * (derivative D).map (C : F →+* F[X])).map (Polynomial.mapRingHom ι) := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.coe_mapRingHom,
      Polynomial.map_X]
    congr 1
    · rw [Polynomial.map_map, hcomm, ← Polynomial.map_map]
    · congr 1
      rw [Polynomial.map_map, derivative_map, Polynomial.map_map, hcomm]
  rw [hdeg, hop1, hop2, subresultant_map]

/-- **Eval-after-map commutes with an injective base change**: for `ι : F →+* G` injective,
`((lrtSubresultant A D j).map (evalRingHom a)).map ι = (lrtSubresultant (A.map ι) (D.map ι) j).map
(evalRingHom (ι a))`. Combines `lrtSubresultant_map_of_injective` with `map_map` of the two evaluation
homs (`evalRingHom a` then `ι` vs. `mapRingHom ι` then `evalRingHom (ι a)`). -/
theorem map_eval_lrtSubresultant_map {F G : Type*} [Field F] [Field G] (ι : F →+* G)
    (hι : Function.Injective ι) (A D : F[X]) (j : ℕ) (a : F) :
    ((lrtSubresultant A D j).map (Polynomial.evalRingHom a)).map ι
      = (lrtSubresultant (A.map ι) (D.map ι) j).map (Polynomial.evalRingHom (ι a)) := by
  rw [← lrtSubresultant_map_of_injective ι hι, Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext q
  · simp
  · simp [Polynomial.coe_mapRingHom]

/-! ### Discharging `hLne` for Example 2.4.1 (the residue non-vanishing) -/

open Compute in
/-- **`(toPoly cD241).natDegree = 6`** (`D = x⁶−5x⁴+5x²+4`). -/
theorem natDegree_toPoly_cD241 : (toPoly cD241).natDegree = 6 := by
  rw [← cdeg_eq_natDegree]; decide

set_option maxHeartbeats 800000 in
open Compute in
open scoped Classical in
/-- **The residue specialization of the base-changed LRT subresultant is nonzero** (Ex 2.4.1): over
`R241 = ℚ[t]/(4t²+1)`, the degree-3 LRT subresultant of `(A.map σ, D.map σ)` specialized at the root
`α = i/2` is nonzero, `(lrtSubresultant (cA241.map σ) (cD241.map σ) 3).map (evalRingHom α) ≠ 0`. Proved by
base-changing to the algebraic closure `K̄ = AlgebraicClosure R241` (`ι` injective), where the LRT
regularity core `leadingCoeff_lrtSubresultant_eval_ne_zero` fires: the residue `β = ι α` is a root of the
base-changed `rtResultant` of *multiplicity exactly 3* (`rootMultiplicity_rtResultant_map_ex241`, from the
honest equation `rtResultant = 45796·(4t²+1)³`), so the index-3 specialized subresultant has degree 3 and
nonzero leading coefficient. The `ι`-image being nonzero reflects back through injectivity. -/
theorem lrtSubresultant_map_eval_ex241_ne_zero :
    (lrtSubresultant ((toPoly cA241).map (AdjoinRoot.of (toPoly cR241)))
        ((toPoly cD241).map (AdjoinRoot.of (toPoly cR241))) 3).map
      (Polynomial.evalRingHom (AdjoinRoot.root (toPoly cR241))) ≠ 0 := by
  classical
  set R241 := AdjoinRoot (toPoly cR241) with hR
  set σ : ℚ →+* R241 := AdjoinRoot.of (toPoly cR241) with hσ
  set α : R241 := AdjoinRoot.root (toPoly cR241) with hα
  set Kbar := AlgebraicClosure R241 with hK
  set ι : R241 →+* Kbar := algebraMap R241 Kbar with hι
  have hιinj : Function.Injective ι := FaithfulSMul.algebraMap_injective R241 Kbar
  set τ : ℚ →+* Kbar := ι.comp σ with hτ
  have hτinj : Function.Injective τ := hιinj.comp (AdjoinRoot.of (toPoly cR241)).injective
  set β : Kbar := ι α with hβdef
  -- `β` is a root of `(toPoly cR241).map τ`
  have hβroot : ((toPoly cR241).map τ).IsRoot β := by
    have hαroot : ((toPoly cR241).map σ).IsRoot α := AdjoinRoot.isRoot_root (toPoly cR241)
    rw [hτ, ← Polynomial.map_map, hβdef]
    simpa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.eval₂_hom]
      using congrArg ι hαroot
  -- separability and degree facts over `Kbar`
  have hDsep : ((toPoly cD241).map τ).Separable := separable_toPoly_cD241.map
  have hAD : ((toPoly cA241).map τ).natDegree < ((toPoly cD241).map τ).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hτinj,
      Polynomial.natDegree_map_eq_of_injective hτinj]
    exact natDegree_cA241_lt_cD241
  -- the multiplicity-3 fact
  have hmult : Polynomial.rootMultiplicity β
      (rtResultant ((toPoly cA241).map τ) ((toPoly cD241).map τ)) = 3 :=
    rootMultiplicity_rtResultant_map_ex241 τ hτinj hβroot
  -- `β` is a root of `rtResultant (A.map τ)(D.map τ)`
  have hRne : rtResultant ((toPoly cA241).map τ) ((toPoly cD241).map τ) ≠ 0 := by
    intro h0; rw [h0, Polynomial.rootMultiplicity_zero] at hmult; exact absurd hmult (by norm_num)
  have hβR : (rtResultant ((toPoly cA241).map τ) ((toPoly cD241).map τ)).IsRoot β :=
    (Polynomial.rootMultiplicity_pos hRne).mp (by rw [hmult]; norm_num)
  -- the regularity core over the algebraically closed `Kbar` at multiplicity `3 < deg D = 6`
  have hdegD6 : ((toPoly cD241).map τ).natDegree = 6 := by
    rw [Polynomial.natDegree_map_eq_of_injective hτinj]; exact natDegree_toPoly_cD241
  have hcore := leadingCoeff_lrtSubresultant_eval_ne_zero
    ((toPoly cA241).map τ) ((toPoly cD241).map τ) hDsep hAD β hβR (by rw [hmult, hdegD6]; norm_num)
  rw [hmult] at hcore
  -- so the specialized subresultant over `Kbar` is nonzero
  have hKbarne : ((lrtSubresultant ((toPoly cA241).map τ) ((toPoly cD241).map τ) 3).map
      (Polynomial.evalRingHom β)) ≠ 0 := fun h => hcore (by rw [h, Polynomial.coeff_zero])
  -- this `Kbar` object is the `ι`-image of the `R241` object; reflect nonzero back
  intro hzero
  apply hKbarne
  -- `map_eval` commute (over `R241 → Kbar`), then `A.map σ.map ι = A.map τ`, `ι α = β`
  have hmapτ : ∀ p : ℚ[X], p.map τ = (p.map σ).map ι := fun p => by rw [hτ, Polynomial.map_map]
  have hcommute := map_eval_lrtSubresultant_map ι hιinj
    ((toPoly cA241).map σ) ((toPoly cD241).map σ) 3 α
  rw [← hmapτ, ← hmapτ] at hcommute
  rw [show β = ι α from hβdef, ← hcommute, hzero, Polynomial.map_zero]

open Compute in
/-- **Example 2.4.1's `hLne` is a theorem**: `Φ (lrtSubresultant (toPoly cA241) (toPoly cD241) 3) ≠ 0`
(with `Φ = mapRingHom φ241`, `φ241 = mk (4t²+1)`). Routes the residue-specialization form
(`mapRingHom_φ241_lrtSubresultant_ex241_eq_eval`) to the proven base-changed non-vanishing
`lrtSubresultant_map_eval_ex241_ne_zero`. -/
theorem mapRingHom_φ241_lrtSubresultant_ex241_ne_zero :
    (Polynomial.mapRingHom φ241) (lrtSubresultant (toPoly cA241) (toPoly cD241) 3) ≠ 0 := by
  rw [mapRingHom_φ241_lrtSubresultant_ex241_eq_eval]
  exact lrtSubresultant_map_eval_ex241_ne_zero

end DeepWiki.SymbolicIntegration
