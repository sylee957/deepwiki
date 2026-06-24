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

end DeepWiki.SymbolicIntegration.Compute
