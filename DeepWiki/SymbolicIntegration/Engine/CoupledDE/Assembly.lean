import DeepWiki.SymbolicIntegration.Engine.CoupledDE.Basic
import DeepWiki.ComputableAlgebra.LinearAlgebraRatCorrect

/-! # Coupled-system matrix assembly faithfulness and base soundness

`cCoupledDESystem` reduces a coupled differential system to a ℚ-linear system via undetermined
coefficients; this file proves the matrix assembly faithful and derives unconditional base
soundness by discharging the cleared-check via the lawful abstract linear-solver capability. -/


namespace DeepWiki.SymbolicIntegration.DensePoly

open Polynomial

/-- `dotQ` of two `range`-maps is the `Finset.range` sum of the products. -/
theorem dotQ_range_maps (n : ℕ) (f g : ℕ → ℚ) :
    dotQ ((List.range n).map f) ((List.range n).map g)
      = ∑ i ∈ Finset.range n, f i * g i := by
  unfold dotQ
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.zipWith_append (by simp),
      List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- `getD` of a `range`-map within range. -/
theorem getD_range_map_q (f : ℕ → ℚ) (n k : ℕ) (hk : k < n) :
    ((List.range n).map f).getD k 0 = f k := by
  rw [getD_lt_gen _ _ _ (by rw [List.length_map, List.length_range]; exact hk),
    List.getElem_map, List.getElem_range]

/-- The dot of a `mulMatrixQ b d nrows` row `r` (for `r < nrows`) with the coefficient vector of a
degree-`≤ d` polynomial `y` is the `r`-th coefficient of `b * y`. -/
theorem dotQ_mulMatrixQ_row (b y : DensePoly ℚ) (d nrows r : ℕ) (hr : r < nrows)
    (hyd : y.length ≤ d + 1) :
    dotQ ((mulMatrixQ b d nrows).getD r []) ((List.range (d + 1)).map (fun i => y.getD i 0))
      = (toPoly (cmul b y)).coeff r := by
  rw [mulMatrixQ, getD_lt_gen _ r [] (by rw [List.length_map, List.length_range]; exact hr),
    List.getElem_map, List.getElem_range]
  rw [dotQ_range_maps]
  simp only [denote]
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- RHS: Σ_{j≤r} b[j]·y[r-j]; reindex j ↦ r-j to Σ_{i≤r} b[r-i]·y[i].
  rw [show (∑ k ∈ Finset.range (r + 1),
        (toPoly b).coeff k * (toPoly y).coeff (r - k))
      = ∑ i ∈ Finset.range (r + 1), (toPoly b).coeff (r - i) * (toPoly y).coeff i from by
    apply Finset.sum_nbij' (fun k => r - k) (fun i => r - i)
    · intro k hk; rw [Finset.mem_range] at hk ⊢; omega
    · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
    · intro k hk; rw [Finset.mem_range] at hk; omega
    · intro i hi; rw [Finset.mem_range] at hi; omega
    · intro k hk; rw [Finset.mem_range] at hk
      rw [show r - (r - k) = k from by omega]]
  simp only [toPolyG_coeff, toR_eq_toK, CFieldSpec.toK_rat,
    show CCommRing.zero = (0 : ℚ) from rfl]
  simp only [CPoly.coeff_dense_eq, show CCommRing.zero = (0 : ℚ) from rfl]
  -- LHS: Σ_{i<d+1} (if r≥i then b[r-i] else 0)·y[i]; RHS: Σ_{x<r+1} b[r-x]·y[x].
  -- Reduce both to the sum over the common nonzero index set.
  have hLHS : (∑ i ∈ Finset.range (d + 1), (if r ≥ i then (b:List ℚ).getD (r - i) 0 else 0)
        * (y:List ℚ).getD i 0)
      = ∑ i ∈ (Finset.range (d + 1)).filter (· ≤ r),
          (b:List ℚ).getD (r - i) 0 * (y:List ℚ).getD i 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : r ≥ i
    · rw [if_pos h, if_pos (by omega : i ≤ r)]
    · rw [if_neg h, if_neg (by omega : ¬ i ≤ r), zero_mul]
  have hRHS : (∑ i ∈ (Finset.range (d + 1)).filter (· ≤ r),
          (b:List ℚ).getD (r - i) 0 * (y:List ℚ).getD i 0)
      = ∑ x ∈ Finset.range (r + 1), (b:List ℚ).getD (r - x) 0 * (y:List ℚ).getD x 0 := by
    apply Finset.sum_subset
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [Finset.mem_range]; omega
    · intro x hx hxnot
      rw [Finset.mem_range] at hx
      rw [Finset.mem_filter, Finset.mem_range] at hxnot
      -- x ≤ r (in range r+1) but x ∉ filter ⟹ x ≥ d+1 ⟹ y[x] = 0.
      have : ¬ x < d + 1 := by
        intro h; exact hxnot ⟨h, by omega⟩
      rw [getD_long_gen y x 0 (by omega), mul_zero]
  rw [hLHS, ← hRHS]

/-- The dot of a `derivMatrixQ d nrows` row `r` (for `r < nrows`) with the coefficient vector of a
degree-`≤ d` polynomial `y` is the `r`-th coefficient of `D y` (`Polynomial.derivative`). -/
theorem dotQ_derivMatrixQ_row (y : DensePoly ℚ) (d nrows r : ℕ) (hr : r < nrows)
    (hyd : y.length ≤ d + 1) :
    dotQ ((derivMatrixQ d nrows).getD r []) ((List.range (d + 1)).map (fun i => y.getD i 0))
      = (toPoly (cderiv y)).coeff r := by
  rw [derivMatrixQ, getD_lt_gen _ r [] (by rw [List.length_map, List.length_range]; exact hr),
    List.getElem_map, List.getElem_range]
  rw [dotQ_range_maps]
  rw [toPolyG_cderivG, Polynomial.coeff_derivative, toPolyG_coeff,
    toR_eq_toK, CFieldSpec.toK_rat, show CCommRing.zero = (0 : ℚ) from rfl]
  -- LHS: Σ_{i<d+1} (if i=r+1 then i else 0)·y[i].
  by_cases hrd : r + 1 < d + 1
  · rw [Finset.sum_eq_single (r + 1)]
    · rw [if_pos rfl]
      push_cast
      ring
    · intro i _ hir; rw [if_neg hir, zero_mul]
    · intro h; exact absurd (Finset.mem_range.mpr hrd) h
  · -- r + 1 ≥ d + 1: y[r+1] = 0, and no i in range hits r+1.
    rw [getD_long_gen y (r + 1) 0 (by omega)]
    rw [Finset.sum_eq_zero]
    · simp
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [if_neg (by omega : ¬ (i = r + 1)), zero_mul]

/-- `dotQ` distributes over an append on equal-length splits:
`dotQ (a ++ b) (u ++ v) = dotQ a u + dotQ b v` when `|a| = |u|`. -/
theorem dotQ_append (a b u v : List ℚ) (h : a.length = u.length) :
    dotQ (a ++ b) (u ++ v) = dotQ a u + dotQ b v := by
  unfold dotQ
  rw [List.zipWith_append h, List.sum_append]

/-- `dotQ` distributes over a `zipWith (+)` on the left when lengths align. -/
theorem dotQ_zipWith_add (a b u : List ℚ) (hab : a.length = b.length) (hu : a.length = u.length) :
    dotQ (List.zipWith (· + ·) a b) u = dotQ a u + dotQ b u := by
  unfold dotQ
  induction a generalizing b u with
  | nil =>
    rw [List.eq_nil_of_length_eq_zero hab.symm]; simp
  | cons x xs ih =>
    cases b with
    | nil => simp at hab
    | cons y ys =>
      cases u with
      | nil => simp at hu
      | cons w ws =>
        simp only [List.zipWith_cons_cons, List.sum_cons]
        rw [ih ys ws (by simpa using hab) (by simpa using hu)]
        ring

/-- The coupled-system first-row dot equals `coeff_r (D y1 + b1 y1 + ab2 y2)`. -/
theorem dotQ_hcatRow (b1 ab2 y1 y2 : DensePoly ℚ) (d nrows r : ℕ) (hr : r < nrows)
    (hy1 : y1.length ≤ d + 1) (hy2 : y2.length ≤ d + 1) :
    dotQ ((hcatQ (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))
          (mulMatrixQ ab2 d nrows)).getD r [])
        (((List.range (d + 1)).map (fun i => y1.getD i 0))
          ++ ((List.range (d + 1)).map (fun i => y2.getD i 0)))
      = (toPoly (cderiv y1)).coeff r + (toPoly (cmul b1 y1)).coeff r
          + (toPoly (cmul ab2 y2)).coeff r := by
  have hDlen : (derivMatrixQ d nrows).length = nrows := derivMatrixQ_len d nrows
  have hB1len : (mulMatrixQ b1 d nrows).length = nrows := mulMatrixQ_len b1 d nrows
  have hmatAdd_len : (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows)).length = nrows := by
    rw [matAddQ_len, hDlen, hB1len]; simp
  have hu_len : ((List.range (d + 1)).map (fun i => y1.getD i 0)).length = d + 1 := by simp
  -- split the hcat row.
  rw [hcatQ_getD_row _ _ r (by rw [hmatAdd_len]; exact hr) (by rw [mulMatrixQ_len]; exact hr)]
  rw [dotQ_append _ _ _ _ (by
    rw [matAddQ_getD_row _ _ r (by rw [hDlen]; exact hr) (by rw [hB1len]; exact hr),
      List.length_zipWith, derivMatrixQ_row_len d nrows r hr, mulMatrixQ_row_len b1 d nrows r hr,
      hu_len]; simp)]
  -- the v-block: ab2 · y2.
  rw [dotQ_mulMatrixQ_row ab2 y2 d nrows r hr hy2]
  -- the u-block: zipWith (+) of derivMatrix and mulMatrix b1 rows.
  rw [matAddQ_getD_row _ _ r (by rw [hDlen]; exact hr) (by rw [hB1len]; exact hr)]
  rw [dotQ_zipWith_add _ _ _
    (by rw [derivMatrixQ_row_len d nrows r hr, mulMatrixQ_row_len b1 d nrows r hr])
    (by rw [derivMatrixQ_row_len d nrows r hr, hu_len])]
  rw [dotQ_derivMatrixQ_row y1 d nrows r hr hy1, dotQ_mulMatrixQ_row b1 y1 d nrows r hr hy1]

/-- The coupled-system second-row dot equals `coeff_r (b2 y1 + D y2 + b1 y2)`. -/
theorem dotQ_hcatRow2 (b1 b2 y1 y2 : DensePoly ℚ) (d nrows r : ℕ) (hr : r < nrows)
    (hy1 : y1.length ≤ d + 1) (hy2 : y2.length ≤ d + 1) :
    dotQ ((hcatQ (mulMatrixQ b2 d nrows)
          (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))).getD r [])
        (((List.range (d + 1)).map (fun i => y1.getD i 0))
          ++ ((List.range (d + 1)).map (fun i => y2.getD i 0)))
      = (toPoly (cmul b2 y1)).coeff r
          + ((toPoly (cderiv y2)).coeff r + (toPoly (cmul b1 y2)).coeff r) := by
  have hDlen : (derivMatrixQ d nrows).length = nrows := derivMatrixQ_len d nrows
  have hB1len : (mulMatrixQ b1 d nrows).length = nrows := mulMatrixQ_len b1 d nrows
  have hmatAdd_len : (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows)).length = nrows := by
    rw [matAddQ_len, hDlen, hB1len]; simp
  have hu_len : ((List.range (d + 1)).map (fun i => y1.getD i 0)).length = d + 1 := by simp
  rw [hcatQ_getD_row _ _ r (by rw [mulMatrixQ_len]; exact hr) (by rw [hmatAdd_len]; exact hr)]
  rw [dotQ_append _ _ _ _ (by rw [mulMatrixQ_row_len b2 d nrows r hr, hu_len])]
  -- u-block: b2 · y1.
  rw [dotQ_mulMatrixQ_row b2 y1 d nrows r hr hy1]
  -- v-block: matAdd row dotted with y2vec.
  rw [matAddQ_getD_row _ _ r (by rw [hDlen]; exact hr) (by rw [hB1len]; exact hr)]
  rw [dotQ_zipWith_add _ _ _
    (by rw [derivMatrixQ_row_len d nrows r hr, mulMatrixQ_row_len b1 d nrows r hr])
    (by rw [derivMatrixQ_row_len d nrows r hr]; simp)]
  rw [dotQ_derivMatrixQ_row y2 d nrows r hr hy2, dotQ_mulMatrixQ_row b1 y2 d nrows r hr hy2]

/-- `coeff r (D y1 + b1 y1 + ab2 y2) = 0` for `r ≥ nrows` when `nrows` exceeds every term's degree. -/
theorem coeff_residual_zero_of_ge (b1 ab2 y1 y2 : DensePoly ℚ) (d nrows r : ℕ)
    (hy1 : (toPoly y1).natDegree ≤ d) (hy2 : (toPoly y2).natDegree ≤ d)
    (hb1 : (toPoly b1).natDegree + d + 2 ≤ nrows)
    (hab2 : (toPoly ab2).natDegree + d + 2 ≤ nrows) (hd : d + 2 ≤ nrows)
    (hr : nrows ≤ r) :
    (toPoly (cderiv y1)).coeff r + (toPoly (cmul b1 y1)).coeff r
        + (toPoly (cmul ab2 y2)).coeff r = 0 := by
  have hderiv : (toPoly (cderiv y1)).coeff r = 0 := by
    simp only [denote]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt (Polynomial.natDegree_derivative_le _) (by omega)
  have hb1y1 : (toPoly (cmul b1 y1)).coeff r = 0 := by
    simp only [denote]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have := Polynomial.natDegree_mul_le (p := toPoly b1) (q := toPoly y1)
    omega
  have hab2y2 : (toPoly (cmul ab2 y2)).coeff r = 0 := by
    simp only [denote]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have := Polynomial.natDegree_mul_le (p := toPoly ab2) (q := toPoly y2)
    omega
  rw [hderiv, hb1y1, hab2y2]; ring

/-- Any list equals the `range`-map of its own `getD` (over its length). -/
theorem eq_range_map_getD {α : Type*} (l : List α) (d : α) :
    l = (List.range l.length).map (fun i => l.getD i d) := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    rw [List.getElem_map, List.getElem_range, getD_lt_gen _ _ _ (by simpa using h1)]

/-- The solution vector `sol` of length `2(d+1)` splits as the two coefficient blocks
`(range(d+1)).map(sol.getD ·) ++ (range(d+1)).map(sol.getD ((d+1)+·))`. -/
theorem sol_split (sol : List ℚ) (d : ℕ) (hsol : sol.length = 2 * (d + 1)) :
    sol = ((List.range (d + 1)).map (fun i => sol.getD i 0))
      ++ ((List.range (d + 1)).map (fun i => sol.getD ((d + 1) + i) 0)) := by
  conv_lhs => rw [eq_range_map_getD sol 0, hsol]
  rw [show 2 * (d + 1) = (d + 1) + (d + 1) from by ring, List.range_add, List.map_append]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp [Nat.add_comm]

/-- The coefficient vector `CPoly.coeffs z nrows` reads coefficient `k < nrows` as
`(toPoly z).coeff k`. -/
theorem coeffs_getD_toPoly (z : DensePoly ℚ) (nrows k : ℕ) (hk : k < nrows) :
    (CPoly.coeffs z nrows).getD k 0 = (toPoly z).coeff k := by
  rw [show (0 : ℚ) = CCommRing.zero from rfl, CPoly.coeffs_getD z nrows k hk,
    CPoly.coeff_dense_eq, toPolyG_coeff, toR_eq_toK,
    CFieldSpec.toK_rat, show CCommRing.zero = (0 : ℚ) from rfl]

/-- First-row identity `coeff_r(D u1 + b1 u1 + a•(b2 u2)) = coeff_r(z1)` (`r < nrows`) from a solve. -/
theorem coupledRow1_coeff_eq (a : ℚ) (b1 b2 z1 z2 : DensePoly ℚ) (d : ℕ) (sol : List ℚ)
    (nrows : ℕ) (hsollen : sol.length = 2 * (d + 1))
    (hsolve : ∀ k, k < (hcatQ (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))
        (mulMatrixQ (cscale a b2) d nrows)
      ++ hcatQ (mulMatrixQ b2 d nrows)
        (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))).length →
      dotQ ((hcatQ (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))
          (mulMatrixQ (cscale a b2) d nrows)
        ++ hcatQ (mulMatrixQ b2 d nrows)
          (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))).getD k [] ) sol
        = (CPoly.coeffs z1 nrows ++ CPoly.coeffs z2 nrows).getD k 0)
    (r : ℕ) (hr : r < nrows) :
    (toPoly (cderiv ((List.range (d + 1)).map (fun i => sol.getD i 0)))).coeff r
        + (toPoly (cmul b1 ((List.range (d + 1)).map (fun i => sol.getD i 0)))).coeff r
        + (toPoly (cmul (cscale a b2)
            ((List.range (d + 1)).map (fun i => sol.getD ((d + 1) + i) 0)))).coeff r
      = (toPoly z1).coeff r := by
  set u1 : DensePoly ℚ := (List.range (d + 1)).map (fun i => sol.getD i 0) with hu1def
  set u2 : DensePoly ℚ := (List.range (d + 1)).map (fun i => sol.getD ((d + 1) + i) 0) with hu2def
  set row1u := matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows) with hrow1u
  have hrow1u_len : row1u.length = nrows := by
    rw [hrow1u, matAddQ_len, derivMatrixQ_len, mulMatrixQ_len]; simp
  have hR1len : (hcatQ row1u (mulMatrixQ (cscale a b2) d nrows)).length = nrows := by
    rw [hcatQ, List.length_zipWith, hrow1u_len, mulMatrixQ_len]; simp
  have hkM : r < (hcatQ row1u (mulMatrixQ (cscale a b2) d nrows)
      ++ hcatQ (mulMatrixQ b2 d nrows) row1u).length := by
    rw [List.length_append, hR1len]; omega
  have heq := hsolve r hkM
  rw [getD_append_left _ _ _ _ (by rw [hR1len]; exact hr)] at heq
  rw [show sol = u1 ++ u2 from sol_split sol d hsollen] at heq
  -- rewrite the two blocks into range-map form so `dotQ_hcatRow` matches.
  rw [show u1 ++ u2 = ((List.range (d + 1)).map (fun i => u1.getD i 0))
      ++ ((List.range (d + 1)).map (fun i => u2.getD i 0)) from by
    conv_lhs => rw [eq_range_map_getD u1 0, eq_range_map_getD u2 0]
    rw [show u1.length = d + 1 from by rw [hu1def]; simp,
      show u2.length = d + 1 from by rw [hu2def]; simp]] at heq
  rw [dotQ_hcatRow b1 (cscale a b2) u1 u2 d nrows r hr (by rw [hu1def]; simp) (by rw [hu2def]; simp)]
    at heq
  rw [getD_append_left _ _ _ _ (by simpa using hr), coeffs_getD_toPoly z1 nrows r hr] at heq
  exact heq

/-- Second-row identity `coeff_r(b2 u1 + D u2 + b1 u2) = coeff_r(z2)` (`r < nrows`). -/
theorem coupledRow2_coeff_eq (a : ℚ) (b1 b2 z1 z2 : DensePoly ℚ) (d : ℕ) (sol : List ℚ)
    (nrows : ℕ) (hsollen : sol.length = 2 * (d + 1))
    (hsolve : ∀ k, k < (hcatQ (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))
        (mulMatrixQ (cscale a b2) d nrows)
      ++ hcatQ (mulMatrixQ b2 d nrows)
        (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))).length →
      dotQ ((hcatQ (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))
          (mulMatrixQ (cscale a b2) d nrows)
        ++ hcatQ (mulMatrixQ b2 d nrows)
          (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))).getD k [] ) sol
        = (CPoly.coeffs z1 nrows ++ CPoly.coeffs z2 nrows).getD k 0)
    (r : ℕ) (hr : r < nrows) :
    (toPoly (cmul b2 ((List.range (d + 1)).map (fun i => sol.getD i 0)))).coeff r
        + ((toPoly (cderiv ((List.range (d + 1)).map (fun i => sol.getD ((d + 1) + i) 0)))).coeff r
          + (toPoly (cmul b1
              ((List.range (d + 1)).map (fun i => sol.getD ((d + 1) + i) 0)))).coeff r)
      = (toPoly z2).coeff r := by
  set u1 : DensePoly ℚ := (List.range (d + 1)).map (fun i => sol.getD i 0) with hu1def
  set u2 : DensePoly ℚ := (List.range (d + 1)).map (fun i => sol.getD ((d + 1) + i) 0) with hu2def
  set row1u := matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows) with hrow1u
  have hrow1u_len : row1u.length = nrows := by
    rw [hrow1u, matAddQ_len, derivMatrixQ_len, mulMatrixQ_len]; simp
  have hR1len : (hcatQ row1u (mulMatrixQ (cscale a b2) d nrows)).length = nrows := by
    rw [hcatQ, List.length_zipWith, hrow1u_len, mulMatrixQ_len]; simp
  have hR2len : (hcatQ (mulMatrixQ b2 d nrows) row1u).length = nrows := by
    rw [hcatQ, List.length_zipWith, mulMatrixQ_len, hrow1u_len]; simp
  have hkM : nrows + r < (hcatQ row1u (mulMatrixQ (cscale a b2) d nrows)
      ++ hcatQ (mulMatrixQ b2 d nrows) row1u).length := by
    rw [List.length_append, hR1len, hR2len]; omega
  have heq := hsolve (nrows + r) hkM
  rw [getD_append_right _ _ _ _ (by rw [hR1len]; omega)] at heq
  rw [hR1len, show nrows + r - nrows = r from by omega] at heq
  rw [show sol = u1 ++ u2 from sol_split sol d hsollen] at heq
  rw [show u1 ++ u2 = ((List.range (d + 1)).map (fun i => u1.getD i 0))
      ++ ((List.range (d + 1)).map (fun i => u2.getD i 0)) from by
    conv_lhs => rw [eq_range_map_getD u1 0, eq_range_map_getD u2 0]
    rw [show u1.length = d + 1 from by rw [hu1def]; simp,
      show u2.length = d + 1 from by rw [hu2def]; simp]] at heq
  rw [dotQ_hcatRow2 b1 b2 u1 u2 d nrows r hr (by rw [hu1def]; simp) (by rw [hu2def]; simp)] at heq
  rw [getD_append_right _ _ _ _ (by simp)] at heq
  rw [CPoly.coeffs_length, show nrows + r - nrows = r from by omega,
    coeffs_getD_toPoly z2 nrows r hr] at heq
  exact heq

/-- A successful `cCoupledDESystem` solve satisfies `coupledClearedCheck … = true`, discharged from
the lawful linear-solver soundness law via the row identities and the residual degree bound. -/
theorem coupledClearedCheck_of_cCoupledDESystem [CLinearSolve ℚ] [LawfulCLinearSolve ℚ]
    (a : ℚ) (b1 b2 z1 z2 y1 y2 : DensePoly ℚ)
    (d : ℕ) (hsome : cCoupledDESystem a b1 b2 z1 z2 d = some (y1, y2)) :
    coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true := by
  rw [cCoupledDESystem_dense_eq, cCoupledDESystemWith] at hsome
  set nrows : ℕ :=
    ([cdeg b1 + d, cdeg b2 + d, cdeg z1, cdeg z2, d].foldl max 0) + 2 with hnrowsdef
  set row1u := matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows) with hrow1u
  set M : List (List ℚ) := hcatQ row1u (mulMatrixQ (cscale a b2) d nrows)
    ++ hcatQ (mulMatrixQ b2 d nrows) row1u with hMdef
  set rhs : List ℚ := CPoly.coeffs z1 nrows ++ CPoly.coeffs z2 nrows with hrhsdef
  rcases hmatch : CLinearSolve.solveUnique M rhs (2 * (d + 1)) with _ | sol
  · rw [hmatch] at hsome; exact absurd hsome (by simp)
  · rw [hmatch] at hsome
    rw [Option.some.injEq, Prod.mk.injEq] at hsome
    obtain ⟨hy1, hy2⟩ := hsome
    set u1 : DensePoly ℚ := (List.range (d + 1)).map (fun i => sol.getD i 0) with hu1def
    set u2 : DensePoly ℚ := (List.range (d + 1)).map (fun i => sol.getD ((d + 1) + i) 0) with hu2def
    -- block lengths.
    have hrow1u_len : row1u.length = nrows := by
      rw [hrow1u, matAddQ_len, derivMatrixQ_len, mulMatrixQ_len]; simp
    have hR1len : (hcatQ row1u (mulMatrixQ (cscale a b2) d nrows)).length = nrows := by
      rw [hcatQ, List.length_zipWith, hrow1u_len, mulMatrixQ_len]; simp
    have hR2len : (hcatQ (mulMatrixQ b2 d nrows) row1u).length = nrows := by
      rw [hcatQ, List.length_zipWith, mulMatrixQ_len, hrow1u_len]; simp
    have hrow1u_width : ∀ k, k < nrows → (row1u.getD k []).length = d + 1 := by
      intro k hk
      rw [hrow1u, matAddQ_getD_row _ _ k (by rw [derivMatrixQ_len]; exact hk)
        (by rw [mulMatrixQ_len]; exact hk), List.length_zipWith,
        derivMatrixQ_row_len d nrows k hk, mulMatrixQ_row_len b1 d nrows k hk]; simp
    have hM_width : ∀ r ∈ M, r.length = 2 * (d + 1) := by
      intro r hr
      rw [hMdef, List.mem_append] at hr
      rcases hr with hr | hr
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
        rw [hR1len] at hk
        rw [← getD_lt_gen _ k [] (by rw [hR1len]; exact hk),
          hcatQ_getD_row _ _ k (by rw [hrow1u_len]; exact hk) (by rw [mulMatrixQ_len]; exact hk),
          List.length_append, hrow1u_width k hk, mulMatrixQ_row_len _ d nrows k hk]; omega
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
        rw [hR2len] at hk
        rw [← getD_lt_gen _ k [] (by rw [hR2len]; exact hk),
          hcatQ_getD_row _ _ k (by rw [mulMatrixQ_len]; exact hk) (by rw [hrow1u_len]; exact hk),
          List.length_append, mulMatrixQ_row_len _ d nrows k hk, hrow1u_width k hk]; omega
    have hMlen : M.length = nrows + nrows := by rw [hMdef, List.length_append, hR1len, hR2len]
    have hrhslen : rhs.length = nrows + nrows := by simp [hrhsdef]
    have hsollen : sol.length = 2 * (d + 1) :=
      LawfulCLinearSolve.solveUnique_length M rhs _ sol hmatch
    have hsolveGeneric := LawfulCLinearSolve.solveUnique_sound M rhs (2 * (d + 1)) sol hM_width
      (by rw [hMlen, hrhslen]) hmatch
    have hsolve : ∀ k, k < M.length →
        DensePoly.dotQ (M.getD k []) sol = rhs.getD k 0 := by
      intro k hk
      have hk' := hsolveGeneric k hk
      change linearDot (M.getD k []) sol = rhs.getD k CCommRing.zero at hk'
      rw [linearDot_rat_eq_dotQ] at hk'
      exact hk'
    -- repackage hsolve with the spelled-out matrix (defeq to M via the `set`s).
    have hsolve' : ∀ k, k < (hcatQ (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))
          (mulMatrixQ (cscale a b2) d nrows)
        ++ hcatQ (mulMatrixQ b2 d nrows)
          (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))).length →
        dotQ ((hcatQ (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))
            (mulMatrixQ (cscale a b2) d nrows)
          ++ hcatQ (mulMatrixQ b2 d nrows)
            (matAddQ (derivMatrixQ d nrows) (mulMatrixQ b1 d nrows))).getD k [] ) sol
          = (CPoly.coeffs z1 nrows ++ CPoly.coeffs z2 nrows).getD k 0 := by
      rw [← hrow1u, ← hMdef, ← hrhsdef]; exact hsolve
    -- toPoly agreement (cnorm).
    have htoP_y1 : toPoly y1 = toPoly u1 := by
      rw [← hy1, CPoly.ofFn_dense_eq, ← hu1def]
      simp only [denote]
    have htoP_y2 : toPoly y2 = toPoly u2 := by
      rw [← hy2, CPoly.ofFn_dense_eq, ← hu2def]
      simp only [denote]
    have hu1deg : (toPoly u1).natDegree ≤ d := by
      have h1 : (toPoly u1).natDegree ≤ (cnorm u1 : List ℚ).length - 1 := natDegree_toPolyG_le u1
      have h2 : (cnorm u1 : List ℚ).length ≤ d + 1 := by
        have h3 := cnormG_length_le u1
        have h4 : u1.length = d + 1 := by rw [hu1def]; simp
        omega
      omega
    have hu2deg : (toPoly u2).natDegree ≤ d := by
      have h1 : (toPoly u2).natDegree ≤ (cnorm u2 : List ℚ).length - 1 := natDegree_toPolyG_le u2
      have h2 : (cnorm u2 : List ℚ).length ≤ d + 1 := by
        have h3 := cnormG_length_le u2
        have h4 : u2.length = d + 1 := by rw [hu2def]; simp
        omega
      omega
    -- degree bounds.
    have hndb1 : (toPoly b1).natDegree ≤ cdeg b1 := by rw [cdegG_eq_natDegree]
    have hndb2 : (toPoly b2).natDegree ≤ cdeg b2 := by rw [cdegG_eq_natDegree]
    have hndab2 : (toPoly (cscale a b2)).natDegree ≤ cdeg b2 := by
      simp only [denote]
      exact le_trans (Polynomial.natDegree_C_mul_le _ _) hndb2
    have hndz1 : (toPoly z1).natDegree ≤ cdeg z1 := by rw [cdegG_eq_natDegree]
    have hndz2 : (toPoly z2).natDegree ≤ cdeg z2 := by rw [cdegG_eq_natDegree]
    have hfold : ∀ x ∈ [cdeg b1 + d, cdeg b2 + d, cdeg z1, cdeg z2, d],
        x ≤ [cdeg b1 + d, cdeg b2 + d, cdeg z1, cdeg z2, d].foldl max 0 := by
      intro x hx; simp only [List.foldl_cons, List.foldl_nil]
      fin_cases hx <;> omega
    have hB1 : cdeg b1 + d ≤ nrows - 2 := by
      rw [hnrowsdef]; have := hfold (cdeg b1 + d) (by simp); omega
    have hB2 : cdeg b2 + d ≤ nrows - 2 := by
      rw [hnrowsdef]; have := hfold (cdeg b2 + d) (by simp); omega
    have hZ1 : cdeg z1 ≤ nrows - 2 := by
      rw [hnrowsdef]; have := hfold (cdeg z1) (by simp); omega
    have hZ2 : cdeg z2 ≤ nrows - 2 := by
      rw [hnrowsdef]; have := hfold (cdeg z2) (by simp); omega
    have hD : d ≤ nrows - 2 := by rw [hnrowsdef]; have := hfold d (by simp); omega
    have hge2 : 2 ≤ nrows := by rw [hnrowsdef]; omega
    rw [coupledClearedCheck_dense_eq, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · -- toPoly R1 = 0.
      rw [cisZeroG_iff]
      apply Polynomial.ext; intro r
      simp only [denote, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_zero,
        CFieldSpec.toK, id_eq, htoP_y1, htoP_y2]
      by_cases hr : r < nrows
      · have hrow := coupledRow1_coeff_eq a b1 b2 z1 z2 d sol nrows hsollen hsolve' r hr
        rw [← hu1def, ← hu2def] at hrow
        simp only [denote, CFieldSpec.toK, id_eq] at hrow
        rw [show (Polynomial.C a * toPoly b2 * toPoly u2)
            = Polynomial.C a * (toPoly b2 * toPoly u2) from by ring] at hrow
        linear_combination hrow
      · rw [not_lt] at hr
        have hz1z : (toPoly z1).coeff r = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have hres := coeff_residual_zero_of_ge b1 (cscale a b2) y1 y2 d nrows r
          (by rw [htoP_y1]; exact hu1deg) (by rw [htoP_y2]; exact hu2deg)
          (by omega) (by omega) (by omega) hr
        simp only [denote, CFieldSpec.toK, id_eq, htoP_y1, htoP_y2] at hres
        rw [show (Polynomial.C a * toPoly b2 * toPoly u2)
            = Polynomial.C a * (toPoly b2 * toPoly u2) from by ring] at hres
        linear_combination hres - hz1z
    · -- toPoly R2 = 0.
      rw [cisZeroG_iff]
      apply Polynomial.ext; intro r
      simp only [denote, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_zero,
        htoP_y1, htoP_y2]
      by_cases hr : r < nrows
      · have hrow := coupledRow2_coeff_eq a b1 b2 z1 z2 d sol nrows hsollen hsolve' r hr
        rw [← hu1def, ← hu2def] at hrow
        simp only [denote] at hrow
        linear_combination hrow
      · rw [not_lt] at hr
        have hz2z : (toPoly z2).coeff r = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have hb2y1 : (toPoly b2 * toPoly u1).coeff r = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          have := Polynomial.natDegree_mul_le (p := toPoly b2) (q := toPoly u1); omega
        have hres := coeff_residual_zero_of_ge b1 (cscale a b2) u2 u1 d nrows r hu2deg hu1deg
          (by omega) (by omega) (by omega) hr
        simp only [denote, CFieldSpec.toK, id_eq] at hres
        have hab2u1 : (Polynomial.C a * toPoly b2 * toPoly u1).coeff r = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          have h := Polynomial.natDegree_mul_le (p := Polynomial.C a * toPoly b2) (q := toPoly u1)
          have h2 := Polynomial.natDegree_C_mul_le a (toPoly b2)
          omega
        rw [hab2u1] at hres
        linear_combination hb2y1 + hres - hz2z

end DeepWiki.SymbolicIntegration.DensePoly

namespace DeepWiki.SymbolicIntegration

open DensePoly in
/-- Base coupled-system soundness: a successful `cCoupledDESystem` solve `(y₁, y₂)` satisfies the two
`ℚ[X]` identities `D(y₁) + b₁·y₁ + C a·(b₂·y₂) = z₁` and `D(y₂) + b₂·y₁ + b₁·y₂ = z₂`. -/
theorem cCoupledDESystem_sound [CLinearSolve ℚ] [LawfulCLinearSolve ℚ]
    (a : ℚ) (b1 b2 z1 z2 : DensePoly ℚ) (d : ℕ)
    (y1 y2 : DensePoly ℚ) (hsome : cCoupledDESystem a b1 b2 z1 z2 d = some (y1, y2)) :
    Polynomial.derivative (toPoly y1) + toPoly b1 * toPoly y1
        + Polynomial.C a * (toPoly b2 * toPoly y2) = toPoly z1 ∧
      Polynomial.derivative (toPoly y2) + toPoly b2 * toPoly y1
        + toPoly b1 * toPoly y2 = toPoly z2 :=
  cCoupledDESystem_sound_of_check a b1 b2 z1 z2 d y1 y2 hsome
    (DensePoly.coupledClearedCheck_of_cCoupledDESystem a b1 b2 z1 z2 y1 y2 d hsome)

end DeepWiki.SymbolicIntegration
