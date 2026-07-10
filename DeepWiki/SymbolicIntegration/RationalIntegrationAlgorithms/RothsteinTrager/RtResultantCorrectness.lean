import DeepWiki.SymbolicIntegration.SubresultantCorrectness
import DeepWiki.SymbolicIntegration.LrtMonicLogs
import Mathlib.LinearAlgebra.Lagrange

/-! # Computable Rothstein–Trager resultant bridge
`rtResultantCompute` recovers the bivariate resultant `res_x(D, A − t·D')` by evaluation and Lagrange
interpolation on `DensePoly ℚ = List ℚ`; this file proves it realizes `rtResultant` through the `toPoly`
bridge, plus the base-change lemmas used for residue regularity. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Degree bound for a determinant with column-degree bounds, and for `rtResultant` -/

open Polynomial in
/-- If every entry of column `j` has `natDegree ≤ b j`, then `natDegree (det M) ≤ ∑ j, b j`. -/
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
/-- Each `t`-coefficient of `A.map C − C X · D'.map C` has `natDegree ≤ 1`. -/
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
/-- `rtResultant A D` has `t`-degree `≤ deg D`. -/
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

/-! ### Point-agreement: `cresultantWf` sample = `rtResultant` specialization -/

open Polynomial in
/-- `toPoly (csub A (cscale a (cderiv D))) = toPoly A − C a · derivative (toPoly D)`. -/
theorem toPoly_sample (A D : DensePoly ℚ) (a : ℚ) :
    toPoly (csub A (cscale a (cderiv D)))
      = toPoly A - Polynomial.C a * derivative (toPoly D) := by
  simp only [toPoly_eq_dense]
  rw [DensePoly.toPolyG_csubG, DensePoly.toPolyG_cscaleG, DensePoly.toPolyG_cderivG]
  simp only [toR_eq_toK, CFieldSpec.toK_rat]

open Polynomial in
/-- Point-agreement (monic `D`): `cresultantWf D (A − a·D')` evaluates the RT resultant at `a`. -/
theorem cresultantWf_sample_eq_eval (A D : DensePoly ℚ) (a : ℚ)
    (hDmonic : (toPoly D).Monic) (hAD : (toPoly A).natDegree < (toPoly D).natDegree) :
    DensePoly.cresultantWf D (csub A (cscale a (cderiv D)))
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
  rw [show DensePoly.cresultantWf D Aa
      = Polynomial.resultant (toPoly D) (toPoly Aa) (cdeg D) (cdeg Aa) from by
        simpa only [CFieldSpec.toK_rat, toPoly_eq_dense] using DensePoly.toPolyG_cresultantWf D Aa,
    rtResultant_eval, cdeg_eq_natDegree D, cdeg_eq_natDegree Aa,
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
/-- `rtResultantCompute` realizes `rtResultant` when `D` is monic and `deg A < deg D`. -/
theorem toPoly_rtResultantCompute_eq_rtResultant (A D : DensePoly ℚ)
    (hDmonic : (toPoly D).Monic) (hAD : (toPoly A).natDegree < (toPoly D).natDegree) :
    toPoly (rtResultantCompute A D) = rtResultant (toPoly A) (toPoly D) := by
  classical
  -- the abscissa list `xs`, exactly as `rtResultantCompute`'s inner `do`-block builds it
  set xs : List ℚ := (do let a ← List.range (cdeg D + 1); pure (a : ℚ)) with hxs
  set pts : List (ℚ × ℚ) :=
    xs.map (fun k : ℚ => (k, DensePoly.cresultantWf D (csub A (cscale k (cderiv D))))) with hpts
  have hcompute : rtResultantCompute A D = DensePoly.cinterpolate pts := rfl
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
    (g := toPoly (DensePoly.cinterpolate pts)) ?_ ?_ ?_ ?_
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
  · -- `degree (toPoly (DensePoly.cinterpolate pts)) < #(range (n+1))`
    rw [Finset.card_range, Nat.cast_withBot]
    have hdeg := DensePoly.degree_toPolyG_cinterpolateG_lt pts hne
    have : (toPoly (DensePoly.cinterpolate pts)).degree < (pts.length : WithBot ℕ) := by
      simpa only [toPoly_eq_dense] using hdeg
    rw [hlen] at this
    simpa [Nat.cast_withBot] using this
  · -- agree at the integer nodes
    intro i hi
    rw [Finset.mem_range] at hi
    -- the node `(↑i, yᵢ) ∈ pts`
    have hixs : (i : ℚ) ∈ xs := by
      rw [hxsmap, List.mem_map]; exact ⟨i, List.mem_range.mpr hi, rfl⟩
    have hmem : ((i : ℚ), DensePoly.cresultantWf D (csub A (cscale (i : ℚ) (cderiv D)))) ∈ pts := by
      rw [hpts, List.mem_map]
      exact ⟨(i : ℚ), hixs, rfl⟩
    have hnodup' : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup := by
      simpa only [CFieldSpec.toK_rat] using hnodup
    have heval := DensePoly.eval_toPolyG_cinterpolateG pts hnodup' hmem
    rw [show (toPoly (DensePoly.cinterpolate pts)).eval (i : ℚ)
        = DensePoly.cresultantWf D (csub A (cscale (i : ℚ) (cderiv D))) from by
      simpa only [toPoly_eq_dense, CFieldSpec.toK_rat] using heval]
    -- `cresultantWf sample = rtResultant eval` by point-agreement
    rw [cresultantWf_sample_eq_eval A D (i : ℚ) hDmonic hAD]


end DeepWiki.SymbolicIntegration.Compute

namespace DeepWiki.SymbolicIntegration

open Polynomial

/-! ### `rtResultant` under an injective base change -/

/-- `rtResultant` commutes with an injective base change `σ : K →+* L`:
`rtResultant (A.map σ) (D.map σ) = (rtResultant A D).map σ`. -/
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

/-- A nonzero scalar times `p^n` has multiplicity `n` at each root of separable `p`. -/
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


/-! ### `lrtSubresultant` under an injective base change, and the eval-commute -/

/-- `lrtSubresultant` commutes with an injective base change `ι : F →+* G`:
`(lrtSubresultant A D j).map (mapRingHom ι) = lrtSubresultant (A.map ι) (D.map ι) j`. -/
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

/-- Eval-after-map commutes with an injective base change `ι`:
`((lrtSubresultant A D j).map (evalRingHom a)).map ι = (lrtSubresultant (A.map ι) (D.map ι) j).map (evalRingHom (ι a))`. -/
theorem map_eval_lrtSubresultant_map {F G : Type*} [Field F] [Field G] (ι : F →+* G)
    (hι : Function.Injective ι) (A D : F[X]) (j : ℕ) (a : F) :
    ((lrtSubresultant A D j).map (Polynomial.evalRingHom a)).map ι
      = (lrtSubresultant (A.map ι) (D.map ι) j).map (Polynomial.evalRingHom (ι a)) := by
  rw [← lrtSubresultant_map_of_injective ι hι, Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext q
  · simp
  · simp [Polynomial.coe_mapRingHom]


end DeepWiki.SymbolicIntegration
