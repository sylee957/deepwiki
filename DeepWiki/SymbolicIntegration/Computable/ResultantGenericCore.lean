import DeepWiki.SymbolicIntegration.Computable.GenericBezout
import DeepWiki.SymbolicIntegration.Computable.FieldGcd
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Generic resultant/interpolation correctness over `CFieldSpec`

Correctness of the generic Lagrange interpolation `cinterpolateG` (node evaluation and degree bound)
and the seed-generic Rothstein–Trager resultant `rtResultantSeed`, read through `CFieldSpec.toK`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α]

/-! ### `cresultantG` invariances -/

/-- The product `∏_{zⱼ ∈ others}(toK zk − toK zⱼ)` is nonzero when every `toK zⱼ ≠ toK zk`. -/
theorem prodG_sub_ne_zero {zk : α} {others : List α}
    (hne : ∀ zj ∈ others, CFieldSpec.toK zj ≠ CFieldSpec.toK zk) :
    (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod ≠ 0 := by
  rw [Ne, List.prod_eq_zero_iff]
  intro hy
  rw [List.mem_map] at hy
  obtain ⟨zj, hzj, hzeq⟩ := hy
  exact hne zj hzj (sub_eq_zero.mp hzeq).symm

/-- `toPolyG` of a single Lagrange interpolation term `cscaleG (yk/denom) (clagNumG others)`. -/
theorem toPolyG_termG (zk yk : α) (others : List α) :
    toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))
      = Polynomial.C (CFieldSpec.toK yk
          / (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod)
        * (others.map (fun z => Polynomial.X - Polynomial.C (CFieldSpec.toK z))).prod := by
  rw [toPolyG_cscaleG, toPolyG_clagNumG, CFieldSpec.toK_div, toK_foldl_csub_mul, CFieldSpec.toK_one,
    one_mul]

/-- Evaluation of a generic Lagrange term at a value `x`. -/
theorem eval_toPolyG_termG (zk yk : α) (others : List α) (x : CFieldSpec.K α) :
    (toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))).eval x
      = (CFieldSpec.toK yk / (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod)
        * (others.map (fun zj => x - CFieldSpec.toK zj)).prod := by
  rw [toPolyG_termG, eval_mul, eval_C]
  congr 1
  rw [eval_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro zj _
  simp [Function.comp, eval_sub, eval_X, eval_C]

/-- A generic Lagrange term evaluated at its own node `toK zk` gives `toK yk`. -/
theorem eval_toPolyG_termG_at_self (zk yk : α) (others : List α)
    (hne : ∀ zj ∈ others, CFieldSpec.toK zj ≠ CFieldSpec.toK zk) :
    (toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk := by
  rw [eval_toPolyG_termG, div_mul_cancel₀]
  exact prodG_sub_ne_zero hne

/-- A generic Lagrange term evaluated at another node `toK x` with `x ∈ others` is `0`. -/
theorem eval_toPolyG_termG_at_other (zk yk x : α) (others : List α) (hx : x ∈ others) :
    (toPolyG (cscaleG (CField.div yk
        (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one))
        (clagNumG others))).eval (CFieldSpec.toK x) = 0 := by
  rw [eval_toPolyG_termG]
  have : (others.map (fun zj => CFieldSpec.toK x - CFieldSpec.toK zj)).prod = 0 := by
    rw [List.prod_eq_zero_iff, List.mem_map]
    exact ⟨x, hx, sub_self _⟩
  rw [this, mul_zero]

/-- The `cinterpolateG` local `term` function for a points list with abscissas `zs`. -/
private def cinterpTermG (zs : List α) (p : α × α) : CPolyG α :=
  cscaleG (CField.div p.2 ((zs.filter (fun zj => CField.isZero (CField.sub zj p.1) = false)).foldl
      (fun acc zj => CField.mul acc (CField.sub p.1 zj)) CField.one))
    (clagNumG (zs.filter (fun zj => CField.isZero (CField.sub zj p.1) = false)))

/-- `toPolyG (cinterpolateG pts)` is the normalized sum of interpolation term images. -/
theorem toPolyG_cinterpolateG (pts : List (α × α)) :
    toPolyG (cinterpolateG pts)
      = (pts.map (fun p => toPolyG (cinterpTermG (pts.map Prod.fst) p))).sum := by
  rw [cinterpolateG, toPolyG_cnormG, toPolyG_foldl_caddG]
  simp [cinterpTermG]

open scoped Classical in
/-- Summing `if toK p.1 = toK zk then toK p.2 else 0` over a points list whose abscissa images
`pts.map (toK ∘ fst)` are nodup picks out the unique entry `(zk, yk)` (`toK`-keyed). -/
theorem sum_ite_eq_of_nodup_toK_fst (pts : List (α × α))
    (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (pts.map (fun p => if CFieldSpec.toK p.1 = CFieldSpec.toK zk
        then CFieldSpec.toK p.2 else 0)).sum = CFieldSpec.toK yk := by
  induction pts with
  | nil => simp at hmem
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons]
    rw [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hpnotin, hpsnodup⟩ := hnodup
    rcases List.mem_cons.mp hmem with hpeq | hpps
    · obtain rfl := hpeq
      rw [if_pos rfl]
      have hzero : (ps.map (fun q => if CFieldSpec.toK q.1 = CFieldSpec.toK zk
          then CFieldSpec.toK q.2 else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro w hw
        rw [List.mem_map] at hw
        obtain ⟨q, hq, rfl⟩ := hw
        rw [if_neg]
        intro hqzk
        exact hpnotin (by rw [List.mem_map]; exact ⟨q, hq, hqzk⟩)
      rw [hzero, add_zero]
    · have hp1 : CFieldSpec.toK p.1 ≠ CFieldSpec.toK zk := by
        intro h
        exact hpnotin (by rw [h, List.mem_map]; exact ⟨(zk, yk), hpps, rfl⟩)
      rw [if_neg hp1, zero_add]
      exact ih hpsnodup hpps

open scoped Classical in
/-- `cinterpolateG` evaluation correctness: with abscissa images `pts.map (toK ∘ fst)` distinct in `K`,
the interpolant evaluates to `toK yk` at each node `toK zk` for `(zk, yk) ∈ pts`. -/
theorem eval_toPolyG_cinterpolateG (pts : List (α × α))
    (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (toPolyG (cinterpolateG pts)).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk := by
  rw [toPolyG_cinterpolateG]
  rw [show (List.map (fun p => toPolyG (cinterpTermG (pts.map Prod.fst) p)) pts).sum.eval
        (CFieldSpec.toK zk)
      = (Polynomial.evalRingHom (CFieldSpec.toK zk))
          (List.map (fun p => toPolyG (cinterpTermG (pts.map Prod.fst) p)) pts).sum from rfl,
    map_list_sum, List.map_map]
  set zs := pts.map Prod.fst with hzs
  have key : ∀ p ∈ pts,
      ((Polynomial.evalRingHom (CFieldSpec.toK zk)) ∘
          fun p => toPolyG (cinterpTermG zs p)) p
        = if CFieldSpec.toK p.1 = CFieldSpec.toK zk then CFieldSpec.toK p.2 else 0 := by
    rintro ⟨a, b⟩ hp
    simp only [Function.comp_apply, Polynomial.coe_evalRingHom, cinterpTermG]
    by_cases hak : CFieldSpec.toK a = CFieldSpec.toK zk
    · rw [if_pos hak, ← hak]
      apply eval_toPolyG_termG_at_self
      intro zj hzj
      rw [List.mem_filter] at hzj
      have hzj2 : CField.isZero (CField.sub zj a) = false := by
        have := hzj.2; simpa using this
      rw [Bool.eq_false_iff, Ne, CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero] at hzj2
      exact hzj2
    · rw [if_neg hak]
      apply eval_toPolyG_termG_at_other
      rw [List.mem_filter]
      refine ⟨by rw [hzs, List.mem_map]; exact ⟨(zk, yk), hmem, rfl⟩, ?_⟩
      have hgoal : CField.isZero (CField.sub zk a) = false := by
        rw [Bool.eq_false_iff, Ne, CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero]
        exact fun h => hak h.symm
      simpa using hgoal
  rw [List.map_congr_left key]
  exact sum_ite_eq_of_nodup_toK_fst pts hnodup hmem

/-- Each `cinterpolateG` term has `natDegree ≤ |others|` (a product of `|others|` linear factors). -/
theorem natDegree_toPolyG_cinterpTermG_le (zs : List α) (p : α × α) :
    (toPolyG (cinterpTermG zs p)).natDegree
      ≤ (zs.filter (fun zj => CField.isZero (CField.sub zj p.1) = false)).length := by
  obtain ⟨a, b⟩ := p
  rw [cinterpTermG, toPolyG_termG]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_map]
  refine (List.sum_le_card_nsmul _ 1 ?_).trans ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨zj, _, rfl⟩ := hx
    simp only [Function.comp_apply]
    exact natDegree_X_sub_C_le _
  · simp

/-- `cinterpolateG` degree bound: the interpolant has degree `< |pts|`. -/
theorem degree_toPolyG_cinterpolateG_lt (pts : List (α × α)) (hne : pts ≠ []) :
    (toPolyG (cinterpolateG pts)).degree < (pts.length : WithBot ℕ) := by
  rw [toPolyG_cinterpolateG]
  have hlen : 1 ≤ pts.length := List.length_pos_iff.mpr hne
  refine lt_of_le_of_lt (degree_list_sum_le_of_forall_degree_le _ ((pts.length : ℕ) - 1 : ℕ) ?_) ?_
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    apply Polynomial.degree_le_of_natDegree_le
    refine le_trans (natDegree_toPolyG_cinterpTermG_le (pts.map Prod.fst) q) ?_
    have hq1 : q.1 ∈ pts.map Prod.fst := List.mem_map.mpr ⟨q, hq, rfl⟩
    have hfilt : ((pts.map Prod.fst).filter
          (fun zj => CField.isZero (CField.sub zj q.1) = false)).length
        < (pts.map Prod.fst).length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      refine ⟨q.1, hq1, ?_⟩
      -- the predicate `isZero (q.1 − q.1) = false` is itself `false` at `q.1`
      have hz : CField.isZero (CField.sub q.1 q.1) = true := by
        rw [CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_self]
      simp [hz]
    rw [List.length_map] at hfilt
    omega
  · rw [Nat.cast_lt]; omega

/-- Restatement: generic interpolation evaluates to `toK yk` at each node `toK zk` when the node images
are distinct in `K`. -/
example (pts : List (α × α)) (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (toPolyG (cinterpolateG pts)).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk :=
  eval_toPolyG_cinterpolateG pts hnodup hmem

end CPolyG

/-! ### The seed-generic abstract Rothstein–Trager resultant `R(z) = res_t(d, a − z·Dd)` -/

variable {K : Type*} [Field K]

/-- Seed-generic Rothstein–Trager resultant `R(z) = res_t(D, A − z·Dd) ∈ K[z]`: `D, A, Dd` lifted to
`(K[z])[t]` and eliminating `t`, with formal `t`-degrees `(deg D, deg D)`. -/
noncomputable def rtResultantSeed (A D Dd : K[X]) : K[X] :=
  Polynomial.resultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * Dd.map (C : K →+* K[X]))
    D.natDegree D.natDegree

/-- `(rtResultantSeed A D Dd).eval c = res_t(D, A − c·Dd)`: specialization at `z = c`. -/
theorem rtResultantSeed_eval (A D Dd : K[X]) (c : K) :
    (rtResultantSeed A D Dd).eval c
      = Polynomial.resultant D (A - C c * Dd) D.natDegree D.natDegree := by
  have hcomp : (Polynomial.evalRingHom c).comp (C : K →+* K[X]) = RingHom.id K := by
    ext k; simp
  show Polynomial.evalRingHom c (rtResultantSeed A D Dd) = _
  rw [rtResultantSeed, ← Polynomial.resultant_map_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

/-- Restatement: the seed-generic abstract RT-resultant specializes at `z = c` to the parameter
resultant `res_t(D, A − c·Dd)`. -/
example (A D Dd : K[X]) (c : K) :
    (rtResultantSeed A D Dd).eval c
      = Polynomial.resultant D (A - C c * Dd) D.natDegree D.natDegree :=
  rtResultantSeed_eval A D Dd c

open Polynomial in
/-- If every entry of column `j` of `M : Matrix ι ι K[X]` has `natDegree ≤ b j`, then
`natDegree (det M) ≤ ∑ j, b j`. -/
theorem natDegree_det_le_sum_col {ι : Type*} [DecidableEq ι] [Fintype ι]
    (M : Matrix ι ι K[X]) (b : ι → ℕ) (hb : ∀ i j, (M i j).natDegree ≤ b j) :
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
/-- Each `t`-coefficient of `A.map C − C z · Dd.map C` has `z`-degree `≤ 1`. -/
theorem natDegree_coeff_rtResultantSeed_g_le (A Dd : K[X]) (k : ℕ) :
    ((A.map (C : K →+* K[X]) - C Polynomial.X * Dd.map (C : K →+* K[X])).coeff k).natDegree ≤ 1 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_C]; exact Nat.zero_le 1
  · refine (Polynomial.natDegree_mul_le (p := (Polynomial.X : K[X]))
      (q := Polynomial.C (Dd.coeff k))).trans ?_
    rw [Polynomial.natDegree_X, Polynomial.natDegree_C]

open Polynomial in
/-- `(rtResultantSeed A D Dd).natDegree ≤ D.natDegree`: degree in `z` bounded by `deg D`. -/
theorem natDegree_rtResultantSeed_le (A D Dd : K[X]) :
    (rtResultantSeed A D Dd).natDegree ≤ D.natDegree := by
  rw [rtResultantSeed, resultant]
  refine le_trans (natDegree_det_le_sum_col _
    (fun j => j.addCases (fun _ => 1) (fun _ => 0)) ?_) ?_
  · intro i j
    rw [Polynomial.sylvester, Matrix.of_apply]
    refine j.addCases (fun j₁ => ?_) (fun j₁ => ?_)
    · simp only [Fin.addCases_left]
      split_ifs with h
      · exact natDegree_coeff_rtResultantSeed_g_le A Dd _
      · simp
    · simp only [Fin.addCases_right]
      split_ifs with h
      · rw [Polynomial.coeff_map, Polynomial.natDegree_C]
      · simp
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    rw [Finset.sum_eq_zero (fun i _ => by rw [Fin.addCases_right])]
    omega

end DeepWiki.SymbolicIntegration
