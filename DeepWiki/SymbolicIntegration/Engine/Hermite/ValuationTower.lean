import DeepWiki.Algebra.ListSums
import DeepWiki.Algebra.ListProducts
import DeepWiki.SymbolicIntegration.Engine.Hermite.TowerStep
import DeepWiki.SymbolicIntegration.Engine.YunSquarefreeDecomposition
import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncRegular
import Mathlib.Data.List.Sigma

/-! # `Q`-regularity over the tower fraction field

The valuation notion behind Hermite pole-cancellation
(over `ℚ`, `d/dx`) to the tower carrier `RatFunc (CFieldSpec.K α)` with the monomial derivation
`towerFractionFieldDeriv Dt`. The representation-independent predicate `IsRatFuncRegular Q f` says
`f` has a representation with denominator coprime to `Q` — i.e. no `Q`-pole. Its tower-specific
closure under the derivative uses the quotient rule `towerFractionFieldDerivG_div`. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- Dense-reader adapter for generic exact-division congruence. -/
private theorem toPoly_div_congr_dense (p₁ q₁ p₂ q₂ : DensePoly α)
    (hp : toPoly p₁ = toPoly p₂) (hq : toPoly q₁ = toPoly q₂)
    (hq₁ : toPoly q₁ ≠ 0) (hdvd₁ : toPoly q₁ ∣ toPoly p₁) :
    toPoly (CPolyEuclidean.div p₁ q₁) = toPoly (CPolyEuclidean.div p₂ q₂) := by
  simpa only [toPoly_list_eq] using
    CPolyEuclidean.toPoly_div_congr p₁ q₁ p₂ q₂
      (by simpa only [toPoly_list_eq] using hp)
      (by simpa only [toPoly_list_eq] using hq)
      (by simpa only [toPoly_list_eq] using hq₁)
      (by simpa only [toPoly_list_eq] using hdvd₁)

/-- **`Q`-regular is closed under the tower derivative** `towerFractionFieldDeriv Dt`: if `f = am p/am q`
with `q` coprime to `Q`, then `D_tower f` has denominator `q²`, still coprime to `Q`. Uses the tower
quotient rule. -/
theorem IsRatFuncRegular.towerDeriv {Q : (CFieldSpec.K α)[X]}
    {f : RatFunc (CFieldSpec.K α)} (Dt : DensePoly α)
    (hf : IsRatFuncRegular Q f) : IsRatFuncRegular Q (towerFractionFieldDeriv Dt f) := by
  obtain ⟨p, q, hq, hQ, hfeq⟩ := hf
  refine ⟨Differential.implicitDeriv (toPoly Dt) p * q - p * Differential.implicitDeriv (toPoly Dt) q,
    q ^ 2, pow_ne_zero 2 hq, hQ.pow_right, ?_⟩
  rw [hfeq, towerFractionFieldDerivG_div, map_sub, map_mul, map_mul, map_pow]

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The inner-loop `gloc` denominator is a power of `v`** (times the seed denominator): the
accumulator denominator only ever multiplies by `cpow v (j+1)`. So a factor's `gloc` denominator is
coprime to any polynomial coprime to `v` — the key to `Vk`-regularity of the other factors. -/
theorem toPolyG_cHermiteReduceTowerInnerWf_den_eq_pow (Dt v u : DensePoly α) :
    ∀ (j : ℕ) (a : DensePoly α) (g : DensePoly α × DensePoly α),
      ∃ N, toPoly (cHermiteReduceTowerInnerWf Dt v u j a g).1.2
        = toPoly g.2 * toPoly v ^ N := by
  intro j
  induction j with
  | zero => intro a g; exact ⟨0, by simp [cHermiteReduceTowerInnerWf]⟩
  | succ j ih =>
    intro a g
    rw [cHermiteReduceTowerInnerWf]
    rcases hBC : CPoly.diophantineReduced (cmul u (CPolyEngine.monomialDeriv Dt v)) v
      (cscale (CCommRing.neg (CField.inv (CField.natCast (j + 1)))) a) with ⟨b, c⟩
    obtain ⟨M, hM⟩ := ih _ (cadd (cmul g.1 (cpow v (j + 1))) (cmul b g.2),
      cmul g.2 (cpow v (j + 1)))
    refine ⟨j + 1 + M, ?_⟩
    rw [hM, toPolyG_cmulG, toPolyG_cpowG, mul_assoc, ← pow_add]

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **A factor's `gloc` fraction is `Q`-regular** whenever `Q` is coprime to `v`: the `gloc` denominator
(from the `(0,1)` seed) is `(toPoly v)^N`, coprime to `Q`. This makes the *other* factors'
contributions `Vk`-regular in the fold. -/
theorem gloc_isRatFuncRegular (Dt v u : DensePoly α) {Q : (CFieldSpec.K α)[X]} (hv : toPoly v ≠ 0)
    (hcop : IsRelPrime Q (toPoly v)) (j : ℕ) (a : DensePoly α) :
    IsRatFuncRegular Q
      (am α (toPoly (cHermiteReduceTowerInnerWf Dt v u j a
          ([CCommRing.zero], [CCommRing.one])).1.1)
        / am α (toPoly (cHermiteReduceTowerInnerWf Dt v u j a
          ([CCommRing.zero], [CCommRing.one])).1.2)) := by
  obtain ⟨N, hN⟩ := toPolyG_cHermiteReduceTowerInnerWf_den_eq_pow Dt v u j a
    ([CCommRing.zero], [CCommRing.one])
  have hden : toPoly (cHermiteReduceTowerInnerWf Dt v u j a ([CCommRing.zero], [CCommRing.one])).1.2
      = toPoly v ^ N := by
    rw [hN, show toPoly ([CCommRing.one] : DensePoly α) = 1 from by
      simp only [denote, mul_zero, add_zero, map_one], one_mul]
  exact ⟨_, _, by rw [hden]; exact pow_ne_zero N hv, by rw [hden]; exact hcop.pow_right, rfl⟩

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The guarded `gloc`-fold reads as a fraction sum.** The `cHermiteReduceTower` `g`-fold
(`foldl` with `if skip then acc else acc + gloc`) denotes `⟦init⟧ + Σ_{non-skipped} ⟦gloc⟧`, given the
seed and each non-skipped `gloc` have nonzero denominator. -/
theorem fracPair_foldl_sum {β : Type*} (glocOf : β → DensePoly α × DensePoly α) (skip : β → Prop)
    [DecidablePred skip] :
    ∀ (L : List β) (init : DensePoly α × DensePoly α), toPoly init.2 ≠ 0 →
      (∀ x ∈ L, ¬ skip x → toPoly (glocOf x).2 ≠ 0) →
      am α (toPoly (L.foldl (fun acc x => if skip x then acc
              else (cadd (cmul acc.1 (glocOf x).2) (cmul (glocOf x).1 acc.2),
                cmul acc.2 (glocOf x).2)) init).1)
          / am α (toPoly (L.foldl (fun acc x => if skip x then acc
              else (cadd (cmul acc.1 (glocOf x).2) (cmul (glocOf x).1 acc.2),
                cmul acc.2 (glocOf x).2)) init).2)
        = am α (toPoly init.1) / am α (toPoly init.2)
          + ((L.filter (fun x => ¬ skip x)).map
              (fun x => am α (toPoly (glocOf x).1) / am α (toPoly (glocOf x).2))).sum := by
  intro L
  induction L with
  | nil => intro init _ _; simp
  | cons x L ih =>
    intro init hinit hden
    rw [List.foldl_cons]
    by_cases hs : skip x
    · rw [if_pos hs, List.filter_cons_of_neg (by simp [hs]),
        ih init hinit (fun y hy => hden y (List.mem_cons_of_mem _ hy))]
    · have hgx : toPoly (glocOf x).2 ≠ 0 := hden x (List.mem_cons_self ..) hs
      have hnew : toPoly (cmul init.2 (glocOf x).2) ≠ 0 := by
        rw [toPolyG_cmulG]; exact mul_ne_zero hinit hgx
      rw [if_neg hs,
        ih _ hnew (fun y hy => hden y (List.mem_cons_of_mem _ hy)),
        List.filter_cons_of_pos (by simp [hs]), List.map_cons, List.sum_cons]
      rw [show (cadd (cmul init.1 (glocOf x).2) (cmul (glocOf x).1 init.2),
          cmul init.2 (glocOf x).2).1 = cadd (cmul init.1 (glocOf x).2)
            (cmul (glocOf x).1 init.2) from rfl,
        show (cadd (cmul init.1 (glocOf x).2) (cmul (glocOf x).1 init.2),
          cmul init.2 (glocOf x).2).2 = cmul init.2 (glocOf x).2 from rfl,
        fracPair_add init.1 init.2 (glocOf x).1 (glocOf x).2 hinit hgx]
      ring

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The guarded Hermite fold keeps a nonzero denominator: from `init.2 ≠ 0` and each non-skipped
`gloc.2 ≠ 0`, the folded `.2` is nonzero (the denominators only ever multiply). -/
theorem foldl_den_ne_zero {β : Type*} (glocOf : β → DensePoly α × DensePoly α) (skip : β → Prop)
    [DecidablePred skip] :
    ∀ (L : List β) (init : DensePoly α × DensePoly α), toPoly init.2 ≠ 0 →
      (∀ x ∈ L, ¬ skip x → toPoly (glocOf x).2 ≠ 0) →
      toPoly (L.foldl (fun acc x => if skip x then acc
              else (cadd (cmul acc.1 (glocOf x).2) (cmul (glocOf x).1 acc.2),
                cmul acc.2 (glocOf x).2)) init).2 ≠ 0 := by
  intro L
  induction L with
  | nil => intro init hinit _; exact hinit
  | cons x L ih =>
    intro init hinit hden
    rw [List.foldl_cons]
    by_cases hs : skip x
    · rw [if_pos hs]; exact ih init hinit (fun y hy => hden y (List.mem_cons_of_mem _ hy))
    · rw [if_neg hs]
      refine ih _ ?_ (fun y hy => hden y (List.mem_cons_of_mem _ hy))
      rw [toPolyG_cmulG]; exact mul_ne_zero hinit (hden x (List.mem_cons_self ..) hs)

variable [CFracGcdCoreWf α]

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The `cHermiteReduceTower` rational part `⟦g⟧` reads as `Σ_{non-skipped factors} ⟦gloc⟧`, the
guarded fold over `(cSqfreeYunFF d).zipIdx` instantiating `fracPair_foldl_sum`. -/
theorem cHermiteReduceTowerG_frac_eq_sum (Dt a d : DensePoly α)
    (hden : ∀ x ∈ (cSqfreeYunFF d).zipIdx, ¬ (x.2 + 1 ≤ 1) →
      toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a
        ([CCommRing.zero], [CCommRing.one])).1.2 ≠ 0) :
    am α (toPoly (cHermiteReduceTower Dt a d).1.1)
        / am α (toPoly (cHermiteReduceTower Dt a d).1.2)
      = (((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
          (fun x => am α (toPoly (cHermiteReduceTowerInnerWf Dt x.1
                (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a ([CCommRing.zero], [CCommRing.one])).1.1)
            / am α (toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
                (x.2 + 1 - 1) a ([CCommRing.zero], [CCommRing.one])).1.2))).sum := by
  have hone : toPoly ([CCommRing.one] : DensePoly α) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  have hz : toPoly ([CCommRing.zero] : DensePoly α) = 0 := by
    simp only [denote, mul_zero, add_zero, map_zero]
  rw [cHermiteReduceTower, squarefreeYun_dense_wf_eq]
  simp only [toPolyG_cnormG]
  rw [fracPair_foldl_sum
    (fun x => (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a
      ([CCommRing.zero], [CCommRing.one])).1)
    (fun x => x.2 + 1 ≤ 1) (cSqfreeYunFF d).zipIdx ([CCommRing.zero], [CCommRing.one])
    (by rw [hone]; exact one_ne_zero) hden]
  rw [hz, hone, map_zero, map_one, zero_div, zero_add]

/-- The `gloc` fraction of a Hermite-fold factor `x = (v, idx)` (multiplicity `idx+1`). -/
noncomputable def glocFrac (Dt a d : DensePoly α) (x : DensePoly α × ℕ) : RatFunc (CFieldSpec.K α) :=
  am α (toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a
      ([CCommRing.zero], [CCommRing.one])).1.1)
    / am α (toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a
      ([CCommRing.zero], [CCommRing.one])).1.2)

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α] in
/-- A fold factor's `gloc` fraction is `Q`-regular for `Q` coprime to its `v`. -/
theorem glocFrac_isRatFuncRegular (Dt a d : DensePoly α) {Q : (CFieldSpec.K α)[X]} (x : DensePoly α × ℕ)
    (hv : toPoly x.1 ≠ 0) (hcop : IsRelPrime Q (toPoly x.1)) :
    IsRatFuncRegular Q (glocFrac Dt a d x) :=
  gloc_isRatFuncRegular Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) hv hcop (x.2 + 1 - 1) a

/-- **`D(⟦g⟧) − D(⟦gloc_k⟧)` is `Vk`-regular** — the pole-cancellation valuation core. `⟦g⟧ = Σ⟦gloc⟧`,
so its tower derivative splits (`map_list_sum`); permuting `kelem` to the front and cancelling leaves
`Σ_{j≠k} D(⟦gloc_j⟧)`, each `Vk`-regular (`glocFrac_isRatFuncRegular.towerDeriv`, coprimality `hcop`). Tower analog
of `deriv_fold_sub_glocIncr_isQRegular`. -/
theorem deriv_fold_sub_isRatFuncRegular (Dt a d : DensePoly α) (kelem : DensePoly α × ℕ)
    (hkmem : kelem ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)))
    (hnd : ((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).Nodup)
    (hV : ∀ x ∈ (cSqfreeYunFF d).zipIdx, toPoly x.1 ≠ 0)
    (hcop : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)), x ≠ kelem →
      IsRelPrime (toPoly kelem.1) (toPoly x.1)) :
    IsRatFuncRegular (toPoly kelem.1)
      (towerFractionFieldDeriv Dt
          (am α (toPoly (cHermiteReduceTower Dt a d).1.1)
            / am α (toPoly (cHermiteReduceTower Dt a d).1.2))
        - towerFractionFieldDeriv Dt (glocFrac Dt a d kelem)) := by
  classical
  set kept := (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)) with hkeptdef
  have hone : toPoly ([CCommRing.one] : DensePoly α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero, toR_eq_toK, CFieldSpec.toK_one, map_one]
  have hden : ∀ x ∈ (cSqfreeYunFF d).zipIdx, ¬ (x.2 + 1 ≤ 1) →
      toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a
        ([CCommRing.zero], [CCommRing.one])).1.2 ≠ 0 := by
    intro x hx _
    obtain ⟨N, hN⟩ := toPolyG_cHermiteReduceTowerInnerWf_den_eq_pow Dt x.1
      (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a ([CCommRing.zero], [CCommRing.one])
    rw [hN, hone, one_mul]; exact pow_ne_zero N (hV x hx)
  -- `⟦g⟧ = Σ_{kept} glocFrac`, so `D⟦g⟧ = Σ D(glocFrac)`.
  rw [cHermiteReduceTowerG_frac_eq_sum Dt a d hden,
    map_list_sum (towerFractionFieldDeriv Dt), List.map_map, ← hkeptdef,
    (List.perm_cons_erase hkmem).map _ |>.sum_eq, List.map_cons, List.sum_cons,
    show (⇑(towerFractionFieldDeriv Dt) ∘ fun x =>
        am α (toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
            (x.2 + 1 - 1) a ([CCommRing.zero], [CCommRing.one])).1.1)
          / am α (toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
            (x.2 + 1 - 1) a ([CCommRing.zero], [CCommRing.one])).1.2)) kelem
      = towerFractionFieldDeriv Dt (glocFrac Dt a d kelem) from rfl,
    add_sub_cancel_left]
  refine isRatFuncRegular_list_sum_self _ (fun f hf => ?_)
  rw [List.mem_map] at hf
  obtain ⟨x, hx, rfl⟩ := hf
  rw [hnd.mem_erase_iff] at hx
  have hxmem : x ∈ (cSqfreeYunFF d).zipIdx := List.mem_of_mem_filter (hkeptdef ▸ hx.2)
  exact (glocFrac_isRatFuncRegular Dt a d x (hV x hxmem)
    (hcop x (hkeptdef ▸ hx.2) hx.1)).towerDeriv Dt

/-- **The total fold residual** (per-factor identities `hstep` given): `⟦a/d⟧ − D⟦g⟧ = ⟦R/d⟧` with
`R = C(1−m)·a + Σ residNum`, `m` the number of kept factors. Sums `D⟦g⟧ = Σ D⟦gloc⟧` using each
factor's `hstep : D⟦gloc x⟧ = ⟦a/d⟧ − ⟦residNum x /d⟧`. Tower analog of `total_fold_residual_over_D`. -/
theorem total_fold_residual_tower (Dt a d : DensePoly α)
    (residNum : DensePoly α × ℕ → (CFieldSpec.K α)[X]) (hd : toPoly d ≠ 0)
    (hden : ∀ x ∈ (cSqfreeYunFF d).zipIdx, ¬ (x.2 + 1 ≤ 1) →
      toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a
        ([CCommRing.zero], [CCommRing.one])).1.2 ≠ 0)
    (hstep : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      towerFractionFieldDeriv Dt (glocFrac Dt a d x)
        = am α (toPoly a) / am α (toPoly d) - am α (residNum x) / am α (toPoly d)) :
    am α (toPoly a) / am α (toPoly d)
        - towerFractionFieldDeriv Dt
            (am α (toPoly (cHermiteReduceTower Dt a d).1.1)
              / am α (toPoly (cHermiteReduceTower Dt a d).1.2))
      = am α (Polynomial.C (1 - ((((cSqfreeYunFF d).zipIdx.filter
              (fun x => ¬ (x.2 + 1 ≤ 1))).length : CFieldSpec.K α))) * toPoly a
            + (((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map residNum).sum)
        / am α (toPoly d) := by
  set kept := (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)) with hkeptdef
  have had : am α (toPoly d) ≠ 0 := am_ne_zero hd
  rw [cHermiteReduceTowerG_frac_eq_sum Dt a d hden, map_list_sum (towerFractionFieldDeriv Dt),
    List.map_map, ← hkeptdef]
  -- rewrite each `D⟦gloc⟧` via `hstep`, so the summed function is `a/d − residNum/d`.
  have heq : (kept.map (⇑(towerFractionFieldDeriv Dt) ∘ fun x =>
        am α (toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
            (x.2 + 1 - 1) a ([CCommRing.zero], [CCommRing.one])).1.1)
          / am α (toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
            (x.2 + 1 - 1) a ([CCommRing.zero], [CCommRing.one])).1.2)))
      = kept.map (fun x => am α (toPoly a) / am α (toPoly d)
          - am α (residNum x) / am α (toPoly d)) := by
    apply List.map_congr_left; intro x hx; exact hstep x hx
  rw [heq, list_sum_map_const_sub]
  -- `Σ (residNum x /d) = am (Σ residNum) / d`.
  have hsumdiv : (kept.map (fun x => am α (residNum x) / am α (toPoly d))).sum
      = am α (kept.map residNum).sum / am α (toPoly d) := by
    rw [list_sum_map_div, map_list_sum (am α), List.map_map]; rfl
  have hCcast : am α (Polynomial.C (1 - (kept.length : CFieldSpec.K α)))
      = 1 - (kept.length : RatFunc (CFieldSpec.K α)) := by
    rw [am, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, map_sub, map_one,
      map_natCast]
  rw [hsumdiv, nsmul_eq_mul, map_add, map_mul, hCcast]
  field_simp
  ring

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α] in
/-- **Per-factor order bound `vk^e ∣ R`.** From the total-fold residual (`af − Dg = ⟦R/D⟧`), the
factor-`k` step (`Dgk = af − ⟦residNum_k/D⟧`), `Vk`-regularity of `Dg − Dgk` (`deriv_fold_sub`),
`vk^(e+1) ∣ D`, and `vk^e ∣ residNum_k`: `vk^(e+1) ∣ (residNum_k − R)` by order extraction, and
`vk^e ∣ residNum_k` gives `vk^e ∣ R`. Tower analog of `dvd_residNum_factor`. -/
theorem dvd_R_of_factor {vk R residNum_k : (CFieldSpec.K α)[X]}
    {af Dg Dgk : RatFunc (CFieldSpec.K α)} (e : ℕ) (D : DensePoly α) (hD : toPoly D ≠ 0)
    (hR : af - Dg = am α R / am α (toPoly D))
    (hstepk : Dgk = af - am α residNum_k / am α (toPoly D))
    (hderiv : IsRatFuncRegular vk (Dg - Dgk))
    (hpow : vk ^ (e + 1) ∣ toPoly D) (hresk : vk ^ e ∣ residNum_k) :
    vk ^ e ∣ R := by
  have hDg : Dg = af - am α R / am α (toPoly D) := by linear_combination -hR
  have heq : Dg - Dgk = am α (residNum_k - R) / am α (toPoly D) := by
    rw [hDg, hstepk, map_sub, sub_div]; ring
  rw [heq] at hderiv
  have hdvd : vk ^ (e + 1) ∣ residNum_k - R := dvd_num_of_isRatFuncRegular hD hpow hderiv
  have h1 : vk ^ e ∣ residNum_k - R := (pow_dvd_pow vk (Nat.le_succ e)).trans hdvd
  have h2 : vk ^ e ∣ residNum_k - (residNum_k - R) := dvd_sub hresk h1
  simpa using h2

omit [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α] in
/-- **Discharge of M2's Bézout hypothesis** from the gcd coprimality of `(u·Dv, v)`: for every step
`(j', A')`, `CPoly.diophantineReduced`'s cofactors satisfy `b·(u·Dv) + c·v = −A'·C((j'+1)⁻¹)`. Uses
`toPolyG_diophantineReduced`; the coprimality `gcd(u·Dv, v)` degree-0/nonzero is the input (from `v`
squarefree + coprime to `u`). -/
theorem cHermiteInner_hbez_of_gcd (Dt v u : DensePoly α)
    (hqn : cnorm v ≠ [])
    (hgdeg : (toPoly (CPolyEuclidean.gcdExt (cmul u (CPolyEngine.monomialDeriv Dt v)) v).1).natDegree = 0)
    (hgne : toPoly (CPolyEuclidean.gcdExt (cmul u (CPolyEngine.monomialDeriv Dt v)) v).1 ≠ 0) :
    ∀ (j' : ℕ) (A' : DensePoly α),
      toPoly (CPoly.diophantineReduced (cmul u (CPolyEngine.monomialDeriv Dt v)) v
            (cscale (CCommRing.neg (CField.inv (CField.natCast (j' + 1)))) A')).1
          * (toPoly u * Differential.implicitDeriv (toPoly Dt) (toPoly v))
        + toPoly (CPoly.diophantineReduced (cmul u (CPolyEngine.monomialDeriv Dt v)) v
            (cscale (CCommRing.neg (CField.inv (CField.natCast (j' + 1)))) A')).2 * toPoly v
      = -toPoly A' * Polynomial.C (((j' : CFieldSpec.K α) + 1)⁻¹) := by
  intro j' A'
  have h := toPolyG_diophantineReduced (cmul u (CPolyEngine.monomialDeriv Dt v)) v
    (cscale (CCommRing.neg (CField.inv (CField.natCast (j' + 1)))) A') hqn hgdeg hgne
  rw [toPolyG_cmulG, toPolyG_cmonomialDeriv] at h
  rw [h, toPolyG_cscaleG, toR_eq_toK, CFieldSpec.toK_neg, CFieldSpec.toK_inv, CFieldSpec.toK_natCast,
    Nat.cast_add_one, Polynomial.C_neg]
  ring

omit [CFracGcdCoreWf α] in
/-- **The per-factor `hstep` identity** (`D⟦gloc x⟧ = ⟦a/d⟧ − ⟦residNum/d⟧`), from M2 and the isolated
inputs: `d ≠ 0`, the gcd coprimality of `(u·Dv, v)` (`hgdeg`/`hgne`), and `u·v^i = d` (`hud`, from
`v^i ∣ d`). Here `residNum = afin · v^(i−1)` (`afin` the inner-loop residual). -/
theorem glocFracG_step_identity [CharZero (CFieldSpec.K α)] (Dt a d : DensePoly α) (x : DensePoly α × ℕ)
    (hd : toPoly d ≠ 0) (hv : toPoly x.1 ≠ 0)
    (hgdeg : (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
        (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0)
    (hgne : toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
        (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hud : toPoly (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) * toPoly x.1 ^ (x.2 + 1) = toPoly d) :
    towerFractionFieldDeriv Dt (glocFrac Dt a d x)
      = am α (toPoly a) / am α (toPoly d)
        - am α (toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
              (x.2 + 1 - 1) a ([CCommRing.zero], [CCommRing.one])).2 * toPoly x.1 ^ x.2)
          / am α (toPoly d) := by
  set u := CPolyEuclidean.div d (cpow x.1 (x.2 + 1)) with hudef
  have hu : toPoly u ≠ 0 := fun h0 => hd (by rw [← hud, h0, zero_mul])
  have hqn : cnorm x.1 ≠ [] := fun h => hv ((cisZeroG_iff x.1).mp (by simp [cisZero, h]))
  have hone : toPoly ([CCommRing.one] : DensePoly α) ≠ 0 := by
    rw [show toPoly ([CCommRing.one] : DensePoly α) = 1 from by
      simp only [denote, mul_zero, add_zero, map_one]]
    exact one_ne_zero
  have hbez := cHermiteInner_hbez_of_gcd Dt x.1 u hqn hgdeg hgne
  have hM2 := cHermiteReduceTowerInnerWf_spec_acc Dt x.1 u hu hv hbez x.2 a
    ([CCommRing.zero], [CCommRing.one]) hone
  -- the seed fraction ⟦0/1⟧ = 0.
  have hz : am α (toPoly ([CCommRing.zero] : DensePoly α)) = 0 := by
    simp only [denote, mul_zero, add_zero, map_zero]
  have ho : am α (toPoly ([CCommRing.one] : DensePoly α)) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  rw [hz, ho, zero_div, map_zero, add_zero] at hM2
  -- `am u · am v^(i) = am d`.
  have hamud : am α (toPoly u) * am α (toPoly x.1) ^ (x.2 + 1) = am α (toPoly d) := by
    rw [← map_pow, ← map_mul, hud]
  have had : am α (toPoly d) ≠ 0 := am_ne_zero hd
  have hav : am α (toPoly x.1) ≠ 0 := am_ne_zero hv
  have hau : am α (toPoly u) ≠ 0 := am_ne_zero hu
  -- rearrange M2 to `D⟦gloc⟧ = am a/(am u·am v^i) − am afin/(am u·am v)`.
  rw [show towerFractionFieldDeriv Dt (glocFrac Dt a d x)
      = am α (toPoly a) / (am α (toPoly u) * am α (toPoly x.1) ^ (x.2 + 1))
        - am α (toPoly (cHermiteReduceTowerInnerWf Dt x.1 u x.2 a
            ([CCommRing.zero], [CCommRing.one])).2) / (am α (toPoly u) * am α (toPoly x.1)) from by
      rw [glocFrac]; simp only [Nat.add_sub_cancel]; linear_combination -hM2]
  rw [Nat.add_sub_cancel, map_mul, map_pow, ← hamud]
  have hvp : am α (toPoly x.1) ^ (x.2 + 1) ≠ 0 := pow_ne_zero _ hav
  field_simp
  ring

/-- The per-factor residual numerator `residNum x = afin · v^(i−1)` (`afin` the inner-loop residual). -/
noncomputable def residNum (Dt a d : DensePoly α) (x : DensePoly α × ℕ) : (CFieldSpec.K α)[X] :=
  toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a
    ([CCommRing.zero], [CCommRing.one])).2 * toPoly x.1 ^ x.2

/-- **All per-factor `hstep` identities** hold, given the per-factor gcd coprimality (`hcopgcd`, the
standard Hermite precondition — the single remaining frontier). Discharges `hv`/`hpow`/`hud` from the
Yun structural facts (`get_ne_zero`, `pow_dvd`, `cdivWf_pow_mul`) via the zipIdx→get bridge. -/
theorem all_hstep [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      towerFractionFieldDeriv Dt (glocFrac Dt a d x)
        = am α (toPoly a) / am α (toPoly d)
          - am α (residNum Dt a d x) / am α (toPoly d) := by
  intro x hx
  have hxzip : x ∈ (cSqfreeYunFF d).zipIdx := List.mem_of_mem_filter hx
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hxzip))
  have hv : toPoly x.1 ≠ 0 := by
    rw [← hget]; exact cSqfreeYunFFG_get_ne_zero hgcd d hd0 hpp x.2 hidx
  have hpow : toPoly x.1 ^ (x.2 + 1) ∣ toPoly d := by
    rw [← hget, add_comm]; exact cSqfreeYunFFG_pow_dvd hgcd d hd0 hpp x.2 hidx
  have hud := toPolyG_cdivWf_pow_mul d x.1 (x.2 + 1) hv hpow
  exact glocFracG_step_identity Dt a d x hd0 hv (hcopgcd x hx).1 (hcopgcd x hx).2 hud

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The gloc denominators are nonzero (`= v^N`, `v` a nonzero Yun factor) — the `hden` input of both
`cHermiteReduceTowerG_frac_eq_sum` and `total_fold_residual_tower`. -/
theorem hden_of [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0) :
    ∀ x ∈ (cSqfreeYunFF d).zipIdx, ¬ (x.2 + 1 ≤ 1) →
      toPoly (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a
        ([CCommRing.zero], [CCommRing.one])).1.2 ≠ 0 := by
  intro x hx _
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx))
  have hv : toPoly x.1 ≠ 0 := by
    rw [← hget]; exact cSqfreeYunFFG_get_ne_zero hgcd d hd0 hpp x.2 hidx
  obtain ⟨N, hN⟩ := toPolyG_cHermiteReduceTowerInnerWf_den_eq_pow Dt x.1
    (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a ([CCommRing.zero], [CCommRing.one])
  rw [hN, show toPoly ([CCommRing.one] : DensePoly α) = 1 from by
    simp only [denote, mul_zero, add_zero, map_one], one_mul]
  exact pow_ne_zero N hv

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The Hermite fold denominator `gden` is nonzero** (`toPoly (cHermiteReduceTower …).1.2 ≠ 0`):
the guarded fold starts at `1` and only multiplies nonzero `gloc` denominators (`hden_of`), so
`foldl_den_ne_zero` gives the result. Discharges `hgd0`. -/
theorem toPolyG_cHermiteReduceTowerG_den_ne_zero [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hpp : (toPoly d).primPart ≠ 0) :
    toPoly (cHermiteReduceTower Dt a d).1.2 ≠ 0 := by
  have hone : toPoly ([CCommRing.one] : DensePoly α) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  rw [cHermiteReduceTower, squarefreeYun_dense_wf_eq]
  simp only [toPolyG_cnormG]
  exact foldl_den_ne_zero
    (fun x => (cHermiteReduceTowerInnerWf Dt x.1 (CPolyEuclidean.div d (cpow x.1 (x.2 + 1))) (x.2 + 1 - 1) a
      ([CCommRing.zero], [CCommRing.one])).1)
    (fun x => x.2 + 1 ≤ 1) (cSqfreeYunFF d).zipIdx ([CCommRing.zero], [CCommRing.one])
    (by rw [hone]; exact one_ne_zero) (hden_of hgcd Dt a d hd0 hpp)

/-- **The `R` residual identity** `⟦a/d⟧ − D⟦g⟧ = ⟦R/d⟧` (`R = C(1−m)·a + Σ residNum`), from
`total_fold_residual_tower` fed by `all_hstep` and `hden_of`. Modulo the per-factor gcd coprimality. -/
theorem R_residual_identity [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    am α (toPoly a) / am α (toPoly d)
        - towerFractionFieldDeriv Dt
            (am α (toPoly (cHermiteReduceTower Dt a d).1.1)
              / am α (toPoly (cHermiteReduceTower Dt a d).1.2))
      = am α (Polynomial.C (1 - ((((cSqfreeYunFF d).zipIdx.filter
              (fun x => ¬ (x.2 + 1 ≤ 1))).length : CFieldSpec.K α))) * toPoly a
            + (((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
                (residNum Dt a d)).sum)
        / am α (toPoly d) :=
  total_fold_residual_tower Dt a d (residNum Dt a d) hd0 (hden_of hgcd Dt a d hd0 hpp)
    (all_hstep hgcd Dt a d hd0 hpp hcopgcd)

/-- **Each `vk^idx` divides `R`** (the per-factor order bounds), by `dvd_R_of_factor` fed by the `R`
residual identity, `all_hstep`, `deriv_fold_sub`, `hpow`, and `hresk = dvd_mul_left`. The `hV`/`hnd`/`hcop`
inputs to `deriv_fold_sub` are the Yun structural facts. Modulo the per-factor gcd coprimality. -/
theorem all_vkidx_dvd_R [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      toPoly x.1 ^ x.2 ∣ (Polynomial.C (1 - ((((cSqfreeYunFF d).zipIdx.filter
              (fun x => ¬ (x.2 + 1 ≤ 1))).length : CFieldSpec.K α))) * toPoly a
            + (((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
                (residNum Dt a d)).sum) := by
  have hV : ∀ y ∈ (cSqfreeYunFF d).zipIdx, toPoly y.1 ≠ 0 := by
    intro y hy
    obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
      (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hy))
    rw [← hget]; exact cSqfreeYunFFG_get_ne_zero hgcd d hd0 hpp y.2 hidx
  have hnd : ((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).Nodup :=
    (List.Nodup.of_map Prod.snd (List.nodup_zipIdx_map_snd _)).filter _
  have hRid := R_residual_identity hgcd Dt a d hd0 hpp hcopgcd
  intro x hx
  obtain ⟨hxidx, hxget⟩ := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using (List.mem_of_mem_filter hx)))
  have hcop : ∀ y ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)), y ≠ x →
      IsRelPrime (toPoly x.1) (toPoly y.1) := by
    intro y hy hyx
    obtain ⟨hyidx, hyget⟩ := List.getElem?_eq_some_iff.mp
      (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using (List.mem_of_mem_filter hy)))
    have hne2 : x.2 ≠ y.2 := by
      intro h; apply hyx
      refine Prod.ext ?_ h.symm
      rw [← hyget, ← hxget]; exact getElem_congr rfl h.symm hyidx
    rw [← hxget, ← hyget]
    exact cSqfreeYunFFG_isRelPrime hgcd d hd0 hpp hxidx hyidx hne2
  have hderiv := deriv_fold_sub_isRatFuncRegular Dt a d x hx hnd hV hcop
  have hstepk := all_hstep hgcd Dt a d hd0 hpp hcopgcd x hx
  have hpow : toPoly x.1 ^ (x.2 + 1) ∣ toPoly d := by
    rw [← hxget, add_comm]; exact cSqfreeYunFFG_pow_dvd hgcd d hd0 hpp x.2 hxidx
  have hresk : toPoly x.1 ^ x.2 ∣ residNum Dt a d x := by rw [residNum]; exact dvd_mul_left _ _
  exact dvd_R_of_factor x.2 d hd0 hRid hstepk hderiv hpow hresk

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The kept factor powers `vk^idx` are pairwise relatively prime (distinct Yun factors coprime,
`IsRelPrime.pow`). -/
theorem powers_pairwise_coprime [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0) :
    List.Pairwise IsRelPrime
      (((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
        (fun x => toPoly x.1 ^ x.2)) := by
  rw [List.pairwise_map]
  apply List.Pairwise.sublist List.filter_sublist
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.length_zipIdx] at hi hj
  have hi' : i < (cSqfreeYunFF d).length := hi
  have hj' : j < (cSqfreeYunFF d).length := hj
  have h1 : ((cSqfreeYunFF d).zipIdx[i]).1 = (cSqfreeYunFF d)[i] := by simp [List.getElem_zipIdx]
  have h2 : ((cSqfreeYunFF d).zipIdx[i]).2 = i := by simp [List.getElem_zipIdx]
  have h3 : ((cSqfreeYunFF d).zipIdx[j]).1 = (cSqfreeYunFF d)[j] := by simp [List.getElem_zipIdx]
  have h4 : ((cSqfreeYunFF d).zipIdx[j]).2 = j := by simp [List.getElem_zipIdx]
  rw [h1, h2, h3, h4]
  exact ((cSqfreeYunFFG_isRelPrime hgcd d hd0 hpp hi' hj' (Nat.ne_of_lt hij)).pow_left).pow_right

/-- **The product `∏ vk^idx ∣ R`** — the kept factor powers, each dividing `R` (`all_vkidx_dvd_R`) and
pairwise coprime (`powers_pairwise_coprime`), so their product divides `R` (`list_prod_dvd_of_pairwise`).
Modulo the per-factor gcd coprimality. -/
theorem prod_vkidx_dvd_R [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    (((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
        (fun x => toPoly x.1 ^ x.2)).prod
      ∣ (Polynomial.C (1 - ((((cSqfreeYunFF d).zipIdx.filter
            (fun x => ¬ (x.2 + 1 ≤ 1))).length : CFieldSpec.K α))) * toPoly a
          + (((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
              (residNum Dt a d)).sum) := by
  refine list_prod_dvd_of_pairwise _ _ (powers_pairwise_coprime hgcd d hd0 hpp) (fun p hp => ?_)
  rw [List.mem_map] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  exact all_vkidx_dvd_R hgcd Dt a d hd0 hpp hcopgcd x hx

/-- **`resNum = R·gden²`** (as polynomials): the def's residual numerator equals `R` times `gden²`,
from the `R` residual identity + the quotient rule for `D⟦g⟧` + `am` injectivity. Bridges the
valuation `R` (`prod_vkidx_dvd_R`) to the field-identity `resNum`. `hgden`: `gden ≠ 0` (a standard
precondition). -/
theorem resNum_eq_R_mul_gden_sq [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hgd0 : toPoly (cHermiteReduceTower Dt a d).1.2 ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    toPoly (csub (cmul a (cmul (cHermiteReduceTower Dt a d).1.2
          (cHermiteReduceTower Dt a d).1.2))
        (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).1.1)
            (cHermiteReduceTower Dt a d).1.2)
          (cmul (cHermiteReduceTower Dt a d).1.1
            (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).1.2)))))
      = (Polynomial.C (1 - ((((cSqfreeYunFF d).zipIdx.filter
              (fun x => ¬ (x.2 + 1 ≤ 1))).length : CFieldSpec.K α))) * toPoly a
            + (((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
                (residNum Dt a d)).sum)
        * toPoly (cHermiteReduceTower Dt a d).1.2 ^ 2 := by
  set gnum := (cHermiteReduceTower Dt a d).1.1 with hgnum
  set gden := (cHermiteReduceTower Dt a d).1.2 with hgden
  set D := Differential.implicitDeriv (toPoly Dt) with hDdef
  have hRid := R_residual_identity hgcd Dt a d hd0 hpp hcopgcd
  rw [← hgnum, ← hgden] at hRid
  have hinj := RatFunc.algebraMap_injective (CFieldSpec.K α)
  have had : am α (toPoly d) ≠ 0 := am_ne_zero hd0
  have hgd : am α (toPoly gden) ≠ 0 := am_ne_zero hgd0
  have hDg : towerFractionFieldDeriv Dt (am α (toPoly gnum) / am α (toPoly gden))
      = (am α (D (toPoly gnum)) * am α (toPoly gden)
          - am α (toPoly gnum) * am α (D (toPoly gden))) / am α (toPoly gden) ^ 2 := by
    rw [towerFractionFieldDerivG_div, ← map_pow]
  rw [hDg] at hRid
  apply hinj
  simp only [denote, map_sub, map_mul, map_pow, ← hDdef]
  field_simp at hRid
  simp only [map_sub] at hRid
  linear_combination hRid

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **Discharge of the multiplicity-product `hWdvd`** from the Yun reconstruction
`d ~ prodPow 1 (Yun factors)`: since `prodPow 1 L = Dstar · FiltProd` and `d = Dstar · W`, cancelling
`Dstar` gives `W ~ FiltProd`, hence `W ∣ FiltProd`. Reduces `hWdvd` to the single clean fact that Yun
factorization reconstructs its input up to associates. -/
theorem hWdvd_of_reconstruction (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd0 : toPoly d ≠ 0)
    (hrecon : Associated (toPoly d) (prodPow 1 ((cSqfreeYunFF d).map toPoly))) :
    toPoly (CPolyEuclidean.div d (cHermiteReduceTower Dt a d).2.2)
      ∣ (((cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
          (fun x => toPoly x.1 ^ x.2)).prod := by
  have hLprod : toPoly (cHermiteReduceTower Dt a d).2.2
      = ((cSqfreeYunFF d).map toPoly).prod := by
    rw [cHermiteReduceTower, squarefreeYun_dense_wf_eq]
    simp only [denote, toPolyG_cnormG, map_one, mul_zero, add_zero, one_mul]
  have hsplit := toPolyG_yunRadical_split hgcd Dt a d hd0
  have hDstar0 : toPoly (cHermiteReduceTower Dt a d).2.2 ≠ 0 := by
    intro h; exact hd0 (by rw [hsplit, h, zero_mul])
  rw [prodPow_one_cSqfreeYunFFG, ← hLprod, hsplit] at hrecon
  exact (Associated.of_mul_left hrecon (Associated.refl _) hDstar0).dvd

/-- **The pole-cancellation `hWgd` (`W·gden² ∣ resNum`)** — reduced to `W ∣ ∏vk^idx` (the Yun
multiplicity-product, carried as the frontier `hWdvd`): `resNum = R·gden²` and `∏vk^idx ∣ R`, so
`W ∣ ∏vk^idx ∣ R` gives `W·gden² ∣ R·gden² = resNum`. This is the hypothesis of
`hermiteTowerStep_field_identity_of_radical`. -/
theorem hWgd_of_multiplicity [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hgd0 : toPoly (cHermiteReduceTower Dt a d).1.2 ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    toPoly (CPolyEuclidean.div d (cHermiteReduceTower Dt a d).2.2)
        * (toPoly (cHermiteReduceTower Dt a d).1.2 * toPoly (cHermiteReduceTower Dt a d).1.2)
      ∣ toPoly (csub (cmul a (cmul (cHermiteReduceTower Dt a d).1.2
            (cHermiteReduceTower Dt a d).1.2))
          (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).1.1)
              (cHermiteReduceTower Dt a d).1.2)
            (cmul (cHermiteReduceTower Dt a d).1.1
              (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).1.2))))) := by
  have hWdvd := hWdvd_of_reconstruction hgcd Dt a d hd0
    (cSqfreeYunFFG_reconstruction hgcd d hd0 hpp)
  rw [resNum_eq_R_mul_gden_sq hgcd Dt a d hd0 hpp hgd0 hcopgcd, ← pow_two]
  exact mul_dvd_mul_right (hWdvd.trans (prod_vkidx_dvd_R hgcd Dt a d hd0 hpp hcopgcd)) _

/-- **Bridge: the capstone's radical numerator `hNum'` denotes the def field `.2.1`.** Both are exact
division of `toPoly`-equal args, so `CPolyEuclidean.toPoly_div_congr` (with the projection form as `P1/Q1` so the
nonzero/divisibility side-goals stay projection-based and reuse `den_ne_zero`/`hWgd`) closes it. -/
theorem toPolyG_hNum'_eq_2_1 [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    toPoly (CPolyEuclidean.div (cmul (csub (cmul a (cmul (cHermiteReduceTower Dt a d).1.2
            (cHermiteReduceTower Dt a d).1.2))
          (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).1.1)
              (cHermiteReduceTower Dt a d).1.2)
            (cmul (cHermiteReduceTower Dt a d).1.1
              (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).1.2)))))
          (cHermiteReduceTower Dt a d).2.2)
        (cmul d (cmul (cHermiteReduceTower Dt a d).1.2 (cHermiteReduceTower Dt a d).1.2)))
      = toPoly (cHermiteReduceTower Dt a d).2.1 := by
  have hgd0 : toPoly (cHermiteReduceTower Dt a d).1.2 ≠ 0 :=
    toPolyG_cHermiteReduceTowerG_den_ne_zero hgcd Dt a d hd0 hpp
  conv_rhs => rw [cHermiteReduceTower, squarefreeYun_dense_wf_eq]
  simp only [toPolyG_cnormG]
  apply toPoly_div_congr_dense
  · simp only [cHermiteReduceTower, squarefreeYun_dense_wf_eq, denote]
  · simp only [cHermiteReduceTower, squarefreeYun_dense_wf_eq, denote]
  · rw [toPolyG_cmulG, toPolyG_cmulG]
    exact mul_ne_zero hd0 (mul_ne_zero hgd0 hgd0)
  · simp only [toPolyG_cmulG]
    rw [toPolyG_yunRadical_split hgcd Dt a d hd0]
    have h := hWgd_of_multiplicity hgcd Dt a d hd0 hpp hgd0 hcopgcd
    calc toPoly (cHermiteReduceTower Dt a d).2.2 * toPoly (CPolyEuclidean.div d (cHermiteReduceTower Dt a d).2.2)
            * (toPoly (cHermiteReduceTower Dt a d).1.2 * toPoly (cHermiteReduceTower Dt a d).1.2)
          = toPoly (CPolyEuclidean.div d (cHermiteReduceTower Dt a d).2.2)
              * (toPoly (cHermiteReduceTower Dt a d).1.2 * toPoly (cHermiteReduceTower Dt a d).1.2)
            * toPoly (cHermiteReduceTower Dt a d).2.2 := by ring
      _ ∣ _ := mul_dvd_mul_right h _

/-- **The whole-step Hermite field identity for `cHermiteReduceTower`** (`D_tower(⟦g⟧) +
⟦hNum/Dstar⟧ = ⟦a/d⟧`), discharging pole-cancellation via `hWgd_of_multiplicity` (with the Yun
reconstruction now internal) and the radical split `toPolyG_yunRadical_split`. `Dstar ≠ 0` and
`gden ≠ 0` are both discharged internally (from `hd0` via the split and via
`toPolyG_cHermiteReduceTowerG_den_ne_zero`). Modulo **only** the genuine differential-normality side
condition `hcopgcd` (per-factor gcd coprimality — `v` coprime `D(v)`, e.g. false for `v=t` under
hyperexponential `D`), which is correctly a hypothesis (matching Bronstein's `hnorm`). -/
theorem cHermiteReduceTowerG_field_identity [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    towerFractionFieldDeriv Dt
        (am α (toPoly (cHermiteReduceTower Dt a d).1.1)
          / am α (toPoly (cHermiteReduceTower Dt a d).1.2))
      + am α (toPoly (CPolyEuclidean.div (cmul (csub
            (cmul a (cmul (cHermiteReduceTower Dt a d).1.2 (cHermiteReduceTower Dt a d).1.2))
            (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).1.1)
                (cHermiteReduceTower Dt a d).1.2)
              (cmul (cHermiteReduceTower Dt a d).1.1
                (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).1.2)))))
            (cHermiteReduceTower Dt a d).2.2)
          (cmul d (cmul (cHermiteReduceTower Dt a d).1.2
            (cHermiteReduceTower Dt a d).1.2))))
        / am α (toPoly (cHermiteReduceTower Dt a d).2.2)
      = am α (toPoly a) / am α (toPoly d) := by
  have hgd0 : toPoly (cHermiteReduceTower Dt a d).1.2 ≠ 0 :=
    toPolyG_cHermiteReduceTowerG_den_ne_zero hgcd Dt a d hd0 hpp
  have hDstar0 : toPoly (cHermiteReduceTower Dt a d).2.2 ≠ 0 := fun h =>
    hd0 (by rw [toPolyG_yunRadical_split hgcd Dt a d hd0, h, zero_mul])
  have hresDen : cnorm (cmul d (cmul (cHermiteReduceTower Dt a d).1.2
      (cHermiteReduceTower Dt a d).1.2)) ≠ [] := by
    intro h
    have : toPoly (cmul d (cmul (cHermiteReduceTower Dt a d).1.2
        (cHermiteReduceTower Dt a d).1.2)) = 0 := (cisZeroG_iff _).mp (by simp [cisZero, h])
    rw [toPolyG_cmulG, toPolyG_cmulG] at this
    exact (mul_ne_zero hd0 (mul_ne_zero hgd0 hgd0)) this
  exact hermiteTowerStep_field_identity_of_radical Dt (cHermiteReduceTower Dt a d).1.1
    (cHermiteReduceTower Dt a d).1.2 a d (cHermiteReduceTower Dt a d).2.2
    (CPolyEuclidean.div d (cHermiteReduceTower Dt a d).2.2) (am_ne_zero hd0)
    (am_ne_zero hgd0) (am_ne_zero hDstar0) hresDen
    (toPolyG_yunRadical_split hgcd Dt a d hd0)
    (hWgd_of_multiplicity hgcd Dt a d hd0 hpp hgd0 hcopgcd)

end DeepWiki.SymbolicIntegration
