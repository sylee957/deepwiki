import DeepWiki.Algebra.ListSums
import DeepWiki.Algebra.ListProducts
import DeepWiki.SymbolicIntegration.Computable.HermiteTowerStep
import DeepWiki.SymbolicIntegration.Computable.YunTowerCorrect
import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncRegular
import Mathlib.Data.List.Sigma

/-! # `Q`-regularity over the tower fraction field

The valuation notion behind Hermite pole-cancellation, ported from `HermiteCorrectness.IsQRegular`
(over `ℚ`, `d/dx`) to the tower carrier `RatFunc (CFieldSpec.K α)` with the monomial derivation
`towerFractionFieldDerivG Dt`. `IsQRegularG Q f` says `f` has a representation with denominator coprime
to `Q` — i.e. no `Q`-pole. The pure lemmas (`add`, `dvd_num_of_isQRegularG`) copy the abstract proofs;
closure under the derivative (`IsQRegularG.deriv`) uses the tower quotient rule
`towerFractionFieldDerivG_div`. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **Exact division respects `toPolyG`**: `cdivWf P Q` denotes `toPolyG P / toPolyG Q` whenever the
division is exact, so `toPolyG`-equal (and exactly-divisible) numerator/denominator pairs give the same
`cdivWf` denotation — the bridge for matching a radical-form numerator to the `cnormG`'d def field. -/
theorem toPolyG_cdivWf_congr [CFracGcdCoreWf α] (P1 Q1 P2 Q2 : CPolyG α)
    (hP : toPolyG P1 = toPolyG P2) (hQ : toPolyG Q1 = toPolyG Q2)
    (hQ1 : toPolyG Q1 ≠ 0) (hdvd1 : toPolyG Q1 ∣ toPolyG P1) :
    toPolyG (cdivWf P1 Q1) = toPolyG (cdivWf P2 Q2) := by
  have hn1 : cnormG Q1 ≠ [] := fun hnil => hQ1 ((cisZeroG_iff Q1).mp (by simp [cisZeroG, hnil]))
  have hn2 : cnormG Q2 ≠ [] := fun hnil => (hQ ▸ hQ1) ((cisZeroG_iff Q2).mp (by simp [cisZeroG, hnil]))
  have h1 := toPolyG_cdivWf_exact P1 Q1 hn1 hdvd1
  have hdvd2 : toPolyG Q2 ∣ toPolyG P2 := by rw [← hQ, ← hP]; exact hdvd1
  have h2 := toPolyG_cdivWf_exact P2 Q2 hn2 hdvd2
  apply mul_right_cancel₀ hQ1
  rw [h1, hP, ← h2, hQ]

/-- `f` is `Q`-regular over the tower fraction field: it has a representation `amG p / amG q` with
`q ≠ 0` coprime to `Q` (no `Q`-pole). -/
def IsQRegularG (Q : (CFieldSpec.K α)[X]) (f : RatFunc (CFieldSpec.K α)) : Prop :=
  IsRatFuncRegular Q f

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `0` is `Q`-regular (denominator `1`). -/
theorem isQRegularG_zero (Q : (CFieldSpec.K α)[X]) : IsQRegularG Q (0 : RatFunc (CFieldSpec.K α)) :=
  isRatFuncRegular_zero Q

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `Q`-regular is closed under `+` (common denominator `q₁·q₂`, coprime to `Q`). -/
theorem IsQRegularG.add {Q : (CFieldSpec.K α)[X]} {f g : RatFunc (CFieldSpec.K α)}
    (hf : IsQRegularG Q f) (hg : IsQRegularG Q g) : IsQRegularG Q (f + g) :=
  IsRatFuncRegular.add hf hg

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **Order extraction**: if `amG r/amG D` is `Q`-regular, `D ≠ 0`, `Q^e ∣ D`, then `Q^e ∣ r`. -/
theorem dvd_num_of_isQRegularG {Q r D : (CFieldSpec.K α)[X]} {e : ℕ} (hD : D ≠ 0) (hQe : Q ^ e ∣ D)
    (hf : IsQRegularG Q (amG α r / amG α D)) : Q ^ e ∣ r :=
  dvd_num_of_isRatFuncRegular hD hQe hf

/-- **`Q`-regular is closed under the tower derivative** `towerFractionFieldDerivG Dt`: if `f = amG p/amG q`
with `q` coprime to `Q`, then `D_tower f` has denominator `q²`, still coprime to `Q`. Uses the tower
quotient rule. -/
theorem IsQRegularG.deriv {Q : (CFieldSpec.K α)[X]} {f : RatFunc (CFieldSpec.K α)} (Dt : CPolyG α)
    (hf : IsQRegularG Q f) : IsQRegularG Q (towerFractionFieldDerivG Dt f) := by
  obtain ⟨p, q, hq, hQ, hfeq⟩ := hf
  refine ⟨Differential.implicitDeriv (toPolyG Dt) p * q - p * Differential.implicitDeriv (toPolyG Dt) q,
    q ^ 2, pow_ne_zero 2 hq, hQ.pow_right, ?_⟩
  rw [hfeq, towerFractionFieldDerivG_div, map_sub, map_mul, map_mul, map_pow]

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The inner-loop `gloc` denominator is a power of `v`** (times the seed denominator): the
accumulator denominator only ever multiplies by `cpowG v (j+1)`. So a factor's `gloc` denominator is
coprime to any polynomial coprime to `v` — the key to `Vk`-regularity of the other factors. -/
theorem toPolyG_cHermiteReduceTowerInnerWf_den_eq_pow (Dt v u : CPolyG α) :
    ∀ (j : ℕ) (a : CPolyG α) (g : CPolyG α × CPolyG α),
      ∃ N, toPolyG (cHermiteReduceTowerInnerWf Dt v u j a g).1.2
        = toPolyG g.2 * toPolyG v ^ N := by
  intro j
  induction j with
  | zero => intro a g; exact ⟨0, by simp [cHermiteReduceTowerInnerWf]⟩
  | succ j ih =>
    intro a g
    rw [cHermiteReduceTowerInnerWf]
    rcases hBC : cdiophantineGWf (cmulG u (cmonomialDeriv Dt v)) v
      (cscaleG (CField.neg (CField.inv (cnatCastG (j + 1)))) a) with ⟨b, c⟩
    obtain ⟨M, hM⟩ := ih _ (caddG (cmulG g.1 (cpowG v (j + 1))) (cmulG b g.2),
      cmulG g.2 (cpowG v (j + 1)))
    refine ⟨j + 1 + M, ?_⟩
    rw [hM, toPolyG_cmulG, toPolyG_cpowG, mul_assoc, ← pow_add]

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **A factor's `gloc` fraction is `Q`-regular** whenever `Q` is coprime to `v`: the `gloc` denominator
(from the `(0,1)` seed) is `(toPolyG v)^N`, coprime to `Q`. This makes the *other* factors'
contributions `Vk`-regular in the fold. -/
theorem gloc_isQRegularG (Dt v u : CPolyG α) {Q : (CFieldSpec.K α)[X]} (hv : toPolyG v ≠ 0)
    (hcop : IsRelPrime Q (toPolyG v)) (j : ℕ) (a : CPolyG α) :
    IsQRegularG Q
      (amG α (toPolyG (cHermiteReduceTowerInnerWf Dt v u j a
          ([CField.zero], [CField.one])).1.1)
        / amG α (toPolyG (cHermiteReduceTowerInnerWf Dt v u j a
          ([CField.zero], [CField.one])).1.2)) := by
  obtain ⟨N, hN⟩ := toPolyG_cHermiteReduceTowerInnerWf_den_eq_pow Dt v u j a
    ([CField.zero], [CField.one])
  have hden : toPolyG (cHermiteReduceTowerInnerWf Dt v u j a ([CField.zero], [CField.one])).1.2
      = toPolyG v ^ N := by
    rw [hN, show toPolyG ([CField.one] : CPolyG α) = 1 from by
      simp only [denote, mul_zero, add_zero, map_one], one_mul]
  exact ⟨_, _, by rw [hden]; exact pow_ne_zero N hv, by rw [hden]; exact hcop.pow_right, rfl⟩

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `Q`-regular is closed under list sums. -/
theorem isQRegularG_list_sum {Q : (CFieldSpec.K α)[X]} (L : List (RatFunc (CFieldSpec.K α)))
    (h : ∀ f ∈ L, IsQRegularG Q f) : IsQRegularG Q L.sum :=
  isRatFuncRegular_list_sum_self L h

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- Cross-multiplied fraction-pair addition reads as the fraction sum:
`⟦(a₁·b₂ + b₁·a₂) / (a₂·b₂)⟧ = ⟦a₁/a₂⟧ + ⟦b₁/b₂⟧` (denominators nonzero). -/
theorem fracPair_add (a1 a2 b1 b2 : CPolyG α) (ha2 : toPolyG a2 ≠ 0) (hb2 : toPolyG b2 ≠ 0) :
    amG α (toPolyG (caddG (cmulG a1 b2) (cmulG b1 a2))) / amG α (toPolyG (cmulG a2 b2))
      = amG α (toPolyG a1) / amG α (toPolyG a2) + amG α (toPolyG b1) / amG α (toPolyG b2) := by
  simp only [denote, map_add, map_mul]
  rw [div_add_div _ _ (amG_toPolyG_ne_zero ha2) (amG_toPolyG_ne_zero hb2)]
  ring

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The guarded `gloc`-fold reads as a fraction sum.** The `cHermiteReduceTowerGWf` `g`-fold
(`foldl` with `if skip then acc else acc + gloc`) denotes `⟦init⟧ + Σ_{non-skipped} ⟦gloc⟧`, given the
seed and each non-skipped `gloc` have nonzero denominator. -/
theorem fracPair_foldl_sum {β : Type*} (glocOf : β → CPolyG α × CPolyG α) (skip : β → Prop)
    [DecidablePred skip] :
    ∀ (L : List β) (init : CPolyG α × CPolyG α), toPolyG init.2 ≠ 0 →
      (∀ x ∈ L, ¬ skip x → toPolyG (glocOf x).2 ≠ 0) →
      amG α (toPolyG (L.foldl (fun acc x => if skip x then acc
              else (caddG (cmulG acc.1 (glocOf x).2) (cmulG (glocOf x).1 acc.2),
                cmulG acc.2 (glocOf x).2)) init).1)
          / amG α (toPolyG (L.foldl (fun acc x => if skip x then acc
              else (caddG (cmulG acc.1 (glocOf x).2) (cmulG (glocOf x).1 acc.2),
                cmulG acc.2 (glocOf x).2)) init).2)
        = amG α (toPolyG init.1) / amG α (toPolyG init.2)
          + ((L.filter (fun x => ¬ skip x)).map
              (fun x => amG α (toPolyG (glocOf x).1) / amG α (toPolyG (glocOf x).2))).sum := by
  intro L
  induction L with
  | nil => intro init _ _; simp
  | cons x L ih =>
    intro init hinit hden
    rw [List.foldl_cons]
    by_cases hs : skip x
    · rw [if_pos hs, List.filter_cons_of_neg (by simp [hs]),
        ih init hinit (fun y hy => hden y (List.mem_cons_of_mem _ hy))]
    · have hgx : toPolyG (glocOf x).2 ≠ 0 := hden x (List.mem_cons_self ..) hs
      have hnew : toPolyG (cmulG init.2 (glocOf x).2) ≠ 0 := by
        rw [toPolyG_cmulG]; exact mul_ne_zero hinit hgx
      rw [if_neg hs,
        ih _ hnew (fun y hy => hden y (List.mem_cons_of_mem _ hy)),
        List.filter_cons_of_pos (by simp [hs]), List.map_cons, List.sum_cons]
      rw [show (caddG (cmulG init.1 (glocOf x).2) (cmulG (glocOf x).1 init.2),
          cmulG init.2 (glocOf x).2).1 = caddG (cmulG init.1 (glocOf x).2)
            (cmulG (glocOf x).1 init.2) from rfl,
        show (caddG (cmulG init.1 (glocOf x).2) (cmulG (glocOf x).1 init.2),
          cmulG init.2 (glocOf x).2).2 = cmulG init.2 (glocOf x).2 from rfl,
        fracPair_add init.1 init.2 (glocOf x).1 (glocOf x).2 hinit hgx]
      ring

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The guarded Hermite fold keeps a nonzero denominator: from `init.2 ≠ 0` and each non-skipped
`gloc.2 ≠ 0`, the folded `.2` is nonzero (the denominators only ever multiply). -/
theorem foldl_den_ne_zero {β : Type*} (glocOf : β → CPolyG α × CPolyG α) (skip : β → Prop)
    [DecidablePred skip] :
    ∀ (L : List β) (init : CPolyG α × CPolyG α), toPolyG init.2 ≠ 0 →
      (∀ x ∈ L, ¬ skip x → toPolyG (glocOf x).2 ≠ 0) →
      toPolyG (L.foldl (fun acc x => if skip x then acc
              else (caddG (cmulG acc.1 (glocOf x).2) (cmulG (glocOf x).1 acc.2),
                cmulG acc.2 (glocOf x).2)) init).2 ≠ 0 := by
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
/-- The `cHermiteReduceTowerGWf` rational part `⟦g⟧` reads as `Σ_{non-skipped factors} ⟦gloc⟧`, the
guarded fold over `(cSqfreeYunFFGWf d).zipIdx` instantiating `fracPair_foldl_sum`. -/
theorem cHermiteReduceTowerGWf_frac_eq_sum (Dt a d : CPolyG α)
    (hden : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx, ¬ (x.2 + 1 ≤ 1) →
      toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a
        ([CField.zero], [CField.one])).1.2 ≠ 0) :
    amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).1.1)
        / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).1.2)
      = (((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
          (fun x => amG α (toPolyG (cHermiteReduceTowerInnerWf Dt x.1
                (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a ([CField.zero], [CField.one])).1.1)
            / amG α (toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1)))
                (x.2 + 1 - 1) a ([CField.zero], [CField.one])).1.2))).sum := by
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  have hz : toPolyG ([CField.zero] : CPolyG α) = 0 := by
    simp only [denote, mul_zero, add_zero, map_zero]
  rw [cHermiteReduceTowerGWf]
  simp only [toPolyG_cnormG]
  rw [fracPair_foldl_sum
    (fun x => (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a
      ([CField.zero], [CField.one])).1)
    (fun x => x.2 + 1 ≤ 1) (cSqfreeYunFFGWf d).zipIdx ([CField.zero], [CField.one])
    (by rw [hone]; exact one_ne_zero) hden]
  rw [hz, hone, map_zero, map_one, zero_div, zero_add]

/-- The `gloc` fraction of a Hermite-fold factor `x = (v, idx)` (multiplicity `idx+1`). -/
noncomputable def glocFracG (Dt a d : CPolyG α) (x : CPolyG α × ℕ) : RatFunc (CFieldSpec.K α) :=
  amG α (toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a
      ([CField.zero], [CField.one])).1.1)
    / amG α (toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a
      ([CField.zero], [CField.one])).1.2)

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α] in
/-- A fold factor's `gloc` fraction is `Q`-regular for `Q` coprime to its `v`. -/
theorem glocFracG_isQRegularG (Dt a d : CPolyG α) {Q : (CFieldSpec.K α)[X]} (x : CPolyG α × ℕ)
    (hv : toPolyG x.1 ≠ 0) (hcop : IsRelPrime Q (toPolyG x.1)) :
    IsQRegularG Q (glocFracG Dt a d x) :=
  gloc_isQRegularG Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1))) hv hcop (x.2 + 1 - 1) a

/-- **`D(⟦g⟧) − D(⟦gloc_k⟧)` is `Vk`-regular** — the pole-cancellation valuation core. `⟦g⟧ = Σ⟦gloc⟧`,
so its tower derivative splits (`map_list_sum`); permuting `kelem` to the front and cancelling leaves
`Σ_{j≠k} D(⟦gloc_j⟧)`, each `Vk`-regular (`glocFracG_isQRegularG.deriv`, coprimality `hcop`). Tower analog
of `deriv_fold_sub_glocIncr_isQRegular`. -/
theorem deriv_fold_sub_isQRegularG (Dt a d : CPolyG α) (kelem : CPolyG α × ℕ)
    (hkmem : kelem ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)))
    (hnd : ((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).Nodup)
    (hV : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx, toPolyG x.1 ≠ 0)
    (hcop : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)), x ≠ kelem →
      IsRelPrime (toPolyG kelem.1) (toPolyG x.1)) :
    IsQRegularG (toPolyG kelem.1)
      (towerFractionFieldDerivG Dt
          (amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).1.1)
            / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).1.2))
        - towerFractionFieldDerivG Dt (glocFracG Dt a d kelem)) := by
  classical
  set kept := (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)) with hkeptdef
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
  have hden : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx, ¬ (x.2 + 1 ≤ 1) →
      toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a
        ([CField.zero], [CField.one])).1.2 ≠ 0 := by
    intro x hx _
    obtain ⟨N, hN⟩ := toPolyG_cHermiteReduceTowerInnerWf_den_eq_pow Dt x.1
      (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a ([CField.zero], [CField.one])
    rw [hN, hone, one_mul]; exact pow_ne_zero N (hV x hx)
  -- `⟦g⟧ = Σ_{kept} glocFracG`, so `D⟦g⟧ = Σ D(glocFracG)`.
  rw [cHermiteReduceTowerGWf_frac_eq_sum Dt a d hden,
    map_list_sum (towerFractionFieldDerivG Dt), List.map_map, ← hkeptdef,
    (List.perm_cons_erase hkmem).map _ |>.sum_eq, List.map_cons, List.sum_cons,
    show (⇑(towerFractionFieldDerivG Dt) ∘ fun x =>
        amG α (toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1)))
            (x.2 + 1 - 1) a ([CField.zero], [CField.one])).1.1)
          / amG α (toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1)))
            (x.2 + 1 - 1) a ([CField.zero], [CField.one])).1.2)) kelem
      = towerFractionFieldDerivG Dt (glocFracG Dt a d kelem) from rfl,
    add_sub_cancel_left]
  refine isQRegularG_list_sum _ (fun f hf => ?_)
  rw [List.mem_map] at hf
  obtain ⟨x, hx, rfl⟩ := hf
  rw [hnd.mem_erase_iff] at hx
  have hxmem : x ∈ (cSqfreeYunFFGWf d).zipIdx := List.mem_of_mem_filter (hkeptdef ▸ hx.2)
  exact (glocFracG_isQRegularG Dt a d x (hV x hxmem)
    (hcop x (hkeptdef ▸ hx.2) hx.1)).deriv Dt

/-- **The total fold residual** (per-factor identities `hstep` given): `⟦a/d⟧ − D⟦g⟧ = ⟦R/d⟧` with
`R = C(1−m)·a + Σ residNumG`, `m` the number of kept factors. Sums `D⟦g⟧ = Σ D⟦gloc⟧` using each
factor's `hstep : D⟦gloc x⟧ = ⟦a/d⟧ − ⟦residNumG x /d⟧`. Tower analog of `total_fold_residual_over_D`. -/
theorem total_fold_residual_tower (Dt a d : CPolyG α)
    (residNumG : CPolyG α × ℕ → (CFieldSpec.K α)[X]) (hd : toPolyG d ≠ 0)
    (hden : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx, ¬ (x.2 + 1 ≤ 1) →
      toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a
        ([CField.zero], [CField.one])).1.2 ≠ 0)
    (hstep : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      towerFractionFieldDerivG Dt (glocFracG Dt a d x)
        = amG α (toPolyG a) / amG α (toPolyG d) - amG α (residNumG x) / amG α (toPolyG d)) :
    amG α (toPolyG a) / amG α (toPolyG d)
        - towerFractionFieldDerivG Dt
            (amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).1.1)
              / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).1.2))
      = amG α (Polynomial.C (1 - ((((cSqfreeYunFFGWf d).zipIdx.filter
              (fun x => ¬ (x.2 + 1 ≤ 1))).length : CFieldSpec.K α))) * toPolyG a
            + (((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map residNumG).sum)
        / amG α (toPolyG d) := by
  set kept := (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)) with hkeptdef
  have had : amG α (toPolyG d) ≠ 0 := amG_toPolyG_ne_zero hd
  rw [cHermiteReduceTowerGWf_frac_eq_sum Dt a d hden, map_list_sum (towerFractionFieldDerivG Dt),
    List.map_map, ← hkeptdef]
  -- rewrite each `D⟦gloc⟧` via `hstep`, so the summed function is `a/d − residNum/d`.
  have heq : (kept.map (⇑(towerFractionFieldDerivG Dt) ∘ fun x =>
        amG α (toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1)))
            (x.2 + 1 - 1) a ([CField.zero], [CField.one])).1.1)
          / amG α (toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1)))
            (x.2 + 1 - 1) a ([CField.zero], [CField.one])).1.2)))
      = kept.map (fun x => amG α (toPolyG a) / amG α (toPolyG d)
          - amG α (residNumG x) / amG α (toPolyG d)) := by
    apply List.map_congr_left; intro x hx; exact hstep x hx
  rw [heq, list_sum_map_const_sub]
  -- `Σ (residNum x /d) = amG (Σ residNum) / d`.
  have hsumdiv : (kept.map (fun x => amG α (residNumG x) / amG α (toPolyG d))).sum
      = amG α (kept.map residNumG).sum / amG α (toPolyG d) := by
    rw [list_sum_map_div, map_list_sum (amG α), List.map_map]; rfl
  have hCcast : amG α (Polynomial.C (1 - (kept.length : CFieldSpec.K α)))
      = 1 - (kept.length : RatFunc (CFieldSpec.K α)) := by
    rw [amG, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, map_sub, map_one,
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
    {af Dg Dgk : RatFunc (CFieldSpec.K α)} (e : ℕ) (D : CPolyG α) (hD : toPolyG D ≠ 0)
    (hR : af - Dg = amG α R / amG α (toPolyG D))
    (hstepk : Dgk = af - amG α residNum_k / amG α (toPolyG D))
    (hderiv : IsQRegularG vk (Dg - Dgk))
    (hpow : vk ^ (e + 1) ∣ toPolyG D) (hresk : vk ^ e ∣ residNum_k) :
    vk ^ e ∣ R := by
  have hDg : Dg = af - amG α R / amG α (toPolyG D) := by linear_combination -hR
  have heq : Dg - Dgk = amG α (residNum_k - R) / amG α (toPolyG D) := by
    rw [hDg, hstepk, map_sub, sub_div]; ring
  rw [heq] at hderiv
  have hdvd : vk ^ (e + 1) ∣ residNum_k - R := dvd_num_of_isQRegularG hD hpow hderiv
  have h1 : vk ^ e ∣ residNum_k - R := (pow_dvd_pow vk (Nat.le_succ e)).trans hdvd
  have h2 : vk ^ e ∣ residNum_k - (residNum_k - R) := dvd_sub hresk h1
  simpa using h2

omit [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α] in
/-- **Discharge of M2's Bézout hypothesis** from the gcd coprimality of `(u·Dv, v)`: for every step
`(j', A')`, `cdiophantineGWf`'s cofactors satisfy `b·(u·Dv) + c·v = −A'·C((j'+1)⁻¹)`. Uses
`toPolyG_cdiophantineGWf`; the coprimality `gcd(u·Dv, v)` degree-0/nonzero is the input (from `v`
squarefree + coprime to `u`). -/
theorem cHermiteInner_hbez_of_gcd (Dt v u : CPolyG α)
    (hqn : cnormG v ≠ [])
    (hgdeg : (toPolyG (cgcdWf (cmulG u (cmonomialDeriv Dt v)) v).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (cmulG u (cmonomialDeriv Dt v)) v).1 ≠ 0) :
    ∀ (j' : ℕ) (A' : CPolyG α),
      toPolyG (cdiophantineGWf (cmulG u (cmonomialDeriv Dt v)) v
            (cscaleG (CField.neg (CField.inv (cnatCastG (j' + 1)))) A')).1
          * (toPolyG u * Differential.implicitDeriv (toPolyG Dt) (toPolyG v))
        + toPolyG (cdiophantineGWf (cmulG u (cmonomialDeriv Dt v)) v
            (cscaleG (CField.neg (CField.inv (cnatCastG (j' + 1)))) A')).2 * toPolyG v
      = -toPolyG A' * Polynomial.C (((j' : CFieldSpec.K α) + 1)⁻¹) := by
  intro j' A'
  have h := toPolyG_cdiophantineGWf (cmulG u (cmonomialDeriv Dt v)) v
    (cscaleG (CField.neg (CField.inv (cnatCastG (j' + 1)))) A') hqn hgdeg hgne
  rw [toPolyG_cmulG, toPolyG_cmonomialDeriv] at h
  rw [h, toPolyG_cscaleG, CFieldSpec.toK_neg, CFieldSpec.toK_inv, CPolyG.toK_cnatCastG,
    Nat.cast_add_one, Polynomial.C_neg]
  ring

omit [CFracGcdCoreWf α] in
/-- **The per-factor `hstep` identity** (`D⟦gloc x⟧ = ⟦a/d⟧ − ⟦residNum/d⟧`), from M2 and the isolated
inputs: `d ≠ 0`, the gcd coprimality of `(u·Dv, v)` (`hgdeg`/`hgne`), and `u·v^i = d` (`hud`, from
`v^i ∣ d`). Here `residNum = afin · v^(i−1)` (`afin` the inner-loop residual). -/
theorem glocFracG_step_identity [CharZero (CFieldSpec.K α)] (Dt a d : CPolyG α) (x : CPolyG α × ℕ)
    (hd : toPolyG d ≠ 0) (hv : toPolyG x.1 ≠ 0)
    (hgdeg : (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
        (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
        (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hud : toPolyG (cdivWf d (cpowG x.1 (x.2 + 1))) * toPolyG x.1 ^ (x.2 + 1) = toPolyG d) :
    towerFractionFieldDerivG Dt (glocFracG Dt a d x)
      = amG α (toPolyG a) / amG α (toPolyG d)
        - amG α (toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1)))
              (x.2 + 1 - 1) a ([CField.zero], [CField.one])).2 * toPolyG x.1 ^ x.2)
          / amG α (toPolyG d) := by
  set u := cdivWf d (cpowG x.1 (x.2 + 1)) with hudef
  have hu : toPolyG u ≠ 0 := fun h0 => hd (by rw [← hud, h0, zero_mul])
  have hqn : cnormG x.1 ≠ [] := fun h => hv ((cisZeroG_iff x.1).mp (by simp [cisZeroG, h]))
  have hone : toPolyG ([CField.one] : CPolyG α) ≠ 0 := by
    rw [show toPolyG ([CField.one] : CPolyG α) = 1 from by
      simp only [denote, mul_zero, add_zero, map_one]]
    exact one_ne_zero
  have hbez := cHermiteInner_hbez_of_gcd Dt x.1 u hqn hgdeg hgne
  have hM2 := cHermiteReduceTowerInnerWf_spec_acc Dt x.1 u hu hv hbez x.2 a
    ([CField.zero], [CField.one]) hone
  -- the seed fraction ⟦0/1⟧ = 0.
  have hz : amG α (toPolyG ([CField.zero] : CPolyG α)) = 0 := by
    simp only [denote, mul_zero, add_zero, map_zero]
  have ho : amG α (toPolyG ([CField.one] : CPolyG α)) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  rw [hz, ho, zero_div, map_zero, add_zero] at hM2
  -- `amG u · amG v^(i) = amG d`.
  have hamud : amG α (toPolyG u) * amG α (toPolyG x.1) ^ (x.2 + 1) = amG α (toPolyG d) := by
    rw [← map_pow, ← map_mul, hud]
  have had : amG α (toPolyG d) ≠ 0 := amG_toPolyG_ne_zero hd
  have hav : amG α (toPolyG x.1) ≠ 0 := amG_toPolyG_ne_zero hv
  have hau : amG α (toPolyG u) ≠ 0 := amG_toPolyG_ne_zero hu
  -- rearrange M2 to `D⟦gloc⟧ = amG a/(amG u·amG v^i) − amG afin/(amG u·amG v)`.
  rw [show towerFractionFieldDerivG Dt (glocFracG Dt a d x)
      = amG α (toPolyG a) / (amG α (toPolyG u) * amG α (toPolyG x.1) ^ (x.2 + 1))
        - amG α (toPolyG (cHermiteReduceTowerInnerWf Dt x.1 u x.2 a
            ([CField.zero], [CField.one])).2) / (amG α (toPolyG u) * amG α (toPolyG x.1)) from by
      rw [glocFracG]; simp only [Nat.add_sub_cancel]; linear_combination -hM2]
  rw [Nat.add_sub_cancel, map_mul, map_pow, ← hamud]
  have hvp : amG α (toPolyG x.1) ^ (x.2 + 1) ≠ 0 := pow_ne_zero _ hav
  field_simp
  ring

/-- The per-factor residual numerator `residNumG x = afin · v^(i−1)` (`afin` the inner-loop residual). -/
noncomputable def residNumG (Dt a d : CPolyG α) (x : CPolyG α × ℕ) : (CFieldSpec.K α)[X] :=
  toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a
    ([CField.zero], [CField.one])).2 * toPolyG x.1 ^ x.2

/-- **All per-factor `hstep` identities** hold, given the per-factor gcd coprimality (`hcopgcd`, the
standard Hermite precondition — the single remaining frontier). Discharges `hv`/`hpow`/`hud` from the
Yun structural facts (`get_ne_zero`, `pow_dvd`, `cdivWf_pow_mul`) via the zipIdx→get bridge. -/
theorem all_hstep [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      towerFractionFieldDerivG Dt (glocFracG Dt a d x)
        = amG α (toPolyG a) / amG α (toPolyG d)
          - amG α (residNumG Dt a d x) / amG α (toPolyG d) := by
  intro x hx
  have hxzip : x ∈ (cSqfreeYunFFGWf d).zipIdx := List.mem_of_mem_filter hx
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hxzip))
  have hv : toPolyG x.1 ≠ 0 := by
    rw [← hget]; exact cSqfreeYunFFGWf_get_ne_zero hgcd d hd0 hpp x.2 hidx
  have hpow : toPolyG x.1 ^ (x.2 + 1) ∣ toPolyG d := by
    rw [← hget, add_comm]; exact cSqfreeYunFFGWf_pow_dvd hgcd d hd0 hpp x.2 hidx
  have hud := toPolyG_cdivWf_pow_mul d x.1 (x.2 + 1) hv hpow
  exact glocFracG_step_identity Dt a d x hd0 hv (hcopgcd x hx).1 (hcopgcd x hx).2 hud

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The gloc denominators are nonzero (`= v^N`, `v` a nonzero Yun factor) — the `hden` input of both
`cHermiteReduceTowerGWf_frac_eq_sum` and `total_fold_residual_tower`. -/
theorem hden_of [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0) :
    ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx, ¬ (x.2 + 1 ≤ 1) →
      toPolyG (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a
        ([CField.zero], [CField.one])).1.2 ≠ 0 := by
  intro x hx _
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx))
  have hv : toPolyG x.1 ≠ 0 := by
    rw [← hget]; exact cSqfreeYunFFGWf_get_ne_zero hgcd d hd0 hpp x.2 hidx
  obtain ⟨N, hN⟩ := toPolyG_cHermiteReduceTowerInnerWf_den_eq_pow Dt x.1
    (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a ([CField.zero], [CField.one])
  rw [hN, show toPolyG ([CField.one] : CPolyG α) = 1 from by
    simp only [denote, mul_zero, add_zero, map_one], one_mul]
  exact pow_ne_zero N hv

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The Hermite fold denominator `gden` is nonzero** (`toPolyG (cHermiteReduceTowerGWf …).1.2 ≠ 0`):
the guarded fold starts at `1` and only multiplies nonzero `gloc` denominators (`hden_of`), so
`foldl_den_ne_zero` gives the result. Discharges `hgd0`. -/
theorem toPolyG_cHermiteReduceTowerGWf_den_ne_zero [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hpp : (toPolyG d).primPart ≠ 0) :
    toPolyG (cHermiteReduceTowerGWf Dt a d).1.2 ≠ 0 := by
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  rw [cHermiteReduceTowerGWf]
  simp only [toPolyG_cnormG]
  exact foldl_den_ne_zero
    (fun x => (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a
      ([CField.zero], [CField.one])).1)
    (fun x => x.2 + 1 ≤ 1) (cSqfreeYunFFGWf d).zipIdx ([CField.zero], [CField.one])
    (by rw [hone]; exact one_ne_zero) (hden_of hgcd Dt a d hd0 hpp)

/-- **The `R` residual identity** `⟦a/d⟧ − D⟦g⟧ = ⟦R/d⟧` (`R = C(1−m)·a + Σ residNumG`), from
`total_fold_residual_tower` fed by `all_hstep` and `hden_of`. Modulo the per-factor gcd coprimality. -/
theorem R_residual_identity [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    amG α (toPolyG a) / amG α (toPolyG d)
        - towerFractionFieldDerivG Dt
            (amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).1.1)
              / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).1.2))
      = amG α (Polynomial.C (1 - ((((cSqfreeYunFFGWf d).zipIdx.filter
              (fun x => ¬ (x.2 + 1 ≤ 1))).length : CFieldSpec.K α))) * toPolyG a
            + (((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
                (residNumG Dt a d)).sum)
        / amG α (toPolyG d) :=
  total_fold_residual_tower Dt a d (residNumG Dt a d) hd0 (hden_of hgcd Dt a d hd0 hpp)
    (all_hstep hgcd Dt a d hd0 hpp hcopgcd)

/-- **Each `vk^idx` divides `R`** (the per-factor order bounds), by `dvd_R_of_factor` fed by the `R`
residual identity, `all_hstep`, `deriv_fold_sub`, `hpow`, and `hresk = dvd_mul_left`. The `hV`/`hnd`/`hcop`
inputs to `deriv_fold_sub` are the Yun structural facts. Modulo the per-factor gcd coprimality. -/
theorem all_vkidx_dvd_R [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      toPolyG x.1 ^ x.2 ∣ (Polynomial.C (1 - ((((cSqfreeYunFFGWf d).zipIdx.filter
              (fun x => ¬ (x.2 + 1 ≤ 1))).length : CFieldSpec.K α))) * toPolyG a
            + (((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
                (residNumG Dt a d)).sum) := by
  have hV : ∀ y ∈ (cSqfreeYunFFGWf d).zipIdx, toPolyG y.1 ≠ 0 := by
    intro y hy
    obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
      (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hy))
    rw [← hget]; exact cSqfreeYunFFGWf_get_ne_zero hgcd d hd0 hpp y.2 hidx
  have hnd : ((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).Nodup :=
    (List.Nodup.of_map Prod.snd (List.nodup_zipIdx_map_snd _)).filter _
  have hRid := R_residual_identity hgcd Dt a d hd0 hpp hcopgcd
  intro x hx
  obtain ⟨hxidx, hxget⟩ := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using (List.mem_of_mem_filter hx)))
  have hcop : ∀ y ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)), y ≠ x →
      IsRelPrime (toPolyG x.1) (toPolyG y.1) := by
    intro y hy hyx
    obtain ⟨hyidx, hyget⟩ := List.getElem?_eq_some_iff.mp
      (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using (List.mem_of_mem_filter hy)))
    have hne2 : x.2 ≠ y.2 := by
      intro h; apply hyx
      refine Prod.ext ?_ h.symm
      rw [← hyget, ← hxget]; exact getElem_congr rfl h.symm hyidx
    rw [← hxget, ← hyget]
    exact cSqfreeYunFFGWf_isRelPrime hgcd d hd0 hpp hxidx hyidx hne2
  have hderiv := deriv_fold_sub_isQRegularG Dt a d x hx hnd hV hcop
  have hstepk := all_hstep hgcd Dt a d hd0 hpp hcopgcd x hx
  have hpow : toPolyG x.1 ^ (x.2 + 1) ∣ toPolyG d := by
    rw [← hxget, add_comm]; exact cSqfreeYunFFGWf_pow_dvd hgcd d hd0 hpp x.2 hxidx
  have hresk : toPolyG x.1 ^ x.2 ∣ residNumG Dt a d x := by rw [residNumG]; exact dvd_mul_left _ _
  exact dvd_R_of_factor x.2 d hd0 hRid hstepk hderiv hpow hresk

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The kept factor powers `vk^idx` are pairwise relatively prime (distinct Yun factors coprime,
`IsRelPrime.pow`). -/
theorem powers_pairwise_coprime [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (d : CPolyG α) (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0) :
    List.Pairwise IsRelPrime
      (((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
        (fun x => toPolyG x.1 ^ x.2)) := by
  rw [List.pairwise_map]
  apply List.Pairwise.sublist List.filter_sublist
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.length_zipIdx] at hi hj
  have hi' : i < (cSqfreeYunFFGWf d).length := hi
  have hj' : j < (cSqfreeYunFFGWf d).length := hj
  have h1 : ((cSqfreeYunFFGWf d).zipIdx[i]).1 = (cSqfreeYunFFGWf d)[i] := by simp [List.getElem_zipIdx]
  have h2 : ((cSqfreeYunFFGWf d).zipIdx[i]).2 = i := by simp [List.getElem_zipIdx]
  have h3 : ((cSqfreeYunFFGWf d).zipIdx[j]).1 = (cSqfreeYunFFGWf d)[j] := by simp [List.getElem_zipIdx]
  have h4 : ((cSqfreeYunFFGWf d).zipIdx[j]).2 = j := by simp [List.getElem_zipIdx]
  rw [h1, h2, h3, h4]
  exact ((cSqfreeYunFFGWf_isRelPrime hgcd d hd0 hpp hi' hj' (Nat.ne_of_lt hij)).pow_left).pow_right

/-- **The product `∏ vk^idx ∣ R`** — the kept factor powers, each dividing `R` (`all_vkidx_dvd_R`) and
pairwise coprime (`powers_pairwise_coprime`), so their product divides `R` (`list_prod_dvd_of_pairwise`).
Modulo the per-factor gcd coprimality. -/
theorem prod_vkidx_dvd_R [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    (((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
        (fun x => toPolyG x.1 ^ x.2)).prod
      ∣ (Polynomial.C (1 - ((((cSqfreeYunFFGWf d).zipIdx.filter
            (fun x => ¬ (x.2 + 1 ≤ 1))).length : CFieldSpec.K α))) * toPolyG a
          + (((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
              (residNumG Dt a d)).sum) := by
  refine list_prod_dvd_of_pairwise _ _ (powers_pairwise_coprime hgcd d hd0 hpp) (fun p hp => ?_)
  rw [List.mem_map] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  exact all_vkidx_dvd_R hgcd Dt a d hd0 hpp hcopgcd x hx

/-- **`resNum = R·gden²`** (as polynomials): the def's residual numerator equals `R` times `gden²`,
from the `R` residual identity + the quotient rule for `D⟦g⟧` + `amG` injectivity. Bridges the
valuation `R` (`prod_vkidx_dvd_R`) to the field-identity `resNum`. `hgden`: `gden ≠ 0` (a standard
precondition). -/
theorem resNum_eq_R_mul_gden_sq [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hgd0 : toPolyG (cHermiteReduceTowerGWf Dt a d).1.2 ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    toPolyG (csubG (cmulG a (cmulG (cHermiteReduceTowerGWf Dt a d).1.2
          (cHermiteReduceTowerGWf Dt a d).1.2))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt (cHermiteReduceTowerGWf Dt a d).1.1)
            (cHermiteReduceTowerGWf Dt a d).1.2)
          (cmulG (cHermiteReduceTowerGWf Dt a d).1.1
            (cmonomialDeriv Dt (cHermiteReduceTowerGWf Dt a d).1.2)))))
      = (Polynomial.C (1 - ((((cSqfreeYunFFGWf d).zipIdx.filter
              (fun x => ¬ (x.2 + 1 ≤ 1))).length : CFieldSpec.K α))) * toPolyG a
            + (((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
                (residNumG Dt a d)).sum)
        * toPolyG (cHermiteReduceTowerGWf Dt a d).1.2 ^ 2 := by
  set gnum := (cHermiteReduceTowerGWf Dt a d).1.1 with hgnum
  set gden := (cHermiteReduceTowerGWf Dt a d).1.2 with hgden
  set D := Differential.implicitDeriv (toPolyG Dt) with hDdef
  have hRid := R_residual_identity hgcd Dt a d hd0 hpp hcopgcd
  rw [← hgnum, ← hgden] at hRid
  have hinj := RatFunc.algebraMap_injective (CFieldSpec.K α)
  have had : amG α (toPolyG d) ≠ 0 := amG_toPolyG_ne_zero hd0
  have hgd : amG α (toPolyG gden) ≠ 0 := amG_toPolyG_ne_zero hgd0
  have hDg : towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
      = (amG α (D (toPolyG gnum)) * amG α (toPolyG gden)
          - amG α (toPolyG gnum) * amG α (D (toPolyG gden))) / amG α (toPolyG gden) ^ 2 := by
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
theorem hWdvd_of_reconstruction (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α)
    (hd0 : toPolyG d ≠ 0)
    (hrecon : Associated (toPolyG d) (prodPow 1 ((cSqfreeYunFFGWf d).map toPolyG))) :
    toPolyG (cdivWf d (cHermiteReduceTowerGWf Dt a d).2.2)
      ∣ (((cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1))).map
          (fun x => toPolyG x.1 ^ x.2)).prod := by
  have hLprod : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2
      = ((cSqfreeYunFFGWf d).map toPolyG).prod := by
    rw [cHermiteReduceTowerGWf]
    simp only [toPolyG_cnormG, toPolyG_foldl_cmulG_plainList, toPolyG_one_singleton, one_mul]
  have hsplit := toPolyG_yunRadical_split hgcd Dt a d hd0
  have hDstar0 : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 ≠ 0 := by
    intro h; exact hd0 (by rw [hsplit, h, zero_mul])
  rw [prodPow_one_cSqfreeYunFFGWf, ← hLprod, hsplit] at hrecon
  exact (Associated.of_mul_left hrecon (Associated.refl _) hDstar0).dvd

/-- **The pole-cancellation `hWgd` (`W·gden² ∣ resNum`)** — reduced to `W ∣ ∏vk^idx` (the Yun
multiplicity-product, carried as the frontier `hWdvd`): `resNum = R·gden²` and `∏vk^idx ∣ R`, so
`W ∣ ∏vk^idx ∣ R` gives `W·gden² ∣ R·gden² = resNum`. This is the hypothesis of
`hermiteTowerStep_field_identity_of_radical`. -/
theorem hWgd_of_multiplicity [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hgd0 : toPolyG (cHermiteReduceTowerGWf Dt a d).1.2 ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    toPolyG (cdivWf d (cHermiteReduceTowerGWf Dt a d).2.2)
        * (toPolyG (cHermiteReduceTowerGWf Dt a d).1.2 * toPolyG (cHermiteReduceTowerGWf Dt a d).1.2)
      ∣ toPolyG (csubG (cmulG a (cmulG (cHermiteReduceTowerGWf Dt a d).1.2
            (cHermiteReduceTowerGWf Dt a d).1.2))
          (cmulG d (csubG (cmulG (cmonomialDeriv Dt (cHermiteReduceTowerGWf Dt a d).1.1)
              (cHermiteReduceTowerGWf Dt a d).1.2)
            (cmulG (cHermiteReduceTowerGWf Dt a d).1.1
              (cmonomialDeriv Dt (cHermiteReduceTowerGWf Dt a d).1.2))))) := by
  have hWdvd := hWdvd_of_reconstruction hgcd Dt a d hd0
    (cSqfreeYunFFGWf_reconstruction hgcd d hd0 hpp)
  rw [resNum_eq_R_mul_gden_sq hgcd Dt a d hd0 hpp hgd0 hcopgcd, ← pow_two]
  exact mul_dvd_mul_right (hWdvd.trans (prod_vkidx_dvd_R hgcd Dt a d hd0 hpp hcopgcd)) _

/-- **Bridge: the capstone's radical numerator `hNum'` denotes the def field `.2.1`.** Both are exact
division of `toPolyG`-equal args, so `toPolyG_cdivWf_congr` (with the projection form as `P1/Q1` so the
nonzero/divisibility side-goals stay projection-based and reuse `den_ne_zero`/`hWgd`) closes it. -/
theorem toPolyG_hNum'_eq_2_1 [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    toPolyG (cdivWf (cmulG (csubG (cmulG a (cmulG (cHermiteReduceTowerGWf Dt a d).1.2
            (cHermiteReduceTowerGWf Dt a d).1.2))
          (cmulG d (csubG (cmulG (cmonomialDeriv Dt (cHermiteReduceTowerGWf Dt a d).1.1)
              (cHermiteReduceTowerGWf Dt a d).1.2)
            (cmulG (cHermiteReduceTowerGWf Dt a d).1.1
              (cmonomialDeriv Dt (cHermiteReduceTowerGWf Dt a d).1.2)))))
          (cHermiteReduceTowerGWf Dt a d).2.2)
        (cmulG d (cmulG (cHermiteReduceTowerGWf Dt a d).1.2 (cHermiteReduceTowerGWf Dt a d).1.2)))
      = toPolyG (cHermiteReduceTowerGWf Dt a d).2.1 := by
  have hgd0 : toPolyG (cHermiteReduceTowerGWf Dt a d).1.2 ≠ 0 :=
    toPolyG_cHermiteReduceTowerGWf_den_ne_zero hgcd Dt a d hd0 hpp
  conv_rhs => rw [cHermiteReduceTowerGWf]
  simp only [toPolyG_cnormG]
  apply toPolyG_cdivWf_congr
  · simp only [cHermiteReduceTowerGWf, denote]
  · simp only [cHermiteReduceTowerGWf, denote]
  · rw [toPolyG_cmulG, toPolyG_cmulG]
    exact mul_ne_zero hd0 (mul_ne_zero hgd0 hgd0)
  · simp only [toPolyG_cmulG]
    rw [toPolyG_yunRadical_split hgcd Dt a d hd0]
    have h := hWgd_of_multiplicity hgcd Dt a d hd0 hpp hgd0 hcopgcd
    calc toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 * toPolyG (cdivWf d (cHermiteReduceTowerGWf Dt a d).2.2)
            * (toPolyG (cHermiteReduceTowerGWf Dt a d).1.2 * toPolyG (cHermiteReduceTowerGWf Dt a d).1.2)
          = toPolyG (cdivWf d (cHermiteReduceTowerGWf Dt a d).2.2)
              * (toPolyG (cHermiteReduceTowerGWf Dt a d).1.2 * toPolyG (cHermiteReduceTowerGWf Dt a d).1.2)
            * toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 := by ring
      _ ∣ _ := mul_dvd_mul_right h _

/-- **The whole-step Hermite field identity for `cHermiteReduceTowerGWf`** (`D_tower(⟦g⟧) +
⟦hNum/Dstar⟧ = ⟦a/d⟧`), discharging pole-cancellation via `hWgd_of_multiplicity` (with the Yun
reconstruction now internal) and the radical split `toPolyG_yunRadical_split`. `Dstar ≠ 0` and
`gden ≠ 0` are both discharged internally (from `hd0` via the split and via
`toPolyG_cHermiteReduceTowerGWf_den_ne_zero`). Modulo **only** the genuine differential-normality side
condition `hcopgcd` (per-factor gcd coprimality — `v` coprime `D(v)`, e.g. false for `v=t` under
hyperexponential `D`), which is correctly a hypothesis (matching Bronstein's `hnorm`). -/
theorem cHermiteReduceTowerGWf_field_identity [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).1.1)
          / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).1.2))
      + amG α (toPolyG (cdivWf (cmulG (csubG
            (cmulG a (cmulG (cHermiteReduceTowerGWf Dt a d).1.2 (cHermiteReduceTowerGWf Dt a d).1.2))
            (cmulG d (csubG (cmulG (cmonomialDeriv Dt (cHermiteReduceTowerGWf Dt a d).1.1)
                (cHermiteReduceTowerGWf Dt a d).1.2)
              (cmulG (cHermiteReduceTowerGWf Dt a d).1.1
                (cmonomialDeriv Dt (cHermiteReduceTowerGWf Dt a d).1.2)))))
            (cHermiteReduceTowerGWf Dt a d).2.2)
          (cmulG d (cmulG (cHermiteReduceTowerGWf Dt a d).1.2
            (cHermiteReduceTowerGWf Dt a d).1.2))))
        / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  have hgd0 : toPolyG (cHermiteReduceTowerGWf Dt a d).1.2 ≠ 0 :=
    toPolyG_cHermiteReduceTowerGWf_den_ne_zero hgcd Dt a d hd0 hpp
  have hDstar0 : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 ≠ 0 := fun h =>
    hd0 (by rw [toPolyG_yunRadical_split hgcd Dt a d hd0, h, zero_mul])
  have hresDen : cnormG (cmulG d (cmulG (cHermiteReduceTowerGWf Dt a d).1.2
      (cHermiteReduceTowerGWf Dt a d).1.2)) ≠ [] := by
    intro h
    have : toPolyG (cmulG d (cmulG (cHermiteReduceTowerGWf Dt a d).1.2
        (cHermiteReduceTowerGWf Dt a d).1.2)) = 0 := (cisZeroG_iff _).mp (by simp [cisZeroG, h])
    rw [toPolyG_cmulG, toPolyG_cmulG] at this
    exact (mul_ne_zero hd0 (mul_ne_zero hgd0 hgd0)) this
  exact hermiteTowerStep_field_identity_of_radical Dt (cHermiteReduceTowerGWf Dt a d).1.1
    (cHermiteReduceTowerGWf Dt a d).1.2 a d (cHermiteReduceTowerGWf Dt a d).2.2
    (cdivWf d (cHermiteReduceTowerGWf Dt a d).2.2) (amG_toPolyG_ne_zero hd0)
    (amG_toPolyG_ne_zero hgd0) (amG_toPolyG_ne_zero hDstar0) hresDen
    (toPolyG_yunRadical_split hgcd Dt a d hd0)
    (hWgd_of_multiplicity hgcd Dt a d hd0 hpp hgd0 hcopgcd)

end DeepWiki.SymbolicIntegration
