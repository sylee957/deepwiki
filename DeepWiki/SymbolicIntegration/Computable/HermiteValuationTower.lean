import DeepWiki.SymbolicIntegration.Computable.HermiteTowerStep

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

/-- `f` is `Q`-regular over the tower fraction field: it has a representation `amG p / amG q` with
`q ≠ 0` coprime to `Q` (no `Q`-pole). -/
def IsQRegularG (Q : (CFieldSpec.K α)[X]) (f : RatFunc (CFieldSpec.K α)) : Prop :=
  ∃ p q : (CFieldSpec.K α)[X], q ≠ 0 ∧ IsRelPrime Q q ∧ f = amG α p / amG α q

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `0` is `Q`-regular (denominator `1`). -/
theorem isQRegularG_zero (Q : (CFieldSpec.K α)[X]) : IsQRegularG Q (0 : RatFunc (CFieldSpec.K α)) :=
  ⟨0, 1, one_ne_zero, isRelPrime_one_right, by simp⟩

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `Q`-regular is closed under `+` (common denominator `q₁·q₂`, coprime to `Q`). -/
theorem IsQRegularG.add {Q : (CFieldSpec.K α)[X]} {f g : RatFunc (CFieldSpec.K α)}
    (hf : IsQRegularG Q f) (hg : IsQRegularG Q g) : IsQRegularG Q (f + g) := by
  obtain ⟨p1, q1, hq1, hQ1, hf⟩ := hf
  obtain ⟨p2, q2, hq2, hQ2, hg⟩ := hg
  refine ⟨p1 * q2 + q1 * p2, q1 * q2, mul_ne_zero hq1 hq2, hQ1.mul_right hQ2, ?_⟩
  have hinj := RatFunc.algebraMap_injective (CFieldSpec.K α)
  have ha1 : amG α q1 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq1
  have ha2 : amG α q2 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq2
  rw [hf, hg, map_add, map_mul, map_mul, map_mul, div_add_div _ _ ha1 ha2,
    mul_comm (amG α q1) (amG α p2)]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **Order extraction**: if `amG r/amG D` is `Q`-regular, `D ≠ 0`, `Q^e ∣ D`, then `Q^e ∣ r`. -/
theorem dvd_num_of_isQRegularG {Q r D : (CFieldSpec.K α)[X]} {e : ℕ} (hD : D ≠ 0) (hQe : Q ^ e ∣ D)
    (hf : IsQRegularG Q (amG α r / amG α D)) : Q ^ e ∣ r := by
  obtain ⟨p, q, hq, hQ, heq⟩ := hf
  have hinj := RatFunc.algebraMap_injective (CFieldSpec.K α)
  have had : amG α D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have haq : amG α q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq
  have hpoly : r * q = p * D := by
    apply hinj
    rw [div_eq_div_iff had haq] at heq
    rw [map_mul, map_mul]; linear_combination heq
  exact (hQ.pow_left).dvd_of_dvd_mul_right (by rw [hpoly]; exact hQe.mul_left p)

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
      rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one], one_mul]
  exact ⟨_, _, by rw [hden]; exact pow_ne_zero N hv, by rw [hden]; exact hcop.pow_right, rfl⟩

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- Cross-multiplied fraction-pair addition reads as the fraction sum:
`⟦(a₁·b₂ + b₁·a₂) / (a₂·b₂)⟧ = ⟦a₁/a₂⟧ + ⟦b₁/b₂⟧` (denominators nonzero). -/
theorem fracPair_add (a1 a2 b1 b2 : CPolyG α) (ha2 : toPolyG a2 ≠ 0) (hb2 : toPolyG b2 ≠ 0) :
    amG α (toPolyG (caddG (cmulG a1 b2) (cmulG b1 a2))) / amG α (toPolyG (cmulG a2 b2))
      = amG α (toPolyG a1) / amG α (toPolyG a2) + amG α (toPolyG b1) / amG α (toPolyG b2) := by
  rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG, map_add, map_mul, map_mul, map_mul,
    div_add_div _ _ (amG_toPolyG_ne_zero ha2) (amG_toPolyG_ne_zero hb2)]
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
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
  have hz : toPolyG ([CField.zero] : CPolyG α) = 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_zero, mul_zero, add_zero, map_zero]
  rw [cHermiteReduceTowerGWf]
  simp only [toPolyG_cnormG]
  rw [fracPair_foldl_sum
    (fun x => (cHermiteReduceTowerInnerWf Dt x.1 (cdivWf d (cpowG x.1 (x.2 + 1))) (x.2 + 1 - 1) a
      ([CField.zero], [CField.one])).1)
    (fun x => x.2 + 1 ≤ 1) (cSqfreeYunFFGWf d).zipIdx ([CField.zero], [CField.one])
    (by rw [hone]; exact one_ne_zero) hden]
  rw [hz, hone, map_zero, map_one, zero_div, zero_add]

end DeepWiki.SymbolicIntegration
