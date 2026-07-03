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

end DeepWiki.SymbolicIntegration
