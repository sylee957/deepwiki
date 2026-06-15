import DeepWiki.NetworkCalculus.Stability

/-! # Rate-level algebra of long-term rates
The arithmetic the SFA rate route needs: the long-term service rate is monotone,
and a truncated difference splits the rate below — `R(β) ≤ r(α) + R(β − α)`.
The latter rests on the mixed bound `liminf (u + v) ≤ limsup u + liminf v`
(no off-the-shelf lemma applies — `ℝ≥0∞` is not a group and `atTop` is not a
`CountableInterFilter`; this is the hand proof, the `liminf` sibling of
`limsup_add_le_atTop`). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Filter

/-- Mixed sub/super-additivity at `atTop` in `ℝ≥0∞`: `liminf (u + v) ≤
limsup u + liminf v`. (The `ε`-device supplies finiteness, so no hypothesis is
needed.) -/
theorem liminf_le_limsup_add_liminf (u v : ℝ≥0 → ℝ≥0∞) :
    liminf (fun t => u t + v t) atTop ≤ limsup u atTop + liminf v atTop := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hfin => ?_
  set Lu := limsup u atTop
  set Lv := liminf v atTop
  obtain ⟨hLuf, hLvf⟩ := ENNReal.add_lt_top.mp hfin
  have hε2 : (↑(ε / 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (div_ne_zero hε.ne' two_ne_zero)
  have heu : ∀ᶠ t in atTop, u t < Lu + (ε / 2 : ℝ≥0) :=
    eventually_lt_of_limsup_lt (ENNReal.lt_add_right hLuf.ne hε2)
  have hfv : ∃ᶠ t in atTop, v t < Lv + (ε / 2 : ℝ≥0) :=
    frequently_lt_of_liminf_lt (h := ENNReal.lt_add_right hLvf.ne hε2)
  refine liminf_le_of_frequently_le' ((hfv.and_eventually heu).mono fun t ht => ?_)
  calc u t + v t ≤ (Lu + (ε / 2 : ℝ≥0)) + (Lv + (ε / 2 : ℝ≥0)) := add_le_add ht.2.le ht.1.le
    _ = (Lu + Lv) + ((ε / 2 : ℝ≥0) + (ε / 2 : ℝ≥0)) := by ring
    _ = (Lu + Lv) + (ε : ℝ≥0) := by rw [← ENNReal.coe_add]; norm_num

/-- The long-term service rate is monotone: `β₁ ≤ β₂ ⟹ R(β₁) ≤ R(β₂)` (the
`liminf` dual of `longTermArrivalRate_mono`). -/
theorem longTermServiceRate_mono {β₁ β₂ : ℝ≥0 → ℝ≥0} (h : ∀ t, β₁ t ≤ β₂ t) :
    longTermServiceRate β₁ ≤ longTermServiceRate β₂ := by
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun t => ?_)
  show (β₁ t : ℝ≥0∞) / (t : ℝ≥0∞) ≤ (β₂ t : ℝ≥0∞) / (t : ℝ≥0∞)
  gcongr
  exact_mod_cast h t

/-- Scaling the service curve scales its long-term rate:
`R(c·β) = c · R(β)` (the constant factors out of the `liminf`). -/
theorem longTermServiceRate_const_mul (c : ℝ≥0) (β : ℝ≥0 → ℝ≥0) :
    longTermServiceRate (fun t => c * β t) = (c : ℝ≥0∞) * longTermServiceRate β := by
  simp only [longTermServiceRate]
  rw [← ENNReal.liminf_const_mul_of_ne_top (a := (c : ℝ≥0∞)) ENNReal.coe_ne_top]
  refine Filter.liminf_congr (Filter.Eventually.of_forall fun t => ?_)
  rw [ENNReal.coe_mul, mul_div_assoc]

/-- A truncated difference splits the service rate below: `R(β) ≤ r(α) + R(β − α)`.
Pointwise `β t ≤ α t + (β t − α t)`, so `R(β) = liminf (β/t) ≤ liminf (α/t +
(β−α)/t) ≤ limsup (α/t) + liminf ((β−α)/t)` by the mixed bound. -/
theorem longTermServiceRate_tsub_ge (β α : ℝ≥0 → ℝ≥0) :
    longTermServiceRate β
      ≤ longTermArrivalRate α + longTermServiceRate (fun t => β t - α t) := by
  refine le_trans (Filter.liminf_le_liminf (Filter.Eventually.of_forall fun t => ?_))
    (liminf_le_limsup_add_liminf (fun t => (α t : ℝ≥0∞) / (t : ℝ≥0∞))
      (fun t => ((β t - α t : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞)))
  show (β t : ℝ≥0∞) / (t : ℝ≥0∞)
      ≤ (α t : ℝ≥0∞) / (t : ℝ≥0∞) + ((β t - α t : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞)
  rw [← ENNReal.add_div, ← ENNReal.coe_add]
  gcongr
  exact_mod_cast le_add_tsub

end DeepWiki
