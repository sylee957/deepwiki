import DeepWiki.NetworkCalculus.ServersResidualPmooRateLatency
import DeepWiki.NetworkCalculus.ServiceCurveMinimal
import DeepWiki.NetworkCalculus.ServersConcatenationChain

/-! # Rate-latency convolution in the `EReal` `concatConv` world
The `List`-indexed end-to-end service curve `concatConv` (used by SFA / GFA / SP-PMOO) is built from
the `EReal` `minConv`. When every hop offers a rate-latency curve, the convolution folds to a single
rate-latency curve `β_{⨅Rₕ, ∑Tₕ}` — the `EReal`/`List` analogue of the `ℝ≥0`/`ℕ`
`chainConv_rateLatency`. This is the closed form that turns a `concatConv` end-to-end service curve
into an explicit rate-latency, enabling end-to-end delay/backlog bounds over arbitrary `List` routing. -/

namespace DeepWiki

open scoped NNReal BigOperators

/-- **EReal rate-latency convolution**: `β_{R,T} ∗ β_{R',T'} = β_{R⊓R', T+T'}` over the
`EReal`-lifted curves (the `minConv` used by `concatConv`), mirroring the `ℝ≥0`
`minConvProj_rateLatency`. The `≥` direction reuses `minConvProj_rateLatency`; the `≤` direction
exhibits the achieving split per case (`t ≤ T+T'`, then `R ≤ R'` / `R' ≤ R`). -/
theorem minConv_liftEReal_rateLatency (R T R' T' : ℝ≥0) :
    minConv (liftEReal (rateLatency R T)) (liftEReal (rateLatency R' T'))
      = liftEReal (rateLatency (R ⊓ R') (T + T')) := by
  funext t
  apply le_antisymm
  · rcases le_total t (T + T') with htle | htle
    · refine le_trans (minConv_le_add _ _ (add_tsub_cancel_of_le (min_le_left t T))) ?_
      have e1 : rateLatency R T (min t T) = 0 := by
        show R * (min t T - T) = 0; rw [tsub_eq_zero_of_le (min_le_right _ _), mul_zero]
      have e2 : rateLatency R' T' (t - min t T) = 0 := by
        show R' * ((t - min t T) - T') = 0
        rw [tsub_eq_zero_of_le ?_, mul_zero]
        rcases le_total t T with h | h
        · rw [min_eq_left h, tsub_self]; exact zero_le'
        · rw [min_eq_right h, tsub_le_iff_left]; exact htle
      have e3 : rateLatency (R ⊓ R') (T + T') t = 0 := by
        show (R ⊓ R') * (t - (T + T')) = 0; rw [tsub_eq_zero_of_le htle, mul_zero]
      simp only [liftEReal, e1, e2, e3]; norm_num
    · have hsub : (t - T') - T = t - (T + T') := by rw [tsub_tsub, add_comm T' T]
      have hsub' : (t - T) - T' = t - (T + T') := by rw [tsub_tsub]
      rcases le_total R R' with hR | hR
      · refine le_trans (minConv_le_add _ _
          (tsub_add_cancel_of_le (le_trans le_add_self htle))) ?_
        have e2 : rateLatency R' T' T' = 0 := by show R' * (T' - T') = 0; rw [tsub_self, mul_zero]
        have key : rateLatency R T (t - T') ≤ rateLatency (R ⊓ R') (T + T') t := by
          show R * ((t - T') - T) ≤ (R ⊓ R') * (t - (T + T')); rw [hsub, min_eq_left hR]
        simp only [liftEReal, e2, NNReal.coe_zero, EReal.coe_zero, add_zero]
        exact_mod_cast key
      · refine le_trans (minConv_le_add _ _
          (add_tsub_cancel_of_le (le_trans le_self_add htle))) ?_
        have e1 : rateLatency R T T = 0 := by show R * (T - T) = 0; rw [tsub_self, mul_zero]
        have key : rateLatency R' T' (t - T) ≤ rateLatency (R ⊓ R') (T + T') t := by
          show R' * ((t - T) - T') ≤ (R ⊓ R') * (t - (T + T')); rw [hsub', min_eq_right hR]
        simp only [liftEReal, e1, NNReal.coe_zero, EReal.coe_zero, zero_add]
        exact_mod_cast key
  · refine le_minConv fun u s hus => ?_
    have hge : rateLatency (R ⊓ R') (T + T') t ≤ rateLatency R T u + rateLatency R' T' s := by
      rw [← minConvProj_rateLatency, minConvProj_eq]
      exact ciInf_le_of_le (OrderBot.bddBelow _) ⟨(u, s), hus⟩ le_rfl
    simp only [liftEReal]; exact_mod_cast hge

variable {κ : Type*}

/-- Min rate of the rate-latency hops `β_{R·,T·}` over the path `h :: hs`. -/
def pathMinRate (R : κ → ℝ≥0) : κ → List κ → ℝ≥0
  | h, [] => R h
  | h, (k :: ks) => R h ⊓ pathMinRate R k ks

/-- Summed latency of the rate-latency hops `β_{R·,T·}` over the path `h :: hs`. -/
def pathSumLatency (T : κ → ℝ≥0) : κ → List κ → ℝ≥0
  | h, [] => T h
  | h, (k :: ks) => T h + pathSumLatency T k ks

/-- **The concatenation of rate-latency servers along a (nonempty) path is rate-latency**:
`∗_{k ∈ h::hs} β_{R k, T k} = β_{⨅ R, ∑ T}` over the path — the `EReal`/`List` analogue of
`chainConv_rateLatency`. -/
theorem concatConv_liftEReal_rateLatency (R T : κ → ℝ≥0) (h : κ) (hs : List κ) :
    concatConv (fun k => liftEReal (rateLatency (R k) (T k))) (h :: hs)
      = liftEReal (rateLatency (pathMinRate R h hs) (pathSumLatency T h hs)) := by
  induction hs generalizing h with
  | nil =>
    rw [concatConv_singleton (fun k => liftEReal (rateLatency (R k) (T k))) h
      (isNonneg_liftEReal (rateLatency (R h) (T h))).isBddBelowReal]
    rfl
  | cons k ks ih => rw [concatConv_cons, ih k, minConv_liftEReal_rateLatency]; rfl

/-- `pathSumLatency` is the sum of the per-hop latencies along the path `h :: hs`. -/
theorem pathSumLatency_eq_sum (T : κ → ℝ≥0) (h : κ) (hs : List κ) :
    pathSumLatency T h hs = ((h :: hs).map T).sum := by
  induction hs generalizing h with
  | nil => simp [pathSumLatency]
  | cons k ks ih =>
    rw [pathSumLatency, ih k]
    simp only [List.map_cons, List.sum_cons]

/-- `pathMinRate` is below the head hop's rate. -/
theorem pathMinRate_le_head (R : κ → ℝ≥0) (h : κ) (hs : List κ) :
    pathMinRate R h hs ≤ R h := by
  cases hs with
  | nil => exact le_refl _
  | cons k ks => exact inf_le_left

/-- `pathMinRate` is positive when every hop's rate along the path is. -/
theorem pathMinRate_pos (R : κ → ℝ≥0) (h : κ) (hs : List κ)
    (hpos : ∀ k ∈ h :: hs, 0 < R k) : 0 < pathMinRate R h hs := by
  induction hs generalizing h with
  | nil => exact hpos h (List.mem_singleton.mpr rfl)
  | cons k ks ih =>
    rw [pathMinRate, lt_inf_iff]
    refine ⟨hpos h (by simp), ih k (fun j hj => hpos j ?_)⟩
    simp only [List.mem_cons] at hj ⊢
    tauto

/-- A value below every hop's rate along the path is below `pathMinRate`. -/
theorem le_pathMinRate (R : κ → ℝ≥0) (c : ℝ≥0) (h : κ) (hs : List κ)
    (hle : ∀ k ∈ h :: hs, c ≤ R k) : c ≤ pathMinRate R h hs := by
  induction hs generalizing h with
  | nil => exact hle h (List.mem_singleton.mpr rfl)
  | cons k ks ih =>
    rw [pathMinRate, le_inf_iff]
    refine ⟨hle h (by simp), ih k (fun j hj => hle j ?_)⟩
    simp only [List.mem_cons] at hj ⊢
    tauto

end DeepWiki
