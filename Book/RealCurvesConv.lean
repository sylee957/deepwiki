import Book.RealCurvesAdditivity

/-! (min,plus) convolutions of the real curves: `conv_delayNN` and
`minDeconv_delayNN` shift laws, monotonicity, `delayNN ∗ delayNN`, `rate ∗ rate`,
the rate-latency convolution algebra, and the `minDeconv … (delayNN d)`
subadditive closure. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

/-- `δ₀` is a right unit on `ℝ≥0∞` curves: `f ∗ delayNN 0 = f`, for any `f`
(contrast `conv_delayNN`, which needs monotone `f`). -/
theorem conv_delayNN_zero (f : ℝ≥0 → ℝ≥0∞) :
    minConv f (delayNN 0) = f := by
  funext t
  apply le_antisymm
  · refine (minConv_le_add f (delayNN 0) (add_zero t)).trans ?_
    rw [delayNN_zero_eq, add_zero]
  · refine le_minConv fun u s hus => ?_
    rcases eq_or_ne s 0 with hs | hs
    · subst hs
      rw [add_zero] at hus
      rw [delayNN_zero_eq, add_zero, hus]
    · rw [show delayNN 0 s = ⊤ from delay_eq_top 0 (pos_of_ne_zero hs),
        add_top]
      exact le_top

/-- Convolving with `delayNN d` shifts: `f ∗ delayNN d = f(· - d)`. -/
theorem conv_delayNN (f : ℝ≥0 → ℝ≥0∞)
    (hf : Monotone f) (d : ℝ≥0) :
    minConv f (delayNN d) = fun t => f (t - d) := by
  funext t
  unfold minConv
  apply le_antisymm
  · rcases le_or_gt t d with ht | ht
    · refine iInf_le_of_le ⟨(0, t), by simp⟩ ?_
      simp only
      rw [show delayNN d t = 0 by simp [delayNN, ht], add_zero,
        tsub_eq_zero_of_le ht]
    · refine iInf_le_of_le ⟨(t - d, d), by
        rw [tsub_add_cancel_of_le (le_of_lt ht)]⟩ ?_
      simp only
      rw [show delayNN d d = 0 by simp [delayNN], add_zero]
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
    simp only
    rcases le_or_gt s d with hs | hs
    · rw [show delayNN d s = 0 by simp [delayNN, hs], add_zero]
      apply hf
      have : u = t - s := by
        rw [← hus, add_tsub_cancel_right]
      rw [this]
      exact tsub_le_tsub_left hs t
    · rw [show delayNN d s = ⊤ by
        simp [delayNN, not_le.mpr hs]]
      simp

/-- `↑(t - d) = max (t - d) 0` in `ℝ`. -/
theorem tsub_eq_posPart (t d : ℝ≥0) :
    ((t - d : ℝ≥0) : ℝ) = max ((t : ℝ) - d) 0 :=
  NNReal.coe_sub_def

/-- `t - d = (max (t - d) 0).toNNReal`. -/
theorem tsub_eq_toNNReal_max (t d : ℝ≥0) :
    (t - d) = (max ((t : ℝ) - d) 0).toNNReal := by
  apply NNReal.coe_injective
  rw [tsub_eq_posPart,
    Real.coe_toNNReal _ (le_max_right _ _)]

/-- Rewrites the delayed argument as a positive part. -/
theorem conv_delayNN_posPart (f : ℝ≥0 → ℝ≥0∞) (t d : ℝ≥0) :
    f (t - d) = f ((max ((t : ℝ) - d) 0).toNNReal) := by
  rw [tsub_eq_toNNReal_max]

/-- Deconvolving by `delayNN d` advances: `f ⊘ delayNN d = f(· + d)`. -/
theorem minDeconv_delayNN (f : ℝ≥0 → ℝ≥0∞)
    (hf : Monotone f) (d : ℝ≥0) :
    minDeconv f (delayNN d) = fun t => f (t + d) := by
  funext t
  unfold minDeconv
  apply le_antisymm
  · refine iSup_le ?_
    intro s
    rcases le_or_gt s d with hs | hs
    · rw [show delayNN d s = 0 by simp [delayNN, hs], tsub_zero]
      exact hf (by gcongr)
    · rw [show delayNN d s = ⊤ by
        simp [delayNN, not_le.mpr hs]]
      simp
  · refine le_iSup_of_le d ?_
    rw [show delayNN d d = 0 by simp [delayNN], tsub_zero]

/-- `f ⊘̄ delayNN d = 0`: the (max,+) deconvolution collapses to `0`. -/
theorem maxDeconv_delayNN (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0) :
    maxDeconv f (delayNN d) = fun _ => 0 := by
  funext t
  unfold maxDeconv
  apply le_antisymm
  · refine iInf_le_of_le (d + 1) ?_
    rw [show delayNN d (d + 1) = ⊤ by
      simp [delayNN, not_le.mpr (lt_add_one d)]]
    simp
  · exact zero_le'

/-- `delayNN 0 ⊓ minDeconv f (delayNN d)` vanishes at `0`. -/
theorem gdelay_zero (f : ℝ≥0 → ℝ≥0∞)
    (hmono : Monotone f) (d : ℝ≥0) :
    (delayNN 0 ⊓ minDeconv f (delayNN d)) 0 = 0 := by
  rw [minDeconv_delayNN f hmono d]
  show min (delayNN 0 0) (f (0 + d)) = 0
  rw [show delayNN 0 0 = (0:ℝ≥0∞) by simp [delayNN]]; simp

/-- `delayNN 0 ⊓ minDeconv f (delayNN d)` is subadditive. -/
theorem gdelay_subadd (f : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive f) (hmono : Monotone f)
    (d : ℝ≥0) :
    IsSubadditive (delayNN 0 ⊓ minDeconv f (delayNN d)) := by
  refine IsSubadditive.of_ne_zero (gdelay_zero f hmono d)
    fun u s hu hs => ?_
  rw [minDeconv_delayNN f hmono d]
  simp only [Pi.inf_apply]
  have hu0 : ¬ u ≤ 0 := by simpa using hu
  have hs0 : ¬ s ≤ 0 := by simpa using hs
  have hus0 : ¬ (u + s) ≤ 0 := by
    rw [nonpos_iff_eq_zero, add_eq_zero]
    rintro ⟨h1, _⟩; exact hu h1
  rw [show delayNN 0 u = ⊤ by simp [delayNN, hu0],
      show delayNN 0 s = ⊤ by simp [delayNN, hs0],
      show delayNN 0 (u + s) = ⊤ by simp [delayNN, hus0],
      min_top_left, min_top_left, min_top_left]
  have harg : u + s + d ≤ (u + d) + (s + d) := by
    have : (u + d) + (s + d) = u + s + (d + d) := by
      ring
    rw [this]; gcongr; exact le_add_right (le_refl d)
  exact le_trans (hmono harg) (hsub (u + d) (s + d))

/-- `toF (delayNN 0)` is the convolution unit `δ₀` over `MinPlusNN`. -/
theorem toF_delay0 :
    toF (delayNN 0) = (convUnit : ℝ≥0 → MinPlusNN) := by
  funext t
  apply MinPlusNN.ext
  show delayNN 0 t = (convUnit t : MinPlusNN).toVal
  rw [MinPlusNN.convUnit_toVal]
  split_ifs with ht
  · rw [ht, show delayNN 0 0 = (0:ℝ≥0∞) by simp [delayNN]]
  · rw [show delayNN 0 t = ⊤ by
      simp [delayNN, (by simpa using ht : ¬ t ≤ 0)]]

/-- Subadditive closure of `minDeconv f (delayNN d)` is `delayNN 0 ⊓ ·`. -/
theorem minDeconv_delayNN_closure (f : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive f) (hmono : Monotone f)
    (d : ℝ≥0) :
    subadditiveClosureENN (minDeconv f (delayNN d))
      = delayNN 0 ⊓ minDeconv f (delayNN d) := by
  set h : ℝ≥0 → ℝ≥0∞ := minDeconv f (delayNN d) with hh
  set g : ℝ≥0 → ℝ≥0∞ := delayNN 0 ⊓ h with hg
  have hgsub : IsSubadditive g :=
    gdelay_subadd f hsub hmono d
  have hg0 : g 0 = 0 := gdelay_zero f hmono d
  have hgh : ∀ t, g t ≤ h t :=
    fun t => min_le_right _ _
  funext t
  apply le_antisymm
  · refine le_min ?_ (subadditiveClosureENN_le h t)
    rw [show subadditiveClosureENN h t
        = (subadditiveClosure (toF h) t).toVal from rfl,
      ← MinPlusNN.le_iff]
    -- goal: toF (delayNN 0) t ≼ₒ subadditiveClosure (toF h) t
    have hu : (toF (delayNN 0)) t ≼ₒ
        subadditiveClosure (toF h) t := by
      rw [congrFun toF_delay0 t]
      have := convPow_le_closure (toF h) 0 t
      simpa [convPow] using this
    exact hu
  · have hgeq := subadditiveClosureENN_eq_self g hgsub hg0
    calc g t = subadditiveClosureENN g t :=
          (congrFun hgeq t).symm
      _ ≤ subadditiveClosureENN h t :=
          subadditiveClosureENN_mono g h hgh t

/-- `delayNN d` is monotone. -/
theorem delayNN_mono (d : ℝ≥0) : Monotone (delayNN d) := by
  intro a b hab
  simp only [delayNN, delay_apply]
  split
  · exact bot_le
  · split
    · rename_i h1 h2; exact absurd (le_trans hab h2) h1
    · exact le_refl _

/-- `rate R` is monotone. -/
theorem rate_mono (R : ℝ≥0) : Monotone (rate R) := by
  intro a b hab; simp only [rate, rateV]; gcongr

/-- `delayNN d ∗ delayNN d' = delayNN (d + d')`. -/
theorem conv_delayNN_delayNN (d d' : ℝ≥0) :
    minConv (delayNN d) (delayNN d') = delayNN (d + d') := by
  rw [conv_delayNN (delayNN d) (delayNN_mono d) d']
  funext t
  simp only [delayNN, delay_apply]
  rcases le_or_gt t (d + d') with ht | ht
  · rw [if_pos ht, if_pos (tsub_le_iff_right.mpr ht)]
  · rw [if_neg (not_le.mpr ht),
      if_neg (fun h =>
        absurd (tsub_le_iff_right.mp h) (not_le.mpr ht))]

/-- `rateLatency R T = delayNN T ∗ rate R`. -/
theorem rateLatency_eq_conv (R T : ℝ≥0) :
    rateLatency R T = minConv (delayNN T) (rate R) := by
  rw [minConv_comm, conv_delayNN (rate R) (rate_mono R) T]
  funext t
  simp only [rate, rateV, rateLatency]

/-- `rate R ∗ rate R' = rate (R ⊓ R')`. -/
theorem conv_rate_rate (R R' : ℝ≥0) :
    minConv (rate R) (rate R') = rate (R ⊓ R') := by
  funext t
  unfold minConv rate rateV
  apply le_antisymm
  · rcases le_total R R' with h | h
    · refine iInf_le_of_le ⟨(t, 0), by simp⟩ ?_
      simp only; rw [min_eq_left h]; simp
    · refine iInf_le_of_le ⟨(0, t), by simp⟩ ?_
      simp only; rw [min_eq_right h]; simp
  · refine le_iInf ?_
    rintro ⟨⟨u, v⟩, (huv : u + v = t)⟩
    simp only
    rw [← huv]
    calc ((R ⊓ R' : ℝ≥0):ℝ≥0∞) * (u + v)
        = (R ⊓ R') * u + (R ⊓ R') * v := by rw [mul_add]
      _ ≤ R * u + R' * v := by
          gcongr
          · exact_mod_cast min_le_left R R'
          · exact_mod_cast min_le_right R R'

/-- `βRT ∗ βR'T' = β_{R⊓R', T+T'}` for rate-latency curves. -/
theorem conv_rateLatency_rateLatency (R R' T T' : ℝ≥0) :
    minConv (rateLatency R T) (rateLatency R' T')
      = rateLatency (R ⊓ R') (T + T') := by
  rw [rateLatency_eq_conv R T, rateLatency_eq_conv R' T']
  rw [minConvE_assoc, ← minConvE_assoc (rate R),
      minConv_comm (rate R) (delayNN T'),
      minConvE_assoc (delayNN T'), ← minConvE_assoc (delayNN T),
      conv_delayNN_delayNN, conv_rate_rate,
      rateLatency_eq_conv (R ⊓ R') (T + T')]
end DeepWiki
