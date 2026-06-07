import Book.RealCurvesAdditivity

/-! (min,plus) convolutions of the real curves: `conv_delay`/`deconv_delay`
shift laws, monotonicity, `delay ∗ delay`, `rate ∗ rate`, the rate-latency
convolution algebra, and the `deconv … (delay d)` subadditive closure. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

/-- Convolving with `delay d` shifts: `f ∗ delay d = f(· - d)`. -/
theorem conv_delay (f : ℝ≥0 → ℝ≥0∞)
    (hf : Monotone f) (d : ℝ≥0) :
    minConv f (delay d) = fun t => f (t - d) := by
  funext t
  unfold minConv
  apply le_antisymm
  · rcases le_or_gt t d with ht | ht
    · refine iInf_le_of_le ⟨(0, t), by simp⟩ ?_
      simp only
      rw [show delay d t = 0 by simp [delay, ht], add_zero,
        tsub_eq_zero_of_le ht]
    · refine iInf_le_of_le ⟨(t - d, d), by
        rw [tsub_add_cancel_of_le (le_of_lt ht)]⟩ ?_
      simp only
      rw [show delay d d = 0 by simp [delay], add_zero]
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
    simp only
    rcases le_or_gt s d with hs | hs
    · rw [show delay d s = 0 by simp [delay, hs], add_zero]
      apply hf
      have : u = t - s := by
        rw [← hus, add_tsub_cancel_right]
      rw [this]
      exact tsub_le_tsub_left hs t
    · rw [show delay d s = ⊤ by
        simp [delay, not_le.mpr hs]]
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
theorem conv_delay_posPart (f : ℝ≥0 → ℝ≥0∞) (t d : ℝ≥0) :
    f (t - d) = f ((max ((t : ℝ) - d) 0).toNNReal) := by
  rw [tsub_eq_toNNReal_max]

/-- Deconvolving by `delay d` advances: `f ⊘ delay d = f(· + d)`. -/
theorem deconv_delay (f : ℝ≥0 → ℝ≥0∞)
    (hf : Monotone f) (d : ℝ≥0) :
    deconv f (delay d) = fun t => f (t + d) := by
  funext t
  unfold deconv
  apply le_antisymm
  · refine iSup_le ?_
    intro s
    rcases le_or_gt s d with hs | hs
    · rw [show delay d s = 0 by simp [delay, hs], tsub_zero]
      exact hf (by gcongr)
    · rw [show delay d s = ⊤ by
        simp [delay, not_le.mpr hs]]
      simp
  · refine le_iSup_of_le d ?_
    rw [show delay d d = 0 by simp [delay], tsub_zero]

/-- `deconv g h` is monotone in its first slot when `g` is monotone. -/
theorem minDeconvE_mono {D T : Type*}
    [_root_.AddCommMonoid D] [PartialOrder D]
    [CovariantClass D D (·+·) (·≤·)]
    [CompleteLattice T] [_root_.AddCommMonoid T] [Sub T]
    [OrderedSub T] [CovariantClass T T (·+·) (·≤·)]
    (g h : D → T)
    (hg : Monotone g) : Monotone (deconv g h) := by
  intro x y hxy
  unfold deconv
  refine iSup_le (fun s => ?_)
  refine le_iSup_of_le s ?_
  have hxs : x + s ≤ y + s := by gcongr
  exact tsub_le_tsub_right (hg hxs) (h s)

/-- `delay 0 ⊓ deconv f (delay d)` is subadditive. -/
theorem gdelay_subadd (f : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive f) (hmono : Monotone f)
    (d : ℝ≥0) :
    IsSubadditive (delay 0 ⊓ deconv f (delay d)) := by
  rw [deconv_delay f hmono d]
  intro u s
  simp only [Pi.inf_apply]
  rcases eq_or_ne u 0 with hu | hu
  · subst hu
    have : min (delay 0 0) (f (0 + d)) = 0 := by
      rw [show delay 0 0 = (0:ℝ≥0∞) by simp [delay]]; simp
    rw [this, zero_add, zero_add]
  · rcases eq_or_ne s 0 with hs | hs
    · subst hs
      have : min (delay 0 0) (f (0 + d)) = 0 := by
        rw [show delay 0 0 = (0:ℝ≥0∞) by simp [delay]]; simp
      rw [this, add_zero, add_zero]
    · have hu0 : ¬ u ≤ 0 := by simpa using hu
      have hs0 : ¬ s ≤ 0 := by simpa using hs
      have hus0 : ¬ (u + s) ≤ 0 := by
        rw [nonpos_iff_eq_zero, add_eq_zero]
        rintro ⟨h1, _⟩; exact hu h1
      rw [show delay 0 u = ⊤ by simp [delay, hu0],
          show delay 0 s = ⊤ by simp [delay, hs0],
          show delay 0 (u + s) = ⊤ by simp [delay, hus0],
          min_top_left, min_top_left, min_top_left]
      have harg : u + s + d ≤ (u + d) + (s + d) := by
        have : (u + d) + (s + d) = u + s + (d + d) := by
          ring
        rw [this]; gcongr; exact le_add_right (le_refl d)
      exact le_trans (hmono harg) (hsub (u + d) (s + d))

/-- `delay 0 ⊓ deconv f (delay d)` vanishes at `0`. -/
theorem gdelay_zero (f : ℝ≥0 → ℝ≥0∞)
    (hmono : Monotone f) (d : ℝ≥0) :
    (delay 0 ⊓ deconv f (delay d)) 0 = 0 := by
  rw [deconv_delay f hmono d]
  show min (delay 0 0) (f (0 + d)) = 0
  rw [show delay 0 0 = (0:ℝ≥0∞) by simp [delay]]; simp

/-- `toF (delay 0)` is the convolution unit `δ₀` over `MinPlusNN`. -/
theorem toF_delay0 :
    toF (delay 0) = (convUnit : ℝ≥0 → MinPlusNN) := by
  funext t
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    rw [convUnit, if_pos rfl]
    apply MinPlusNN.ext
    show delay 0 0 = ((eₒ : MinPlusNN) : ℝ≥0∞)
    rw [show delay 0 0 = (0:ℝ≥0∞) by simp [delay]]; rfl
  · rw [convUnit, if_neg ht]
    apply MinPlusNN.ext
    show delay 0 t = ((εₒ : MinPlusNN) : ℝ≥0∞)
    rw [show delay 0 t = ⊤ by
      simp [delay, (by simpa using ht : ¬ t ≤ 0)]]; rfl

/-- Subadditive closure of `deconv f (delay d)` is `delay 0 ⊓ ·`. -/
theorem deconv_delay_closure (f : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive f) (hmono : Monotone f)
    (d : ℝ≥0) :
    subadditiveClosureE (deconv f (delay d))
      = delay 0 ⊓ deconv f (delay d) := by
  set h : ℝ≥0 → ℝ≥0∞ := deconv f (delay d) with hh
  set g : ℝ≥0 → ℝ≥0∞ := delay 0 ⊓ h with hg
  have hgsub : IsSubadditive g :=
    gdelay_subadd f hsub hmono d
  have hg0 : g 0 = 0 := gdelay_zero f hmono d
  have hgh : ∀ t, g t ≤ h t :=
    fun t => min_le_right _ _
  funext t
  apply le_antisymm
  · refine le_min ?_ (subadditiveClosureE_le h t)
    rw [show subadditiveClosureE h t
        = (subadditiveClosure (toF h) t).toVal from rfl,
      ← MinPlusNN.le_iff]
    -- goal: toF (delay 0) t ≼ₒ subadditiveClosure (toF h) t
    have hu : (toF (delay 0)) t ≼ₒ
        subadditiveClosure (toF h) t := by
      rw [congrFun toF_delay0 t]
      have := convPow_le_closure (toF h) 0 t
      simpa [convPow] using this
    exact hu
  · have hgeq := subadditiveClosureE_eq_self g hgsub hg0
    calc g t = subadditiveClosureE g t :=
          (congrFun hgeq t).symm
      _ ≤ subadditiveClosureE h t :=
          subadditiveClosureE_mono g h hgh t

/-- `delay d` is monotone. -/
theorem delay_mono (d : ℝ≥0) : Monotone (delay d) := by
  intro a b hab
  simp only [delay]
  split
  · exact bot_le
  · split
    · rename_i h1 h2; exact absurd (le_trans hab h2) h1
    · exact le_refl _

/-- `rate R` is monotone. -/
theorem rate_mono (R : ℝ≥0) : Monotone (rate R) := by
  intro a b hab; simp only [rate]; gcongr

/-- `delay d ∗ delay d' = delay (d + d')`. -/
theorem conv_delay_delay (d d' : ℝ≥0) :
    minConv (delay d) (delay d') = delay (d + d') := by
  rw [conv_delay (delay d) (delay_mono d) d']
  funext t
  simp only [delay]
  rcases le_or_gt t (d + d') with ht | ht
  · rw [if_pos ht, if_pos (tsub_le_iff_right.mpr ht)]
  · rw [if_neg (not_le.mpr ht),
      if_neg (fun h =>
        absurd (tsub_le_iff_right.mp h) (not_le.mpr ht))]

/-- `rateLatency R T = delay T ∗ rate R`. -/
theorem rateLatency_eq_conv (R T : ℝ≥0) :
    rateLatency R T = minConv (delay T) (rate R) := by
  rw [minConvE_comm, conv_delay (rate R) (rate_mono R) T]
  funext t
  simp only [rate, rateLatency]

/-- `rate R ∗ rate R' = rate (R ⊓ R')`. -/
theorem conv_rate_rate (R R' : ℝ≥0) :
    minConv (rate R) (rate R') = rate (R ⊓ R') := by
  funext t
  unfold minConv rate
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
      minConvE_comm (rate R) (delay T'),
      minConvE_assoc (delay T'), ← minConvE_assoc (delay T),
      conv_delay_delay, conv_rate_rate,
      rateLatency_eq_conv (R ⊓ R') (T + T')]
end DeepWiki
