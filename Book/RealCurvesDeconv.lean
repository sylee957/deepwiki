import Book.RealCurvesConv

/-! Deconvolution of the real curves and the `affine` curve: `minDeconv` of
token-bucket/rate against rate-latency and rate, the stable closed forms and
the unstable `⊤` cases, with the supporting affine-shift and bound lemmas. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

/-- `min A B ≤ min a1 a2 + min c1 c2` from the four cross bounds. -/
theorem min_le_min_add_min {A B a1 a2 c1 c2 : ℝ≥0∞}
    (h11 : min A B ≤ a1 + c1) (h12 : min A B ≤ a1 + c2)
    (h21 : min A B ≤ a2 + c1) (h22 : min A B ≤ a2 + c2) :
    min A B ≤ min a1 a2 + min c1 c2 := by
  rcases le_total a1 a2 with ha | ha <;>
    rcases le_total c1 c2 with hc | hc <;>
    [ (rw [min_eq_left ha, min_eq_left hc]; exact h11);
      (rw [min_eq_left ha, min_eq_right hc]; exact h12);
      (rw [min_eq_right ha, min_eq_left hc]; exact h21);
      (rw [min_eq_right ha, min_eq_right hc];
        exact h22) ]

/-- The min of two affine curves is subadditive. -/
theorem affine_min_subadd (r b r' b' s t : ℝ≥0) :
    min (((r*(s+t)+b : ℝ≥0)):ℝ≥0∞)
        (((r'*(s+t)+b' : ℝ≥0)):ℝ≥0∞)
      ≤ min (((r*s+b:ℝ≥0)):ℝ≥0∞) (((r'*s+b':ℝ≥0)):ℝ≥0∞)
        + min (((r*t+b:ℝ≥0)):ℝ≥0∞)
            (((r'*t+b':ℝ≥0)):ℝ≥0∞) := by
  have cle : ∀ {a x y : ℝ≥0}, (a:ℝ) ≤ (x:ℝ) + (y:ℝ) →
      ((a:ℝ≥0):ℝ≥0∞) ≤ ((x:ℝ≥0):ℝ≥0∞) + ((y:ℝ≥0):ℝ≥0∞) := by
    intro a x y h
    rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
    exact_mod_cast h
  refine min_le_min_add_min ?_ ?_ ?_ ?_
  · exact le_trans (min_le_left _ _)
      (cle (by push_cast; nlinarith [b.coe_nonneg]))
  · rcases le_total r r' with h | h
    · exact le_trans (min_le_left _ _) (cle (by
        push_cast; nlinarith [b.coe_nonneg, b'.coe_nonneg,
          t.coe_nonneg, NNReal.coe_le_coe.mpr h]))
    · exact le_trans (min_le_right _ _) (cle (by
        push_cast; nlinarith [b.coe_nonneg, b'.coe_nonneg,
          s.coe_nonneg, NNReal.coe_le_coe.mpr h]))
  · rcases le_total r r' with h | h
    · exact le_trans (min_le_left _ _) (cle (by
        push_cast; nlinarith [b.coe_nonneg, b'.coe_nonneg,
          s.coe_nonneg, NNReal.coe_le_coe.mpr h]))
    · exact le_trans (min_le_right _ _) (cle (by
        push_cast; nlinarith [b.coe_nonneg, b'.coe_nonneg,
          t.coe_nonneg, NNReal.coe_le_coe.mpr h]))
  · exact le_trans (min_le_right _ _)
      (cle (by push_cast; nlinarith [b'.coe_nonneg]))

/-- For `t ≠ 0`, `tokenBucket r b t = r * t + b`. -/
theorem tokenBucket_apply_pos (r b t : ℝ≥0)
    (ht : t ≠ 0) :
    tokenBucket r b t = (r:ℝ≥0∞) * t + b := by
  have h0 : ¬ t ≤ 0 := by simpa using ht
  simp only [tokenBucket_apply, delayNN, delay_apply, if_neg h0,
    min_top_right]

/-- The min of two token-buckets is subadditive. -/
theorem tokenBucket_inf_subadd (r b r' b' : ℝ≥0) :
    IsSubadditive
      (tokenBucket r b ⊓ tokenBucket r' b') := by
  intro u s
  simp only [Pi.inf_apply]
  rcases eq_or_ne u 0 with hu | hu
  · subst hu
    rw [tokenBucket_zero_eq, tokenBucket_zero_eq, min_self,
      zero_add, zero_add]
  · rcases eq_or_ne s 0 with hs | hs
    · subst hs
      rw [tokenBucket_zero_eq, tokenBucket_zero_eq,
        min_self, add_zero, add_zero]
    · have hus : (u + s) ≠ 0 := by
        rw [← pos_iff_ne_zero] at hu ⊢; positivity
      rw [tokenBucket_apply_pos r b u hu,
          tokenBucket_apply_pos r' b' u hu,
          tokenBucket_apply_pos r b s hs,
          tokenBucket_apply_pos r' b' s hs,
          tokenBucket_apply_pos r b (u + s) hus,
          tokenBucket_apply_pos r' b' (u + s) hus]
      have key := affine_min_subadd r b r' b' u s
      push_cast at key
      convert key using 2

/-- Token-bucket convolution equals their pointwise min. -/
theorem conv_tokenBucket_tokenBucket (r b r' b' : ℝ≥0) :
    minConv (tokenBucket r b) (tokenBucket r' b')
      = tokenBucket r b ⊓ tokenBucket r' b' :=
  minConvE_eq_inf_of_subadd _ _
    (tokenBucket_zero_eq r b) (tokenBucket_zero_eq r' b')
    (tokenBucket_inf_subadd r b r' b')

/-- Affine curve `t ↦ r * t + b` (no clamp at `0`). -/
noncomputable def affine (r b : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => (r:ℝ≥0∞) * t + b

/-- `affine r b ⊓ delayNN 0 = tokenBucket r b`. -/
theorem affine_inf_delay0 (r b : ℝ≥0) :
    affine r b ⊓ delayNN 0 = tokenBucket r b := by
  rw [tokenBucket_eq]; rfl

/-- `affine r 0 = rate r`. -/
theorem affine_zero (r : ℝ≥0) : affine r 0 = rate r := by
  funext t
  simp only [affine, rate_apply, ENNReal.coe_zero, add_zero]

/-- `rateLatency R 0 = rate R`. -/
theorem rateLatency_zero (R : ℝ≥0) :
    rateLatency R 0 = rate R := by
  funext t; simp only [rateLatency, rate_apply, tsub_zero]

/-- `tokenBucket R 0 = rate R`. -/
theorem tokenBucket_zero_rate (R : ℝ≥0) :
    tokenBucket R 0 = rate R := by
  funext t
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; rw [tokenBucket_zero_eq]; simp
  · rw [tokenBucket_apply_pos R 0 t ht]; simp

/-- `tokenBucket r b` is monotone. -/
theorem tokenBucket_mono (r b : ℝ≥0) :
    Monotone (tokenBucket r b) := by
  intro a c hac
  simp only [tokenBucket_apply]
  exact min_le_min (by gcongr) (delayNN_mono 0 hac)

/-- `delayNN d ⊘ delayNN d' = delayNN (d - d')` when `d' ≤ d`. -/
theorem minDeconv_delayNN_delayNN (d d' : ℝ≥0) (h : d' ≤ d) :
    minDeconv (delayNN d) (delayNN d') = delayNN (d - d') := by
  rw [minDeconv_delayNN (delayNN d) (delayNN_mono d) d']
  funext t
  show (if t + d' ≤ d then (0:ℝ≥0∞) else ⊤)
      = delayNN (d - d') t
  simp only [delayNN, delay_apply]; congr 1; rw [le_tsub_iff_right h]

/-- `rate R ⊘ delayNN d = affine R (R * d)`. -/
theorem minDeconv_rate_delayNN (R d : ℝ≥0) :
    minDeconv (rate R) (delayNN d) = affine R (R * d) := by
  rw [minDeconv_delayNN (rate R) (rate_mono R) d]
  funext t; simp only [rate_apply, affine]; push_cast; ring

/-- `tokenBucket r b ⊘ delayNN d = affine r (b + r * d)` for `d > 0`. -/
theorem minDeconv_tokenBucket_delay (r b d : ℝ≥0)
    (hd : 0 < d) :
    minDeconv (tokenBucket r b) (delayNN d)
      = affine r (b + r * d) := by
  rw [minDeconv_delayNN (tokenBucket r b)
    (tokenBucket_mono r b) d]
  funext t
  have htd : t + d ≠ 0 := by positivity
  rw [tokenBucket_apply_pos r b (t + d) htd]
  simp only [affine]; push_cast; ring

/-- Affine shift bound against a rate-latency term (`r ≤ R`). -/
theorem affine_shift_bound (r b R T t u : ℝ≥0)
    (h : r ≤ R) :
    affine r b (t + u)
      ≤ affine r (b + r*T) t + rateLatency R T u := by
  simp only [affine, rateLatency]
  have key : (r*(t+u)+b : ℝ≥0)
      ≤ (r*t+(b+r*T)) + R*(u-T) := by
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub_def]
    rcases le_total u T with hu | hu
    · rw [max_eq_right (by
        have := NNReal.coe_le_coe.mpr hu; linarith)]
      nlinarith [mul_le_mul_of_nonneg_left
        (NNReal.coe_le_coe.mpr hu) r.coe_nonneg]
    · rw [max_eq_left (by
        have := NNReal.coe_le_coe.mpr hu; linarith)]
      nlinarith [mul_le_mul_of_nonneg_right
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hu))]
  calc (r:ℝ≥0∞)*(t+u)+b
        = ((r*(t+u)+b : ℝ≥0):ℝ≥0∞) := by push_cast; ring
    _ ≤ (((r*t+(b+r*T)) + R*(u-T) : ℝ≥0):ℝ≥0∞) := by
        exact_mod_cast key
    _ = ((r:ℝ≥0∞)*t+(b+r*T)) + (R:ℝ≥0∞)*(u-T) := by
        push_cast; ring

/-- `tokenBucket r b ≤ affine r b` pointwise. -/
theorem tokenBucket_le_affine (r b t : ℝ≥0) :
    tokenBucket r b t ≤ affine r b t := by
  simp only [tokenBucket_apply, affine]
  exact min_le_left _ _

/-- `tokenBucket r b ⊘ βRT = affine r (b + r*T)` for `r ≤ R`, `T > 0`. -/
theorem minDeconv_tokenBucket_rateLatency
    (r b R T : ℝ≥0) (h : r ≤ R) (hT : 0 < T) :
    minDeconv (tokenBucket r b) (rateLatency R T)
      = affine r (b + r*T) := by
  funext t
  apply le_antisymm
  · unfold minDeconv
    refine iSup_le (fun u => ?_)
    refine le_trans (tsub_le_iff_right.mpr ?_) le_rfl
    exact le_trans (tokenBucket_le_affine r b (t+u))
      (affine_shift_bound r b R T t u h)
  · unfold minDeconv
    refine le_iSup_of_le T ?_
    have htT : t + T ≠ 0 := by positivity
    rw [tokenBucket_apply_pos r b (t+T) htT]
    have hbeta : rateLatency R T T = 0 := by
      simp only [rateLatency, tsub_self]; simp
    rw [hbeta, tsub_zero]
    simp only [affine]; push_cast; ring_nf; rfl

/-- Lower bound on a single deconvolution term when `R ≤ r`. -/
theorem minDeconv_term_lb (r b R T t u : ℝ≥0)
    (hRr : R ≤ r) (hu : T ≤ u) (htu : t + u ≠ 0) :
    ((((r-R)*(u-T) : ℝ≥0)):ℝ≥0∞)
      ≤ tokenBucket r b (t+u) - rateLatency R T u := by
  rw [tokenBucket_apply_pos r b (t+u) htu]
  have hβ : rateLatency R T u
      = ((R*(u-T):ℝ≥0):ℝ≥0∞) := by
    simp only [rateLatency]; push_cast; ring
  rw [hβ]
  apply ENNReal.le_sub_of_add_le_right ENNReal.coe_ne_top
  rw [← ENNReal.coe_mul, ← ENNReal.coe_add,
      ← ENNReal.coe_add, ENNReal.coe_le_coe,
      ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub_def]
  have hT : (↑T:ℝ) ≤ ↑u := NNReal.coe_le_coe.mpr hu
  have hR : (↑R:ℝ) ≤ ↑r := NNReal.coe_le_coe.mpr hRr
  rw [max_eq_left (show (0:ℝ) ≤ ↑u - ↑T by linarith),
      max_eq_left (show (0:ℝ) ≤ ↑r - ↑R by linarith)]
  nlinarith [r.coe_nonneg, b.coe_nonneg,
    mul_nonneg r.coe_nonneg t.coe_nonneg,
    mul_nonneg r.coe_nonneg T.coe_nonneg]

/-- `⨆ s, c * s = ⊤` over `ℝ≥0` when `c > 0`. -/
theorem iSup_coe_mul_eq_top (c : ℝ≥0) (hc : 0 < c) :
    (⨆ s : ℝ≥0, ((c * s : ℝ≥0):ℝ≥0∞)) = ⊤ := by
  rw [iSup_eq_top]; intro M hM
  lift M to ℝ≥0 using hM.ne with M'
  refine ⟨(M'/c) + 1, ?_⟩
  rw [ENNReal.coe_lt_coe,
    show c * (M'/c + 1) = (M'/c)*c + c by ring,
    div_mul_cancel₀ M' hc.ne']
  exact lt_add_of_le_of_pos le_rfl hc

/-- `tokenBucket r b ⊘ βRT = ⊤` when `R < r` (unstable). -/
theorem minDeconv_tokenBucket_rateLatency_top
    (r b R T : ℝ≥0) (hRr : R < r) :
    minDeconv (tokenBucket r b) (rateLatency R T)
      = fun _ => (⊤:ℝ≥0∞) := by
  funext t
  rw [eq_top_iff]
  have hpos : 0 < r - R := tsub_pos_of_lt hRr
  rw [← iSup_coe_mul_eq_top (r - R) hpos]
  refine iSup_le ?_
  intro w
  refine le_iSup_of_le (T + w) ?_
  by_cases htu : t + (T + w) = 0
  · have hw : w = 0 := by
      have h2 : w ≤ t + (T + w) :=
        le_add_self.trans
          (by rw [add_comm]; exact le_add_self)
      simpa [htu] using h2
    simp [hw]
  · have hu : T ≤ T + w := le_self_add
    have hlb := minDeconv_term_lb r b R T t (T + w)
      hRr.le hu htu
    refine le_trans ?_ hlb
    rw [ENNReal.coe_le_coe]
    have he : (T + w) - T = w := by simp
    rw [he]

/-- The deconvolution `sup` against `rate R` is at least `b` (`r ≤ R`). -/
theorem minDeconv_origin_lb (r b R : ℝ≥0) (h : r ≤ R) :
    (b:ℝ≥0∞)
      ≤ ⨆ s : ℝ≥0, tokenBucket r b s - rate R s := by
  rw [le_iSup_iff]
  intro c hc
  by_contra hbc
  rw [not_le] at hbc
  lift c to ℝ≥0 using hbc.ne_top with c'
  rw [ENNReal.coe_lt_coe] at hbc
  rcases eq_or_lt_of_le h with hRr | hRr
  · subst hRr
    have h1 := hc 1
    rw [tokenBucket_apply_pos r b 1 one_ne_zero,
      rate_apply] at h1
    simp only [ENNReal.coe_one, mul_one] at h1
    rw [ENNReal.add_sub_cancel_left
      ENNReal.coe_ne_top] at h1
    exact absurd (ENNReal.coe_le_coe.mp h1)
      (not_le.mpr hbc)
  · set d := R - r with hd
    have hdpos : 0 < d := tsub_pos_of_lt hRr
    have hgpos : 0 < b - c' := tsub_pos_of_lt hbc
    set s := (b - c') / (2 * d) with hs
    have hsne : s ≠ 0 := by rw [hs]; positivity
    have hcs := hc s
    rw [tokenBucket_apply_pos r b s hsne, rate_apply] at hcs
    have hRcoe : (R:ℝ≥0∞) * s
        = ((R * s : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_mul]
    have hrcoe : (r:ℝ≥0∞) * s + b
        = ((r * s + b : ℝ≥0):ℝ≥0∞) := by
      rw [ENNReal.coe_add, ENNReal.coe_mul]
    rw [hRcoe, hrcoe, ← ENNReal.coe_sub,
      ENNReal.coe_le_coe] at hcs
    apply absurd hcs
    rw [not_le, ← NNReal.coe_lt_coe]
    push_cast [NNReal.coe_sub_def]
    have hcr : (c':ℝ) < b := by exact_mod_cast hbc
    have hdr : (0:ℝ) < d := by exact_mod_cast hdpos
    have hds : (d:ℝ) * s = ((b:ℝ) - c')/2 := by
      rw [hs]
      push_cast [NNReal.coe_sub_def,
        max_eq_left (by linarith : (0:ℝ) ≤ ↑b - ↑c')]
      field_simp
    have hRrd : (R:ℝ) = (r:ℝ) + d := by
      have he : ((R - r : ℝ≥0):ℝ) = (R:ℝ) - r :=
        NNReal.coe_sub h
      rw [hd]; rw [he]; ring
    have hexp : (R:ℝ) * s = r * s + d * s := by
      rw [hRrd]; ring
    have hval : (↑r * ↑s + ↑b - ↑R * ↑s : ℝ)
        = (↑b + ↑c')/2 := by
      rw [hexp,
        show (↑r*↑s+↑b-(↑r*↑s+↑d*↑s):ℝ)
          = ↑b - ↑d*↑s by ring, hds]
      ring
    rw [max_eq_left (by
      rw [hval]
      linarith [c'.coe_nonneg, b.coe_nonneg]), hval]
    linarith

/-- Affine shift bound against a `rate R` term (`r ≤ R`). -/
theorem affine_shift_bound0 (r b R t u : ℝ≥0)
    (h : r ≤ R) :
    affine r b (t + u) ≤ affine r b t + rate R u := by
  simp only [affine, rate_apply]
  have key : (r*(t+u)+b : ℝ≥0) ≤ (r*t+b) + R*u := by
    rw [← NNReal.coe_le_coe]; push_cast
    nlinarith [mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.mpr h) u.coe_nonneg]
  calc (r:ℝ≥0∞)*(t+u)+b
        = ((r*(t+u)+b : ℝ≥0):ℝ≥0∞) := by push_cast; ring
    _ ≤ (((r*t+b) + R*u : ℝ≥0):ℝ≥0∞) := by
        exact_mod_cast key
    _ = ((r:ℝ≥0∞)*t+b) + (R:ℝ≥0∞)*u := by
        push_cast; ring

/-- `tokenBucket r b ⊘ rate R = affine r b` when `r ≤ R`. -/
theorem minDeconv_tokenBucket_rate (r b R : ℝ≥0)
    (h : r ≤ R) :
    minDeconv (tokenBucket r b) (rate R) = affine r b := by
  funext t
  apply le_antisymm
  · unfold minDeconv
    refine iSup_le (fun u => ?_)
    refine le_trans (tsub_le_iff_right.mpr ?_) le_rfl
    exact le_trans (tokenBucket_le_affine r b (t+u))
      (affine_shift_bound0 r b R t u h)
  · rcases eq_or_ne t 0 with ht | ht
    · subst ht
      simp only [affine, ENNReal.coe_zero, mul_zero,
        zero_add]
      unfold minDeconv; simp only [zero_add]
      exact minDeconv_origin_lb r b R h
    · unfold minDeconv; refine le_iSup_of_le 0 ?_
      rw [add_zero, tokenBucket_apply_pos r b t ht]
      simp only [rate_apply, ENNReal.coe_zero, mul_zero,
        tsub_zero, affine, le_refl]

/-- `tokenBucket r b ⊘ rate R = ⊤` when `R < r` (unstable). -/
theorem minDeconv_tokenBucket_rate_top (r b R : ℝ≥0)
    (hRr : R < r) :
    minDeconv (tokenBucket r b) (rate R)
      = fun _ => (⊤:ℝ≥0∞) := by
  rw [← rateLatency_zero R]
  exact minDeconv_tokenBucket_rateLatency_top r b R 0 hRr

/-- `rate R ⊘ rate R' = rate R` when `R ≤ R'`. -/
theorem minDeconv_rate_rate (R R' : ℝ≥0) (h : R ≤ R') :
    minDeconv (rate R) (rate R') = rate R := by
  conv_lhs => rw [← tokenBucket_zero_rate R]
  rw [minDeconv_tokenBucket_rate R 0 R' h, affine_zero]

/-- `rate R ⊘ rate R' = ⊤` when `R' < R` (unstable). -/
theorem minDeconv_rate_rate_top (R R' : ℝ≥0) (h : R' < R) :
    minDeconv (rate R) (rate R')
      = fun _ => (⊤:ℝ≥0∞) := by
  conv_lhs => rw [← tokenBucket_zero_rate R]
  exact minDeconv_tokenBucket_rate_top R 0 R' h
end DeepWiki
