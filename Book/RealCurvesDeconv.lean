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

/-- For `t ≠ 0`, `tokenBucketNN r b t = r * t + b`. -/
theorem tokenBucketNN_apply_pos (r b t : ℝ≥0)
    (ht : t ≠ 0) :
    tokenBucketNN r b t = (r:ℝ≥0∞) * t + b := by
  have h0 : ¬ t ≤ 0 := by simpa using ht
  simp only [tokenBucketNN_apply, delayNN, delay_apply, if_neg h0,
    min_top_right]

/-- For `t ≠ 0`, `tokenBucketNN r b t = ↑(r * t + b)` (single coercion). -/
theorem tokenBucketNN_coe_of_ne (r b : ℝ≥0) {t : ℝ≥0}
    (hne : t ≠ 0) :
    tokenBucketNN r b t = ((r * t + b : ℝ≥0):ℝ≥0∞) :=
  (tokenBucketNN_apply_pos r b t hne).trans (by push_cast; ring)

/-- The min of two token-buckets is subadditive. -/
theorem tokenBucketNN_inf_subadd (r b r' b' : ℝ≥0) :
    IsSubadditive
      (tokenBucketNN r b ⊓ tokenBucketNN r' b') := by
  refine IsSubadditive.of_ne_zero ?_ fun u s hu hs => ?_
  · rw [Pi.inf_apply, tokenBucketNN_zero_eq,
      tokenBucketNN_zero_eq, min_self]
  · simp only [Pi.inf_apply]
    have hus : (u + s) ≠ 0 := by
      rw [← pos_iff_ne_zero] at hu ⊢; positivity
    rw [tokenBucketNN_coe_of_ne r b hu,
        tokenBucketNN_coe_of_ne r' b' hu,
        tokenBucketNN_coe_of_ne r b hs,
        tokenBucketNN_coe_of_ne r' b' hs,
        tokenBucketNN_coe_of_ne r b hus,
        tokenBucketNN_coe_of_ne r' b' hus]
    exact affine_min_subadd r b r' b' u s

/-- Token-bucket convolution equals their pointwise min. -/
theorem conv_tokenBucketNN_tokenBucketNN (r b r' b' : ℝ≥0) :
    minConv (tokenBucketNN r b) (tokenBucketNN r' b')
      = tokenBucketNN r b ⊓ tokenBucketNN r' b' :=
  minConv_eq_inf_of_subadditive _ _
    (tokenBucketNN_zero_eq r b) (tokenBucketNN_zero_eq r' b')
    (tokenBucketNN_inf_subadd r b r' b')

/-- Affine curve `t ↦ r * t + b` (no clamp at `0`). -/
noncomputable def affine (r b : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => (r:ℝ≥0∞) * t + b

/-- `affine r b t = ↑(r * t + b)` (single coercion). -/
theorem affine_coe (r b t : ℝ≥0) :
    affine r b t = ((r * t + b : ℝ≥0):ℝ≥0∞) := by
  simp only [affine]; push_cast; ring

/-- `affine r b ⊓ delayNN 0 = tokenBucketNN r b`. -/
theorem affine_inf_delay0 (r b : ℝ≥0) :
    affine r b ⊓ delayNN 0 = tokenBucketNN r b := by
  rw [tokenBucketNN_eq]; rfl

/-- `affine r 0 = rateNN r`. -/
theorem affine_zero (r : ℝ≥0) : affine r 0 = rateNN r := by
  funext t
  simp only [affine, rateNN_apply, ENNReal.coe_zero, add_zero]

/-- `affine r b 0 = b`. -/
theorem affine_zero_eq (r b : ℝ≥0) : affine r b 0 = (b:ℝ≥0∞) := by
  simp only [affine, ENNReal.coe_zero, mul_zero, zero_add]

/-- `rateLatencyNN R 0 = rateNN R`. -/
theorem rateLatencyNN_zero (R : ℝ≥0) :
    rateLatencyNN R 0 = rateNN R := by
  funext t; simp only [rateLatencyNN, rateNN_apply, tsub_zero]

/-- `tokenBucketNN R 0 = rateNN R`. -/
theorem tokenBucketNN_zero_rateNN (R : ℝ≥0) :
    tokenBucketNN R 0 = rateNN R := by
  funext t
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; rw [tokenBucketNN_zero_eq]; simp
  · rw [tokenBucketNN_apply_pos R 0 t ht]; simp

/-- `tokenBucketNN r b` is monotone. -/
theorem tokenBucketNN_mono (r b : ℝ≥0) :
    Monotone (tokenBucketNN r b) := by
  intro a c hac
  simp only [tokenBucketNN_apply]
  exact min_le_min (by gcongr) (delayNN_mono 0 hac)

/-- `delayNN d ⊘ delayNN d' = delayNN (d - d')` when `d' ≤ d`. -/
theorem minDeconv_delayNN_delayNN (d d' : ℝ≥0) (h : d' ≤ d) :
    minDeconv (delayNN d) (delayNN d') = delayNN (d - d') := by
  rw [minDeconv_delayNN (delayNN d) (delayNN_mono d) d']
  funext t
  show (if t + d' ≤ d then (0:ℝ≥0∞) else ⊤)
      = delayNN (d - d') t
  simp only [delayNN, delay_apply]; congr 1; rw [le_tsub_iff_right h]

/-- `rateNN R ⊘ delayNN d = affine R (R * d)`. -/
theorem minDeconv_rateNN_delayNN (R d : ℝ≥0) :
    minDeconv (rateNN R) (delayNN d) = affine R (R * d) := by
  rw [minDeconv_delayNN (rateNN R) (rateNN_mono R) d]
  funext t; simp only [rateNN_apply, affine]; push_cast; ring

/-- `tokenBucketNN r b ⊘ delayNN d = affine r (b + r * d)` for `d > 0`. -/
theorem minDeconv_tokenBucketNN_delay (r b d : ℝ≥0)
    (hd : 0 < d) :
    minDeconv (tokenBucketNN r b) (delayNN d)
      = affine r (b + r * d) := by
  rw [minDeconv_delayNN (tokenBucketNN r b)
    (tokenBucketNN_mono r b) d]
  funext t
  have htd : t + d ≠ 0 := by positivity
  rw [tokenBucketNN_apply_pos r b (t + d) htd]
  simp only [affine]; push_cast; ring

/-- Affine shift bound against a rate-latency term (`r ≤ R`). -/
theorem affine_shift_bound (r b R T t u : ℝ≥0)
    (h : r ≤ R) :
    affine r b (t + u)
      ≤ affine r (b + r*T) t + rateLatencyNN R T u := by
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
  rw [affine_coe, affine_coe, rateLatencyNN_coe]
  exact_mod_cast key

/-- `tokenBucketNN r b ≤ affine r b` pointwise. -/
theorem tokenBucketNN_le_affine (r b t : ℝ≥0) :
    tokenBucketNN r b t ≤ affine r b t := by
  simp only [tokenBucketNN_apply, affine]
  exact min_le_left _ _

/-- `tokenBucketNN r b ⊘ βRT = affine r (b + r*T)` for `r ≤ R`, `T > 0`. -/
theorem minDeconv_tokenBucketNN_rateLatencyNN
    (r b R T : ℝ≥0) (h : r ≤ R) (hT : 0 < T) :
    minDeconv (tokenBucketNN r b) (rateLatencyNN R T)
      = affine r (b + r*T) := by
  funext t
  apply le_antisymm
  · unfold minDeconv
    refine iSup_le (fun u => ?_)
    refine le_trans (tsub_le_iff_right.mpr ?_) le_rfl
    exact le_trans (tokenBucketNN_le_affine r b (t+u))
      (affine_shift_bound r b R T t u h)
  · unfold minDeconv
    refine le_iSup_of_le T ?_
    have htT : t + T ≠ 0 := by positivity
    rw [tokenBucketNN_apply_pos r b (t+T) htT]
    have hbeta : rateLatencyNN R T T = 0 := by
      simp only [rateLatencyNN, tsub_self]; simp
    rw [hbeta, tsub_zero]
    simp only [affine]; push_cast; ring_nf; rfl

/-- Lower bound on a single deconvolution term when `R ≤ r`. -/
theorem minDeconv_term_lb (r b R T t u : ℝ≥0)
    (hRr : R ≤ r) (hu : T ≤ u) (htu : t + u ≠ 0) :
    ((((r-R)*(u-T) : ℝ≥0)):ℝ≥0∞)
      ≤ tokenBucketNN r b (t+u) - rateLatencyNN R T u := by
  rw [tokenBucketNN_apply_pos r b (t+u) htu, rateLatencyNN_coe]
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

/-- `tokenBucketNN r b ⊘ βRT = ⊤` when `R < r` (unstable). -/
theorem minDeconv_tokenBucketNN_rateLatencyNN_top
    (r b R T : ℝ≥0) (hRr : R < r) :
    minDeconv (tokenBucketNN r b) (rateLatencyNN R T)
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

/-- The deconvolution `sup` against `rateNN R` is at least `b` (`r ≤ R`). -/
theorem minDeconv_origin_lb (r b R : ℝ≥0) (h : r ≤ R) :
    (b:ℝ≥0∞)
      ≤ ⨆ s : ℝ≥0, tokenBucketNN r b s - rateNN R s := by
  rw [le_iSup_iff]
  intro c hc
  by_contra hbc
  rw [not_le] at hbc
  lift c to ℝ≥0 using hbc.ne_top with c'
  rw [ENNReal.coe_lt_coe] at hbc
  rcases eq_or_lt_of_le h with hRr | hRr
  · subst hRr
    have h1 := hc 1
    rw [tokenBucketNN_apply_pos r b 1 one_ne_zero,
      rateNN_apply] at h1
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
    rw [tokenBucketNN_coe_of_ne r b hsne, rateNN_apply,
      ← ENNReal.coe_mul, ← ENNReal.coe_sub,
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

/-- Affine shift bound against a `rateNN R` term (`r ≤ R`). -/
theorem affine_shift_bound0 (r b R t u : ℝ≥0)
    (h : r ≤ R) :
    affine r b (t + u) ≤ affine r b t + rateNN R u := by
  have key : (r*(t+u)+b : ℝ≥0) ≤ (r*t+b) + R*u := by
    rw [← NNReal.coe_le_coe]; push_cast
    nlinarith [mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.mpr h) u.coe_nonneg]
  rw [affine_coe, affine_coe, rateNN_apply]
  exact_mod_cast key

/-- `tokenBucketNN r b ⊘ rateNN R = affine r b` when `r ≤ R`. -/
theorem minDeconv_tokenBucketNN_rateNN (r b R : ℝ≥0)
    (h : r ≤ R) :
    minDeconv (tokenBucketNN r b) (rateNN R) = affine r b := by
  funext t
  apply le_antisymm
  · unfold minDeconv
    refine iSup_le (fun u => ?_)
    refine le_trans (tsub_le_iff_right.mpr ?_) le_rfl
    exact le_trans (tokenBucketNN_le_affine r b (t+u))
      (affine_shift_bound0 r b R t u h)
  · rcases eq_or_ne t 0 with ht | ht
    · subst ht
      rw [affine_zero_eq]
      unfold minDeconv; simp only [zero_add]
      exact minDeconv_origin_lb r b R h
    · unfold minDeconv; refine le_iSup_of_le 0 ?_
      rw [add_zero, tokenBucketNN_apply_pos r b t ht]
      simp only [rateNN_apply, ENNReal.coe_zero, mul_zero,
        tsub_zero, affine, le_refl]

/-- `tokenBucketNN r b ⊘ rateNN R = ⊤` when `R < r` (unstable). -/
theorem minDeconv_tokenBucketNN_rateNN_top (r b R : ℝ≥0)
    (hRr : R < r) :
    minDeconv (tokenBucketNN r b) (rateNN R)
      = fun _ => (⊤:ℝ≥0∞) := by
  rw [← rateLatencyNN_zero R]
  exact minDeconv_tokenBucketNN_rateLatencyNN_top r b R 0 hRr

/-- `rateNN R ⊘ rateNN R' = rateNN R` when `R ≤ R'`. -/
theorem minDeconv_rateNN_rateNN (R R' : ℝ≥0) (h : R ≤ R') :
    minDeconv (rateNN R) (rateNN R') = rateNN R := by
  conv_lhs => rw [← tokenBucketNN_zero_rateNN R]
  rw [minDeconv_tokenBucketNN_rateNN R 0 R' h, affine_zero]

/-- `rateNN R ⊘ rateNN R' = ⊤` when `R' < R` (unstable). -/
theorem minDeconv_rateNN_rateNN_top (R R' : ℝ≥0) (h : R' < R) :
    minDeconv (rateNN R) (rateNN R')
      = fun _ => (⊤:ℝ≥0∞) := by
  conv_lhs => rw [← tokenBucketNN_zero_rateNN R]
  exact minDeconv_tokenBucketNN_rateNN_top R 0 R' h

/-- The jitter window collapses to a single shift:
`(α ∗ δ_a) ⊘ δ_b = α ⊘ δ_(b − a)` for monotone `α` and `a ≤ b` — the
output of a jitter with per-bit delays in `[a, b]` is constrained by the
input curve deconvolved by the jitter `b − a`. -/
theorem minDeconv_conv_delayNN_delayNN {α : ℝ≥0 → ℝ≥0∞}
    (hmono : Monotone α) {a b : ℝ≥0} (hab : a ≤ b) :
    minDeconv (minConv α (delayNN a)) (delayNN b)
      = minDeconv α (delayNN (b - a)) := by
  rw [conv_delayNN α hmono a,
    minDeconv_delayNN _ (fun u v huv => hmono (tsub_le_tsub_right huv a)) b,
    minDeconv_delayNN α hmono (b - a)]
  funext t
  congr 1
  rw [add_tsub_assoc_of_le hab]

end DeepWiki
