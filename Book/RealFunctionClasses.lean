import Book.Additivity
import Book.Continuity
import Book.Closures

/-! Concrete real curves over `ℝ≥0 → ℝ≥0∞`: delay, rate, rate-latency,
token-bucket, staircase, test. Their regularity (piecewise/left-continuity),
(super/sub)additivity, closures, convolutions, deconvolutions, and horizontal/
vertical deviations. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

/-- Pure-delay curve: `0` for `t ≤ d`, `⊤` afterwards. -/
noncomputable def delay (d : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => if t ≤ d then 0 else ⊤

/-- Constant-rate curve `t ↦ R * t`. -/
noncomputable def rate (R : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => (R : ℝ≥0∞) * (t : ℝ≥0∞)

/-- Rate-latency curve `t ↦ R * (t - T)₊`. -/
noncomputable def rateLatency (R T : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => (R : ℝ≥0∞) * ((t - T : ℝ≥0) : ℝ≥0∞)

/-- Token-bucket curve `(r * t + b) ⊓ delay 0` (`0` at `t = 0`). -/
noncomputable def tokenBucket (r b : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  (fun t => (r : ℝ≥0∞) * t + b) ⊓ delay 0

/-- Staircase curve of step `P`, height `h`, offset `J`, clamped at `0`. -/
noncomputable def staircase (P h : ℝ≥0) (J : ℝ) :
    ℝ≥0 → ℝ≥0∞ :=
  fun t =>
    min (ENNReal.ofReal
      (max (h * ⌈((t : ℝ) + J) / P⌉) 0)) (delay 0 t)

/-- Test/step curve: `0` for `t ≤ T`, `1` afterwards. -/
noncomputable def test (T : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => if t ≤ T then 0 else 1

/-- `delay d 0 = 0`. -/
theorem delay_zero_eq (d : ℝ≥0) : delay d 0 = 0 := by
  simp [delay]

/-- `rate R 0 = 0`. -/
theorem rate_zero_eq (R : ℝ≥0) : rate R 0 = 0 := by
  simp [rate]

/-- `rateLatency R T 0 = 0`. -/
theorem rateLatency_zero_eq (R T : ℝ≥0) :
    rateLatency R T 0 = 0 := by
  simp [rateLatency]

/-- `tokenBucket r b 0 = 0`. -/
theorem tokenBucket_zero_eq (r b : ℝ≥0) :
    tokenBucket r b 0 = 0 := by
  simp [tokenBucket, delay]

/-- `staircase P h J 0 = 0`. -/
theorem staircase_zero_eq (P h : ℝ≥0) (J : ℝ) :
    staircase P h J 0 = 0 := by
  simp [staircase, delay]

/-- `test T 0 = 0`. -/
theorem test_zero_eq (T : ℝ≥0) : test T 0 = 0 := by
  simp [test]

/-- `rate R` is continuous. -/
theorem rate_continuous (R : ℝ≥0) : Continuous (rate R) :=
  (ENNReal.continuous_const_mul (by simp)).comp
    (by fun_prop)

/-- `rateLatency R T` is continuous. -/
theorem rateLatency_continuous (R T : ℝ≥0) :
    Continuous (rateLatency R T) :=
  (ENNReal.continuous_const_mul (by simp)).comp
    (by fun_prop)

/-- `rate R` is piecewise continuous. -/
theorem rate_pwc (R : ℝ≥0) :
    IsPiecewiseContinuous (rate R) :=
  isPiecewiseContinuous_of_continuous _ (rate_continuous R)

/-- `rateLatency R T` is piecewise continuous. -/
theorem rateLatency_pwc (R T : ℝ≥0) :
    IsPiecewiseContinuous (rateLatency R T) :=
  isPiecewiseContinuous_of_continuous _
    (rateLatency_continuous R T)

/-- `delay d` is continuous at every `t ≠ d`. -/
theorem delay_continuousAt (d t : ℝ≥0) (h : t ≠ d) :
    ContinuousAt (delay d) t := by
  rcases lt_or_gt_of_ne h with h | h
  · refine (continuousAt_const (y := (0:ℝ≥0∞))).congr ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    simp [delay, le_of_lt (Set.mem_Iio.mp hs)]
  · refine (continuousAt_const (y := (⊤:ℝ≥0∞))).congr ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    simp [delay, not_le.mpr (Set.mem_Ioi.mp hs)]

/-- `delay d` is piecewise continuous (one jump at `d`). -/
theorem delay_pwc (d : ℝ≥0) :
    IsPiecewiseContinuous (delay d) := by
  intro T
  apply Set.Finite.subset (Set.finite_singleton d)
  rintro t ⟨ht, _⟩
  by_contra hne
  exact ht (delay_continuousAt d t hne)

/-- `test T` is continuous at every `t ≠ T`. -/
theorem test_continuousAt (T t : ℝ≥0) (h : t ≠ T) :
    ContinuousAt (test T) t := by
  rcases lt_or_gt_of_ne h with h | h
  · refine (continuousAt_const (y := (0:ℝ≥0∞))).congr ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    simp [test, le_of_lt (Set.mem_Iio.mp hs)]
  · refine (continuousAt_const (y := (1:ℝ≥0∞))).congr ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    simp [test, not_le.mpr (Set.mem_Ioi.mp hs)]

/-- `test T` is piecewise continuous (one jump at `T`). -/
theorem test_pwc (T : ℝ≥0) :
    IsPiecewiseContinuous (test T) := by
  intro S
  apply Set.Finite.subset (Set.finite_singleton T)
  rintro t ⟨ht, _⟩
  by_contra hne
  exact ht (test_continuousAt T t hne)

/-- `tokenBucket r b` is continuous at every `t ≠ 0`. -/
theorem tokenBucket_continuousAt (r b t : ℝ≥0)
    (h : t ≠ 0) : ContinuousAt (tokenBucket r b) t := by
  refine Filter.Tendsto.min ?_ (delay_continuousAt 0 t h)
  have h1 : ContinuousAt
      (fun s : ℝ≥0 => (r:ℝ≥0∞) * s) t :=
    (ENNReal.continuous_const_mul
      (by simp)).continuousAt.comp (by fun_prop)
  exact h1.add continuousAt_const

/-- `tokenBucket r b` is piecewise continuous (one jump at `0`). -/
theorem tokenBucket_pwc (r b : ℝ≥0) :
    IsPiecewiseContinuous (tokenBucket r b) := by
  intro T
  apply Set.Finite.subset (Set.finite_singleton 0)
  rintro t ⟨ht, _⟩
  by_contra hne
  exact ht (tokenBucket_continuousAt r b t hne)

/-- `⌈·⌉` is locally constant at non-integer points. -/
theorem ceil_eventuallyEq (x : ℝ) (hx : (⌈x⌉ : ℝ) ≠ x) :
    ∀ᶠ y in 𝓝 x, ⌈y⌉ = ⌈x⌉ := by
  have hhi : x < (⌈x⌉ : ℝ) :=
    lt_of_le_of_ne (Int.le_ceil x) (fun h => hx h.symm)
  have hlo : (⌈x⌉ : ℝ) - 1 < x := by
    have := Int.ceil_lt_add_one x; linarith
  filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
  rw [Int.ceil_eq_iff]
  exact ⟨by linarith [hy.1], le_of_lt hy.2⟩

/-- The step-count `⌈(s+J)/P⌉` is continuous off the jump points. -/
theorem stepCount_continuousAt (P : ℝ≥0) (J : ℝ)
    (t : ℝ≥0)
    (ht : (⌈((t:ℝ)+J)/P⌉ : ℝ) ≠ ((t:ℝ)+J)/P) :
    ContinuousAt
      (fun s : ℝ≥0 => (⌈((s:ℝ)+J)/P⌉ : ℝ)) t := by
  have hcomp : ContinuousAt
      (fun s : ℝ≥0 => ((s:ℝ)+J)/P) t := by fun_prop
  refine (continuousAt_const
    (y := (⌈((t:ℝ)+J)/P⌉:ℝ))).congr ?_
  have := hcomp.tendsto.eventually (ceil_eventuallyEq _ ht)
  filter_upwards [this] with s hs
  rw [hs]

/-- The staircase's jump set on `[0, T]` is finite. -/
theorem jumpset_finite (P : ℝ≥0) (J : ℝ)
    (hP : (0:ℝ) < P) (T : ℝ≥0) :
    {t : ℝ≥0 |
        (⌈((t:ℝ)+J)/P⌉ : ℝ) = ((t:ℝ)+J)/P
          ∧ t ≤ T}.Finite := by
  apply Set.Finite.of_finite_image
    (f := fun t : ℝ≥0 => ⌈((t:ℝ)+J)/P⌉)
  · apply Set.Finite.subset
      (Set.finite_Icc ⌈J/P⌉ ⌈((T:ℝ)+J)/P⌉)
    rintro n ⟨t, ⟨_, htT⟩, rfl⟩
    rw [Set.mem_Icc]
    have htT' : (t:ℝ) ≤ T := by exact_mod_cast htT
    refine ⟨Int.ceil_mono
        ((div_le_div_iff_of_pos_right hP).2 ?_),
      Int.ceil_mono
        ((div_le_div_iff_of_pos_right hP).2 ?_)⟩
    · linarith [t.coe_nonneg]
    · linarith
  · rintro a ⟨ha1, _⟩ b ⟨hb1, _⟩ hab
    have hcast : ((⌈((a:ℝ)+J)/P⌉ : ℤ):ℝ)
        = ((⌈((b:ℝ)+J)/P⌉ : ℤ):ℝ) := by
      exact_mod_cast hab
    have heq : ((a:ℝ)+J)/P = ((b:ℝ)+J)/P := by
      rw [← ha1, ← hb1, hcast]
    have hPne : (P:ℝ) ≠ 0 := ne_of_gt hP
    field_simp at heq
    have : (a:ℝ) = b := by linarith
    exact_mod_cast this

/-- `staircase P h J` is continuous off `0` and the jump points. -/
theorem staircase_continuousAt (P h : ℝ≥0) (J : ℝ)
    (t : ℝ≥0) (h0 : t ≠ 0)
    (ht : (⌈((t:ℝ)+J)/P⌉ : ℝ) ≠ ((t:ℝ)+J)/P) :
    ContinuousAt (staircase P h J) t := by
  refine Filter.Tendsto.min ?_ (delay_continuousAt 0 t h0)
  apply ENNReal.continuous_ofReal.continuousAt.comp
  exact Filter.Tendsto.max
    ((stepCount_continuousAt P J t ht).const_mul (h:ℝ))
    continuousAt_const

/-- `staircase P h J` is piecewise continuous. -/
theorem staircase_pwc (P h : ℝ≥0) (J : ℝ)
    (hP : (0:ℝ) < P) :
    IsPiecewiseContinuous (staircase P h J) := by
  intro T
  apply Set.Finite.subset
    (((jumpset_finite P J hP T).union
      (Set.finite_singleton 0)))
  rintro t ⟨ht, htT⟩
  by_contra hmem
  rw [Set.mem_union] at hmem
  push Not at hmem
  obtain ⟨hjump, h0⟩ := hmem
  apply ht
  refine staircase_continuousAt P h J t ?_ ?_
  · simpa using h0
  · intro hcontra
    exact hjump ⟨hcontra, htT.2⟩

/-- `rate R` is left-continuous. -/
theorem rate_leftCont (R : ℝ≥0) :
    IsLeftContinuous (rate R) :=
  leftCont_of_continuous _ (rate_continuous R)

/-- `rateLatency R T` is left-continuous. -/
theorem rateLatency_leftCont (R T : ℝ≥0) :
    IsLeftContinuous (rateLatency R T) :=
  leftCont_of_continuous _ (rateLatency_continuous R T)

/-- `delay d` is left-continuous. -/
theorem delay_leftCont (d : ℝ≥0) :
    IsLeftContinuous (delay d) := by
  intro t
  rcases le_or_gt t d with h | h
  · refine ContinuousWithinAt.congr
      (f := fun _ => (0:ℝ≥0∞)) continuousWithinAt_const
      (fun s hs => ?_) ?_
    · simp only [delay,
        if_pos (le_of_lt (lt_of_lt_of_le hs h))]
    · simp [delay, h]
  · have hev : (delay d) =ᶠ[𝓝[Iio t] t]
        (fun _ => (⊤:ℝ≥0∞)) := by
      filter_upwards [Ioo_mem_nhdsLT h] with s hs
      simp [delay, not_le.mpr hs.1]
    exact continuousWithinAt_const.congr_of_eventuallyEq
      hev (by simp [delay, not_le.mpr h])

/-- `test T` is left-continuous. -/
theorem test_leftCont (T : ℝ≥0) :
    IsLeftContinuous (test T) := by
  intro t
  rcases le_or_gt t T with h | h
  · refine ContinuousWithinAt.congr
      (f := fun _ => (0:ℝ≥0∞)) continuousWithinAt_const
      (fun s hs => ?_) ?_
    · simp only [test,
        if_pos (le_of_lt (lt_of_lt_of_le hs h))]
    · simp [test, h]
  · have hev : (test T) =ᶠ[𝓝[Iio t] t]
        (fun _ => (1:ℝ≥0∞)) := by
      filter_upwards [Ioo_mem_nhdsLT h] with s hs
      simp [test, not_le.mpr hs.1]
    exact continuousWithinAt_const.congr_of_eventuallyEq
      hev (by simp [test, not_le.mpr h])

/-- `tokenBucket r b` is left-continuous. -/
theorem tokenBucket_leftCont (r b : ℝ≥0) :
    IsLeftContinuous (tokenBucket r b) := by
  intro t
  refine Filter.Tendsto.min ?_ (delay_leftCont 0 t)
  have h1 : ContinuousWithinAt
      (fun s : ℝ≥0 => (r:ℝ≥0∞) * s) (Iio t) t :=
    ((ENNReal.continuous_const_mul
      (by simp)).comp (by fun_prop)).continuousWithinAt
  exact h1.add continuousWithinAt_const

/-- The step-count is eventually constant on a left neighborhood. -/
theorem stepCount_eventuallyEq_left (P : ℝ≥0)
    (hP : (0:ℝ) < P) (J : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᶠ s in (𝓝[Iio t] t : Filter ℝ≥0),
      (fun u : ℝ≥0 =>
        ⌈((u:ℝ)+J)/P⌉ = ⌈((t:ℝ)+J)/P⌉) s := by
  set n := ⌈((t:ℝ)+J)/P⌉ with hn
  have hPne : (P:ℝ) ≠ 0 := ne_of_gt hP
  have hLlt : ((n:ℝ)-1)*P - J < (t:ℝ) := by
    have h1 : ((t:ℝ)+J)/P > (n:ℝ) - 1 := by
      have := Int.ceil_lt_add_one (((t:ℝ)+J)/P)
      rw [← hn] at this; linarith
    rw [gt_iff_lt, lt_div_iff₀ hP] at h1; nlinarith
  set L : ℝ≥0 := (((n:ℝ)-1)*P - J).toNNReal with hL
  have hLco : (L:ℝ) = max (((n:ℝ)-1)*P - J) 0 := by
    rw [hL, Real.coe_toNNReal']
  have hLt : L < t := by
    rw [← NNReal.coe_lt_coe, hLco]
    exact max_lt hLlt (by exact_mod_cast ht)
  filter_upwards [Ioo_mem_nhdsLT hLt] with s hs
  have hLs : (L:ℝ) < (s:ℝ) := by exact_mod_cast hs.1
  have hsR : (s:ℝ) ≤ (t:ℝ) :=
    le_of_lt (by exact_mod_cast hs.2)
  have hsL : ((n:ℝ)-1)*P - J < (s:ℝ) := by
    have : ((n:ℝ)-1)*P - J ≤ (L:ℝ) := by
      rw [hLco]; exact le_max_left _ _
    linarith
  show ⌈((s:ℝ)+J)/P⌉ = n
  rw [Int.ceil_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hP]; nlinarith
  · rw [div_le_iff₀ hP]
    have hn_le : ((t:ℝ)+J)/P ≤ (n:ℝ) := by
      rw [hn]; exact Int.le_ceil _
    rw [div_le_iff₀ hP] at hn_le; nlinarith

/-- The unclamped staircase value is left-continuous. -/
theorem staircase_val_leftCont (P h : ℝ≥0)
    (hP : (0:ℝ) < P) (J : ℝ) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => ENNReal.ofReal
        (max ((h:ℝ) * (⌈((s:ℝ)+J)/P⌉:ℝ)) 0)) (Iio t) t := by
  rcases eq_zero_or_pos t with h0 | ht
  · subst h0
    have : 𝓝[Iio (0:ℝ≥0)] 0 = ⊥ := by
      rw [show Iio (0:ℝ≥0) = ∅ by simp, nhdsWithin_empty]
    unfold ContinuousWithinAt; rw [this]; exact tendsto_bot
  · refine continuousWithinAt_const.congr_of_eventuallyEq
      ?_ rfl
    filter_upwards
      [stepCount_eventuallyEq_left P hP J t ht] with s hs
    show ENNReal.ofReal
        (max ((h:ℝ)*(⌈((s:ℝ)+J)/P⌉:ℝ)) 0)
      = ENNReal.ofReal
        (max ((h:ℝ)*(⌈((t:ℝ)+J)/P⌉:ℝ)) 0)
    rw [hs]

/-- `staircase P h J` is left-continuous. -/
theorem staircase_leftCont (P h : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ) : IsLeftContinuous (staircase P h J) := by
  intro t
  exact Filter.Tendsto.min
    (staircase_val_leftCont P h hP J t) (delay_leftCont 0 t)

/-- `rate R = rateLatency R 0`. -/
theorem rate_eq_rateLatency_zero (R : ℝ≥0) :
    rate R = rateLatency R 0 := by
  funext t; simp [rate, rateLatency]

/-- `rate R = tokenBucket R 0`. -/
theorem rate_eq_tokenBucket_zero (R : ℝ≥0) :
    rate R = tokenBucket R 0 := by
  funext t
  simp only [rate, tokenBucket, Pi.inf_apply,
    ENNReal.coe_zero, add_zero]
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [delay]
  · have ht : ¬ t ≤ 0 := by simpa using h
    simp [delay, ht]

/-- `test 0 = tokenBucket 0 1`. -/
theorem test_zero_eq_tokenBucket :
    test (0 : ℝ≥0) = tokenBucket 0 1 := by
  funext t
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [test, tokenBucket, delay]
  · have ht : ¬ t ≤ 0 := by simpa using h
    simp [test, tokenBucket, delay, ht]

/-- `rate R` is subadditive. -/
theorem rate_subadditive (R : ℝ≥0) :
    IsSubadditive (rate R) := by
  intro u s; simp only [rate]; push_cast; rw [mul_add]

/-- `rate R` is superadditive (hence additive). -/
theorem rate_superadditive (R : ℝ≥0) :
    IsSuperadditive (rate R) := by
  intro u s; simp only [rate]; push_cast; rw [mul_add]

/-- `delay d` is superadditive. -/
theorem delay_superadditive (d : ℝ≥0) :
    IsSuperadditive (delay d) := by
  intro u s
  simp only [delay]
  rcases le_or_gt (u + s) d with h | h
  · rw [if_pos h, if_pos (le_trans le_self_add h),
      if_pos (le_trans le_add_self h)]; simp
  · rw [if_neg (not_le.mpr h)]; exact le_top

/-- Truncated subtraction is superadditive: `(u-T)+(s-T) ≤ (u+s)-T`. -/
theorem tsub_add_tsub_le_tsub (u s T : ℝ≥0) :
    (u - T) + (s - T) ≤ (u + s) - T := by
  rcases le_or_gt u T with hu | hu
  · rw [tsub_eq_zero_of_le hu, zero_add]
    exact tsub_le_tsub_right le_add_self T
  · rcases le_or_gt s T with hs | hs
    · rw [tsub_eq_zero_of_le hs, add_zero]
      exact tsub_le_tsub_right le_self_add T
    · rw [tsub_add_tsub_comm (le_of_lt hu) (le_of_lt hs)]
      exact tsub_le_tsub_left le_add_self _

/-- `rateLatency R T` is superadditive. -/
theorem rateLatency_superadditive (R T : ℝ≥0) :
    IsSuperadditive (rateLatency R T) := by
  intro u s
  simp only [rateLatency]
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul,
    ← ENNReal.coe_mul, ← ENNReal.coe_add,
    ENNReal.coe_le_coe, ← mul_add]
  exact _root_.mul_le_mul_right (tsub_add_tsub_le_tsub u s T) R

/-- `tokenBucket r b` is subadditive. -/
theorem tokenBucket_subadditive (r b : ℝ≥0) :
    IsSubadditive (tokenBucket r b) := by
  intro u s
  rcases eq_or_ne u 0 with hu | hu
  · subst hu; rw [zero_add, tokenBucket_zero_eq, zero_add]
  · rcases eq_or_ne s 0 with hs | hs
    · subst hs
      rw [add_zero, tokenBucket_zero_eq, add_zero]
    · have hu0 : ¬ u ≤ 0 := by simpa using hu
      have hs0 : ¬ s ≤ 0 := by simpa using hs
      have hus0 : ¬ (u + s) ≤ 0 := by
        rw [nonpos_iff_eq_zero, add_eq_zero]
        rintro ⟨h1, _⟩; exact hu h1
      simp only [tokenBucket, Pi.inf_apply, delay,
        if_neg hu0, if_neg hs0, if_neg hus0, min_top_right]
      push_cast [mul_add]
      calc (r:ℝ≥0∞)*u + r*s + b
          ≤ (r*u + r*s + b) + b := le_self_add
        _ = (r*u + b) + (r*s + b) := by ring

/-- `test 0` is subadditive. -/
theorem test_zero_subadditive :
    IsSubadditive (test (0 : ℝ≥0)) := by
  rw [test_zero_eq_tokenBucket]
  exact tokenBucket_subadditive 0 1

/-- Subadditive step-count bound when `J ≥ 0`. -/
theorem staircase_ceil_sub (P : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ) (hJ : 0 ≤ J) (u s : ℝ≥0) :
    ⌈((u:ℝ)+(s:ℝ)+J)/P⌉
      ≤ ⌈((u:ℝ)+J)/P⌉ + ⌈((s:ℝ)+J)/P⌉ := by
  calc ⌈((u:ℝ)+(s:ℝ)+J)/P⌉
      ≤ ⌈((u:ℝ)+J)/P + ((s:ℝ)+J)/P⌉ := by
        apply Int.ceil_mono
        rw [← add_div, div_le_div_iff_of_pos_right hP]
        linarith
    _ ≤ ⌈((u:ℝ)+J)/P⌉ + ⌈((s:ℝ)+J)/P⌉ :=
        Int.ceil_add_le _ _

/-- Subadditive bound on the clamped staircase value (`J ≥ 0`). -/
theorem staircase_val_sub (P h : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ) (hJ : 0 ≤ J) (u s : ℝ≥0) :
    ENNReal.ofReal
        (max ((h:ℝ) * (⌈((u:ℝ)+(s:ℝ)+J)/P⌉:ℝ)) 0)
      ≤ ENNReal.ofReal
          (max ((h:ℝ)*(⌈((u:ℝ)+J)/P⌉:ℝ)) 0)
        + ENNReal.ofReal
          (max ((h:ℝ)*(⌈((s:ℝ)+J)/P⌉:ℝ)) 0) := by
  rw [← ENNReal.ofReal_add (le_max_right _ _)
    (le_max_right _ _)]
  apply ENNReal.ofReal_le_ofReal
  have hkey := staircase_ceil_sub P hP J hJ u s
  rcases le_or_gt ((h:ℝ) * (⌈((u:ℝ)+(s:ℝ)+J)/P⌉:ℝ)) 0
    with h0 | h0
  · rw [max_eq_right h0]
    exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  · rw [max_eq_left (le_of_lt h0)]
    calc (h:ℝ) * (⌈((u:ℝ)+(s:ℝ)+J)/P⌉:ℝ)
        ≤ (h:ℝ) * ((⌈((u:ℝ)+J)/P⌉:ℝ)
            + (⌈((s:ℝ)+J)/P⌉:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ h.coe_nonneg
          exact_mod_cast hkey
      _ = (h:ℝ)*(⌈((u:ℝ)+J)/P⌉:ℝ)
          + (h:ℝ)*(⌈((s:ℝ)+J)/P⌉:ℝ) := by ring
      _ ≤ max ((h:ℝ)*(⌈((u:ℝ)+J)/P⌉:ℝ)) 0
          + max ((h:ℝ)*(⌈((s:ℝ)+J)/P⌉:ℝ)) 0 :=
          add_le_add (le_max_left _ _) (le_max_left _ _)

/-- `staircase P h J` is subadditive when `J ≥ 0`. -/
theorem staircase_subadditive (P h : ℝ≥0)
    (hP : (0:ℝ) < P) (J : ℝ) (hJ : 0 ≤ J) :
    IsSubadditive (staircase P h J) := by
  intro u s
  rcases eq_or_ne u 0 with hu | hu
  · subst hu; rw [zero_add, staircase_zero_eq, zero_add]
  · rcases eq_or_ne s 0 with hs | hs
    · subst hs
      rw [add_zero, staircase_zero_eq, add_zero]
    · have hu0 : ¬ u ≤ 0 := by simpa using hu
      have hs0 : ¬ s ≤ 0 := by simpa using hs
      have hus0 : ¬ (u + s) ≤ 0 := by
        rw [nonpos_iff_eq_zero, add_eq_zero]
        rintro ⟨h1, _⟩; exact hu h1
      simp only [staircase, delay, if_neg hu0,
        if_neg hs0, if_neg hus0, min_top_right]
      push_cast
      exact staircase_val_sub P h hP J hJ u s

/-- `⌈x⌉ + ⌈y⌉ ≤ ⌈x+y⌉ + 1`. -/
theorem ceil_add_le_ceil_succ (x y : ℝ) :
    ⌈x⌉ + ⌈y⌉ ≤ ⌈x + y⌉ + 1 := by
  have hx := Int.ceil_lt_add_one x
  have hy := Int.ceil_lt_add_one y
  have hxy := Int.le_ceil (x + y)
  have hi : ⌈x⌉ + ⌈y⌉ < ⌈x+y⌉ + 2 := by
    have : (⌈x⌉:ℝ) + ⌈y⌉ < ⌈x+y⌉ + 2 := by linarith
    exact_mod_cast this
  omega

/-- Superadditive step-count bound when `J < -P`. -/
theorem staircase_ceil_super (P : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ) (hJ : J < -P) (u s : ℝ≥0) :
    ⌈((u:ℝ)+J)/P⌉ + ⌈((s:ℝ)+J)/P⌉
      ≤ ⌈((u:ℝ)+(s:ℝ)+J)/P⌉ := by
  have hPne : (P:ℝ) ≠ 0 := ne_of_gt hP
  have hab : ((u:ℝ)+J)/P + ((s:ℝ)+J)/P
      ≤ ((u:ℝ)+(s:ℝ)+J)/P - 1 := by
    rw [← add_div, le_sub_iff_add_le,
      div_add' _ _ _ hPne,
      div_le_div_iff_of_pos_right hP]
    nlinarith [hJ]
  have h1 := ceil_add_le_ceil_succ
    (((u:ℝ)+J)/P) (((s:ℝ)+J)/P)
  have h2 : ⌈((u:ℝ)+J)/P + ((s:ℝ)+J)/P⌉
      ≤ ⌈((u:ℝ)+(s:ℝ)+J)/P - 1⌉ := Int.ceil_mono hab
  have h3 : ⌈((u:ℝ)+(s:ℝ)+J)/P - 1⌉
      = ⌈((u:ℝ)+(s:ℝ)+J)/P⌉ - 1 := by
    rw [show ((u:ℝ)+(s:ℝ)+J)/P - 1
        = ((u:ℝ)+(s:ℝ)+J)/P + ((-1 : ℤ) : ℝ) by
      push_cast; ring, Int.ceil_add_intCast]; ring
  omega

/-- Superadditivity of `max (h·n) 0` clamps under `n+m ≤ k`. -/
theorem clamp_super (h : ℝ) (hh : 0 ≤ h) (n m k : ℤ)
    (hn : n ≤ k) (hm : m ≤ k) (hnm : n + m ≤ k) :
    max (h * n) 0 + max (h * m) 0 ≤ max (h * k) 0 := by
  rcases le_or_gt (h*(n:ℝ)) 0 with hN | hN
  · rw [max_eq_right hN, zero_add]
    rcases le_or_gt (h*(m:ℝ)) 0 with hM | hM
    · rw [max_eq_right hM]; exact le_max_right _ _
    · rw [max_eq_left (le_of_lt hM)]
      apply le_max_of_le_left
      have : (m:ℝ) ≤ k := by exact_mod_cast hm
      nlinarith [hh, this]
  · rcases le_or_gt (h*(m:ℝ)) 0 with hM | hM
    · rw [max_eq_left (le_of_lt hN), max_eq_right hM,
        add_zero]
      apply le_max_of_le_left
      have : (n:ℝ) ≤ k := by exact_mod_cast hn
      nlinarith [hh, this]
    · rw [max_eq_left (le_of_lt hN),
        max_eq_left (le_of_lt hM)]
      apply le_max_of_le_left
      have : (n:ℝ) + m ≤ k := by exact_mod_cast hnm
      nlinarith [hh, this]

/-- `staircase P h J` is superadditive when `J < -P`. -/
theorem staircase_superadditive (P h : ℝ≥0)
    (hP : (0:ℝ) < P) (J : ℝ) (hJ : J < -P) :
    IsSuperadditive (staircase P h J) := by
  intro u s
  rcases eq_or_ne u 0 with hu | hu
  · subst hu; rw [zero_add, staircase_zero_eq, zero_add]
  · rcases eq_or_ne s 0 with hs | hs
    · subst hs
      rw [add_zero, staircase_zero_eq, add_zero]
    · have hu0 : ¬ u ≤ 0 := by simpa using hu
      have hs0 : ¬ s ≤ 0 := by simpa using hs
      have hus0 : ¬ (u + s) ≤ 0 := by
        rw [nonpos_iff_eq_zero, add_eq_zero]
        rintro ⟨h1, _⟩; exact hu h1
      simp only [staircase, delay, if_neg hu0,
        if_neg hs0, if_neg hus0, min_top_right]
      rw [← ENNReal.ofReal_add (le_max_right _ _)
        (le_max_right _ _)]
      apply ENNReal.ofReal_le_ofReal
      have hnk : ⌈((u:ℝ)+J)/P⌉
          ≤ ⌈((u:ℝ)+(s:ℝ)+J)/P⌉ :=
        Int.ceil_mono ((div_le_div_iff_of_pos_right hP).2
          (by linarith [s.coe_nonneg]))
      have hmk : ⌈((s:ℝ)+J)/P⌉
          ≤ ⌈((u:ℝ)+(s:ℝ)+J)/P⌉ :=
        Int.ceil_mono ((div_le_div_iff_of_pos_right hP).2
          (by linarith [u.coe_nonneg]))
      exact clamp_super (h:ℝ) h.coe_nonneg _ _ _ hnk hmk
        (staircase_ceil_super P hP J hJ u s)

/-- The token-bucket is its own subadditive closure. -/
theorem tokenBucket_closure (r b : ℝ≥0) :
    subadditiveClosureE (tokenBucket r b)
      = tokenBucket r b :=
  subadditiveClosureE_eq_self _
    (tokenBucket_subadditive r b)
    (tokenBucket_zero_eq r b)

/-- The staircase (`J ≥ 0`) is its own subadditive closure. -/
theorem staircase_closure (P h : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ) (hJ : 0 ≤ J) :
    subadditiveClosureE (staircase P h J)
      = staircase P h J :=
  subadditiveClosureE_eq_self _
    (staircase_subadditive P h hP J hJ)
    (staircase_zero_eq P h J)

/-- Pointwise coercion `(ℝ≥0 → ℝ≥0∞) → (ℝ≥0 → WithBot ℝ≥0∞)`. -/
instance : Coe (ℝ≥0 → ℝ≥0∞) (ℝ≥0 → WithBot ℝ≥0∞) :=
  ⟨fun g t => ((g t : ℝ≥0∞) : WithBot ℝ≥0∞)⟩

/-- A superadditive `g` with `g 0 = 0` is its own superadditive closure. -/
theorem superadditiveClosure_coe_eq_self
    (g : ℝ≥0 → ℝ≥0∞)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0) :
    superadditiveClosure (↑g)
      = (↑g : ℝ≥0 → WithBot ℝ≥0∞) := by
  apply superadditiveClosure_eq_self
  · intro u s
    show ((g u : ℝ≥0∞) : WithBot ℝ≥0∞)
        + ((g s : ℝ≥0∞) : WithBot ℝ≥0∞)
      ≤ ((g (u + s) : ℝ≥0∞) : WithBot ℝ≥0∞)
    rw [← WithBot.coe_add]
    exact_mod_cast hsup u s
  · show ((g 0 : ℝ≥0∞) : WithBot ℝ≥0∞) = 0
    rw [h0]; rfl

/-- Superadditive-closure of `g` recovers `g` after `unbotD 0`. -/
theorem superadditiveClosure_unbotD_eq
    (g : ℝ≥0 → ℝ≥0∞)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0)
    (t : ℝ≥0) :
    (superadditiveClosure (↑g) t).unbotD 0 = g t := by
  rw [superadditiveClosure_coe_eq_self g hsup h0]
  show (((g t : ℝ≥0∞) : WithBot ℝ≥0∞)).unbotD 0 = g t
  rw [WithBot.unbotD_coe]

/-- `delay d` is fixed by its superadditive closure. -/
theorem delay_closure (d : ℝ≥0) (t : ℝ≥0) :
    (superadditiveClosure (↑(delay d)) t).unbotD 0
      = delay d t :=
  superadditiveClosure_unbotD_eq _
    (delay_superadditive d) (delay_zero_eq d) t

/-- `rate R` is fixed by its superadditive closure. -/
theorem rate_closure (R : ℝ≥0) (t : ℝ≥0) :
    (superadditiveClosure (↑(rate R)) t).unbotD 0
      = rate R t :=
  superadditiveClosure_unbotD_eq _
    (rate_superadditive R) (rate_zero_eq R) t

/-- `rateLatency R T` is fixed by its superadditive closure. -/
theorem rateLatency_closure (R T : ℝ≥0) (t : ℝ≥0) :
    (superadditiveClosure (↑(rateLatency R T)) t).unbotD 0
      = rateLatency R T t :=
  superadditiveClosure_unbotD_eq _
    (rateLatency_superadditive R T)
    (rateLatency_zero_eq R T) t

/-- The staircase (`J < -P`) is fixed by its superadditive closure. -/
theorem staircase_closure_super (P h : ℝ≥0)
    (hP : (0:ℝ) < P) (J : ℝ) (hJ : J < -P) (t : ℝ≥0) :
    (superadditiveClosure (↑(staircase P h J)) t).unbotD 0
      = staircase P h J t :=
  superadditiveClosure_unbotD_eq _
    (staircase_superadditive P h hP J hJ)
    (staircase_zero_eq P h J) t

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
  simp only [tokenBucket, Pi.inf_apply, delay, if_neg h0,
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

/-- `affine r b ⊓ delay 0 = tokenBucket r b`. -/
theorem affine_inf_delay0 (r b : ℝ≥0) :
    affine r b ⊓ delay 0 = tokenBucket r b := rfl

/-- `affine r 0 = rate r`. -/
theorem affine_zero (r : ℝ≥0) : affine r 0 = rate r := by
  funext t
  simp only [affine, rate, ENNReal.coe_zero, add_zero]

/-- `rateLatency R 0 = rate R`. -/
theorem rateLatency_zero (R : ℝ≥0) :
    rateLatency R 0 = rate R := by
  funext t; simp only [rateLatency, rate, tsub_zero]

/-- `tokenBucket R 0 = rate R`. -/
theorem tokenBucket_zero_rate (R : ℝ≥0) :
    tokenBucket R 0 = rate R := by
  funext t
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; rw [tokenBucket_zero_eq]; simp [rate]
  · rw [tokenBucket_apply_pos R 0 t ht]; simp [rate]

/-- `tokenBucket r b` is monotone. -/
theorem tokenBucket_mono (r b : ℝ≥0) :
    Monotone (tokenBucket r b) := by
  intro a c hac
  simp only [tokenBucket, Pi.inf_apply]
  exact min_le_min (by gcongr) (delay_mono 0 hac)

/-- `delay d ⊘ delay d' = delay (d - d')` when `d' ≤ d`. -/
theorem deconv_delay_delay (d d' : ℝ≥0) (h : d' ≤ d) :
    deconv (delay d) (delay d') = delay (d - d') := by
  rw [deconv_delay (delay d) (delay_mono d) d']
  funext t
  show (if t + d' ≤ d then (0:ℝ≥0∞) else ⊤)
      = delay (d - d') t
  simp only [delay]; congr 1; rw [le_tsub_iff_right h]

/-- `rate R ⊘ delay d = affine R (R * d)`. -/
theorem deconv_rate_delay (R d : ℝ≥0) :
    deconv (rate R) (delay d) = affine R (R * d) := by
  rw [deconv_delay (rate R) (rate_mono R) d]
  funext t; simp only [rate, affine]; push_cast; ring

/-- `tokenBucket r b ⊘ delay d = affine r (b + r * d)` for `d > 0`. -/
theorem deconv_tokenBucket_delay (r b d : ℝ≥0)
    (hd : 0 < d) :
    deconv (tokenBucket r b) (delay d)
      = affine r (b + r * d) := by
  rw [deconv_delay (tokenBucket r b)
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
  simp only [tokenBucket, Pi.inf_apply, affine]
  exact min_le_left _ _

/-- `tokenBucket r b ⊘ βRT = affine r (b + r*T)` for `r ≤ R`, `T > 0`. -/
theorem deconv_tokenBucket_rateLatency
    (r b R T : ℝ≥0) (h : r ≤ R) (hT : 0 < T) :
    deconv (tokenBucket r b) (rateLatency R T)
      = affine r (b + r*T) := by
  funext t
  apply le_antisymm
  · unfold deconv
    refine iSup_le (fun u => ?_)
    refine le_trans (tsub_le_iff_right.mpr ?_) le_rfl
    exact le_trans (tokenBucket_le_affine r b (t+u))
      (affine_shift_bound r b R T t u h)
  · unfold deconv
    refine le_iSup_of_le T ?_
    have htT : t + T ≠ 0 := by positivity
    rw [tokenBucket_apply_pos r b (t+T) htT]
    have hbeta : rateLatency R T T = 0 := by
      simp only [rateLatency, tsub_self]; simp
    rw [hbeta, tsub_zero]
    simp only [affine]; push_cast; ring_nf; rfl

/-- Lower bound on a single deconvolution term when `R ≤ r`. -/
theorem deconv_term_lb (r b R T t u : ℝ≥0)
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
theorem deconv_tokenBucket_rateLatency_top
    (r b R T : ℝ≥0) (hRr : R < r) :
    deconv (tokenBucket r b) (rateLatency R T)
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
    have hlb := deconv_term_lb r b R T t (T + w)
      hRr.le hu htu
    refine le_trans ?_ hlb
    rw [ENNReal.coe_le_coe]
    have he : (T + w) - T = w := by simp
    rw [he]

/-- The deconvolution `sup` against `rate R` is at least `b` (`r ≤ R`). -/
theorem deconv_origin_lb (r b R : ℝ≥0) (h : r ≤ R) :
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
      rate] at h1
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
    rw [tokenBucket_apply_pos r b s hsne, rate] at hcs
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
  simp only [affine, rate]
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
theorem deconv_tokenBucket_rate (r b R : ℝ≥0)
    (h : r ≤ R) :
    deconv (tokenBucket r b) (rate R) = affine r b := by
  funext t
  apply le_antisymm
  · unfold deconv
    refine iSup_le (fun u => ?_)
    refine le_trans (tsub_le_iff_right.mpr ?_) le_rfl
    exact le_trans (tokenBucket_le_affine r b (t+u))
      (affine_shift_bound0 r b R t u h)
  · rcases eq_or_ne t 0 with ht | ht
    · subst ht
      simp only [affine, ENNReal.coe_zero, mul_zero,
        zero_add]
      unfold deconv; simp only [zero_add]
      exact deconv_origin_lb r b R h
    · unfold deconv; refine le_iSup_of_le 0 ?_
      rw [add_zero, tokenBucket_apply_pos r b t ht]
      simp only [rate, ENNReal.coe_zero, mul_zero,
        tsub_zero, affine, le_refl]

/-- `tokenBucket r b ⊘ rate R = ⊤` when `R < r` (unstable). -/
theorem deconv_tokenBucket_rate_top (r b R : ℝ≥0)
    (hRr : R < r) :
    deconv (tokenBucket r b) (rate R)
      = fun _ => (⊤:ℝ≥0∞) := by
  rw [← rateLatency_zero R]
  exact deconv_tokenBucket_rateLatency_top r b R 0 hRr

/-- `rate R ⊘ rate R' = rate R` when `R ≤ R'`. -/
theorem deconv_rate_rate (R R' : ℝ≥0) (h : R ≤ R') :
    deconv (rate R) (rate R') = rate R := by
  conv_lhs => rw [← tokenBucket_zero_rate R]
  rw [deconv_tokenBucket_rate R 0 R' h, affine_zero]

/-- `rate R ⊘ rate R' = ⊤` when `R' < R` (unstable). -/
theorem deconv_rate_rate_top (R R' : ℝ≥0) (h : R' < R) :
    deconv (rate R) (rate R')
      = fun _ => (⊤:ℝ≥0∞) := by
  conv_lhs => rw [← tokenBucket_zero_rate R]
  exact deconv_tokenBucket_rate_top R 0 R' h

/-- Horizontal deviation of `f` from `g` at `t`: least shift `d` with `f t ≤ g(t+d)`. -/
noncomputable def horizDevAt (f g : ℝ≥0 → ℝ≥0∞)
    (t : ℝ≥0) : ℝ≥0∞ :=
  ⨅ d : {d : ℝ≥0 // f t ≤ g (t + d)}, (d.1 : ℝ≥0∞)

/-- `horizDevAt f g t = ⊤` when no admissible shift exists. -/
theorem horizDevAt_eq_top (f g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0)
    (h : ∀ d : ℝ≥0, ¬ f t ≤ g (t + d)) :
    horizDevAt f g t = ⊤ := by
  unfold horizDevAt
  rw [iInf_eq_top]
  rintro ⟨d, hd⟩
  exact absurd hd (h d)

/-- Horizontal deviation `hDev f g = ⨆ t, horizDevAt f g t`. -/
noncomputable def hDev (f g : ℝ≥0 → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, horizDevAt f g t

/-- Vertical deviation `vDev f g = ⨆ t, f t - g t`. -/
noncomputable def vDev {D T : Type*} [SupSet T] [Sub T]
    (f g : D → T) : T :=
  ⨆ t : D, f t - g t

/-- `vDev f g = (f ⊘ g) 0`. -/
theorem vDev_eq_deconv_zero {D T : Type*}
    [_root_.AddZeroClass D] [SupSet T] [Sub T]
    (f g : D → T) :
    vDev f g = deconv f g 0 := by
  unfold vDev deconv
  simp only [zero_add]

/-- `delay d (t + u) = ⊤` when `d < t + u`. -/
theorem delay_top_of_gt (d t u : ℝ≥0) (h : d < t + u) :
    delay d (t + u) = ⊤ := by
  simp only [delay, if_neg (not_le.mpr h)]

/-- `horizDevAt f (delay d) t ≤ d`. -/
theorem horizDevAt_delay_le (f : ℝ≥0 → ℝ≥0∞) (d t : ℝ≥0) :
    horizDevAt f (delay d) t ≤ d := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  have hadm : f t ≤ delay d (t + (d + ε)) := by
    rw [delay_top_of_gt d t (d + ε) (by
      calc d < d + ε := by simpa using hε
        _ ≤ t + (d + ε) := le_add_self)]
    exact le_top
  unfold horizDevAt
  refine iInf_le_of_le ⟨d + ε, hadm⟩ ?_
  push_cast; rfl

/-- `hDev f (delay d) ≤ d`. -/
theorem hDev_delay_le (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0) :
    hDev f (delay d) ≤ d := by
  unfold hDev
  exact iSup_le (fun t => horizDevAt_delay_le f d t)

/-- `(d - t) ≤ horizDevAt f (delay d) t` when `f t > 0`. -/
theorem horizDevAt_delay_ge (f : ℝ≥0 → ℝ≥0∞) (d t : ℝ≥0)
    (hft : 0 < f t) :
    ((d - t : ℝ≥0) : ℝ≥0∞) ≤ horizDevAt f (delay d) t := by
  unfold horizDevAt
  refine le_iInf ?_
  rintro ⟨d', hd'⟩
  by_contra hlt
  rw [not_le] at hlt
  have hd'r : d' < d - t := by exact_mod_cast hlt
  have htd : t + d' < d := by
    rwa [lt_tsub_iff_left] at hd'r
  have h0 : delay d (t + d') = 0 := by
    simp only [delay, if_pos htd.le]
  rw [h0] at hd'
  exact absurd (le_antisymm hd' bot_le) hft.ne'

/-- `hDev f (delay d) = d` when `f > 0` on `(0, ∞)`. -/
theorem hDev_delay_eq (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0)
    (hf : ∀ t : ℝ≥0, 0 < t → 0 < f t) :
    hDev f (delay d) = d := by
  apply le_antisymm (hDev_delay_le f d)
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  have ht : (0:ℝ≥0) < ε := hε
  have hlb : ((d - ε : ℝ≥0):ℝ≥0∞) ≤ hDev f (delay d) := by
    refine le_trans (horizDevAt_delay_ge f d ε (hf ε ht)) ?_
    unfold hDev; exact le_iSup _ ε
  calc (d:ℝ≥0∞) ≤ ((d - ε : ℝ≥0):ℝ≥0∞) + ε := by
        rw [← ENNReal.coe_add]; exact_mod_cast le_tsub_add
    _ ≤ hDev f (delay d) + ε := by gcongr

/-- `hDev f (delay d) = d` if `f > 0` on some right-window of `0`. -/
theorem hDev_delay_eq_of_pos_window
    (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0)
    (hw : ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t : ℝ≥0, 0 < t → t < δ → 0 < f t) :
    hDev f (delay d) = d := by
  apply le_antisymm (hDev_delay_le f d)
  obtain ⟨δ, hδ, hpw⟩ := hw
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  set s : ℝ≥0 := min ε (δ / 2) with hs
  have hs_pos : 0 < s := lt_min hε (by positivity)
  have hs_ltδ : s < δ :=
    lt_of_le_of_lt (min_le_right _ _)
      (NNReal.half_lt_self hδ.ne')
  have hs_le_ε : (s:ℝ≥0∞) ≤ ε := by
    exact_mod_cast min_le_left _ _
  have hlb : ((d - s : ℝ≥0):ℝ≥0∞)
      ≤ hDev f (delay d) := by
    refine le_trans
      (horizDevAt_delay_ge f d s (hpw s hs_pos hs_ltδ)) ?_
    unfold hDev; exact le_iSup _ s
  calc (d:ℝ≥0∞) ≤ ((d - s : ℝ≥0):ℝ≥0∞) + s := by
        rw [← ENNReal.coe_add]; exact_mod_cast le_tsub_add
    _ ≤ hDev f (delay d) + ε := add_le_add hlb hs_le_ε

/-- `hDev f (delay d) = d` if `f(0⁺) = L > 0`. -/
theorem hDev_delay_eq_of_rightLimit_pos
    (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0) (L : ℝ≥0∞)
    (hL : TendstoRight f 0 L) (hL0 : 0 < L) :
    hDev f (delay d) = d :=
  hDev_delay_eq_of_pos_window f d
    (pos_near_zero_of_rightLimit_pos f L hL hL0)

/-- `hDev f (delay d) = d` if `f` is right-continuous with `f 0 > 0`. -/
theorem hDev_delay_eq_of_rightCont
    (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0)
    (hrc : IsRightContinuous f) (h0 : 0 < f 0) :
    hDev f (delay d) = d :=
  hDev_delay_eq_of_rightLimit_pos f d (f 0)
    (hrc 0).tendsto h0

/-- `tokenBucket r b` has right limit `b` at `0`. -/
theorem tokenBucket_tendsto_right (r b : ℝ≥0) :
    Tendsto (tokenBucket r b) (𝓝[>] (0:ℝ≥0))
      (𝓝 (b:ℝ≥0∞)) := by
  have heq : (𝓝[>] (0:ℝ≥0)).EventuallyEq
      (tokenBucket r b)
      (fun t => ((r*t + b : ℝ≥0):ℝ≥0∞)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [tokenBucket_apply_pos r b t
      (Set.mem_Ioi.mp ht).ne']
    push_cast; ring
  rw [tendsto_congr' heq]
  have hcont : Tendsto
      (fun t : ℝ≥0 => ((r*t + b : ℝ≥0):ℝ≥0∞))
      (𝓝 (0:ℝ≥0)) (𝓝 ((r*0 + b : ℝ≥0):ℝ≥0∞)) := by
    apply (ENNReal.continuous_coe.tendsto _).comp
    exact (continuous_const.mul continuous_id).add
      continuous_const |>.tendsto 0
  simp only [mul_zero, zero_add] at hcont
  exact hcont.mono_left nhdsWithin_le_nhds

/-- `hDev (tokenBucket r b) (delay d) = d` when `b > 0`. -/
theorem hDev_tokenBucket_delay (r b d : ℝ≥0)
    (hb : 0 < b) :
    hDev (tokenBucket r b) (delay d) = d :=
  hDev_delay_eq_of_rightLimit_pos (tokenBucket r b) d
    (b:ℝ≥0∞) (tokenBucket_tendsto_right r b)
    (by exact_mod_cast hb)

/-- `rateLatency R T u = ↑(R * (u - T))`. -/
theorem rateLatency_coe' (R T u : ℝ≥0) :
    rateLatency R T u = ((R*(u-T):ℝ≥0):ℝ≥0∞) := by
  simp only [rateLatency]; push_cast; ring

/-- Admissibility `tb ≤ βRT(t+d)` gives `r*t+b ≤ R*((t+d)-T)`. -/
theorem beta_admissible_imp
    (r b R T t d : ℝ≥0) (ht : t ≠ 0)
    (h : tokenBucket r b t ≤ rateLatency R T (t+d)) :
    (r*t+b : ℝ≥0) ≤ R*((t+d)-T) := by
  rw [tokenBucket_apply_pos r b t ht, rateLatency_coe',
    show (r:ℝ≥0∞)*t+b = ((r*t+b:ℝ≥0):ℝ≥0∞)
      by push_cast; ring,
    ENNReal.coe_le_coe] at h
  exact h

/-- Shift `d* = T + b/R` is admissible (`0 < R`, `r ≤ R`). -/
theorem dstar_admissible (r b R T t : ℝ≥0)
    (hR : 0 < R) (hrR : r ≤ R) :
    tokenBucket r b t
      ≤ rateLatency R T (t + (T + b/R)) := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; rw [tokenBucket_zero_eq]; exact bot_le
  · rw [tokenBucket_apply_pos r b t ht, rateLatency_coe',
      show (r:ℝ≥0∞)*t+b = ((r*t+b:ℝ≥0):ℝ≥0∞)
        by push_cast; ring, ENNReal.coe_le_coe]
    have hkey : (t + (T + b/R)) - T = t + b/R := by
      rw [show t + (T + b/R) = (t + b/R) + T by ring,
        add_tsub_cancel_right]
    rw [hkey]
    have hRbR : R * (b/R) = b := by
      rw [mul_div_assoc', mul_comm, mul_div_assoc,
        div_self hR.ne', mul_one]
    calc (r*t+b : ℝ≥0) ≤ R*t + b := by gcongr
      _ = R*(t + b/R) := by rw [mul_add, hRbR]

/-- `hDev (tokenBucket r b) βRT ≤ T + b/R` (`0 < R`, `r ≤ R`). -/
theorem hDev_tokenBucket_rateLatency_le
    (r b R T : ℝ≥0) (hR : 0 < R) (hrR : r ≤ R) :
    hDev (tokenBucket r b) (rateLatency R T)
      ≤ ((T + b/R : ℝ≥0):ℝ≥0∞) := by
  unfold hDev
  refine iSup_le (fun t => ?_)
  unfold horizDevAt
  exact iInf_le_of_le
    ⟨T + b/R, dstar_admissible r b R T t hR hrR⟩
    (le_refl _)

/-- Admissible shift lower bound: `R*T + b ≤ R*d + (R-r)*t`. -/
theorem dlb (r b R T t d : ℝ≥0) (hb : 0 < b)
    (ht : t ≠ 0)
    (h : tokenBucket r b t ≤ rateLatency R T (t+d)) :
    R*T + b ≤ R*d + (R - r)*t := by
  have hreal := beta_admissible_imp r b R T t d ht h
  rw [← NNReal.coe_le_coe] at hreal ⊢
  push_cast [NNReal.coe_sub_def] at hreal ⊢
  have htt : (0:ℝ) ≤ t := by positivity
  have hbb : (0:ℝ) < b := by exact_mod_cast hb
  have hmrt : (R-r:ℝ)*t ≤ max ((R:ℝ)-r) 0 * t := by
    rcases le_total ((R:ℝ)-r) 0 with hle|hle
    · rw [max_eq_right hle]; nlinarith
    · rw [max_eq_left hle]
  rcases le_total ((t:ℝ)+d-T) 0 with hle|hle
  · rw [max_eq_right hle] at hreal
    nlinarith [hreal,
      mul_nonneg htt (by positivity : (0:ℝ) ≤ r)]
  · rw [max_eq_left hle] at hreal
    nlinarith [hreal, hmrt]

/-- Per-point lower bound on `horizDevAt (tokenBucket r b) βRT`. -/
theorem horizDevAt_rateLatency_ge (r b R T t : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (ht : t ≠ 0) :
    (((T + b/R) - ((R-r)/R)*t : ℝ≥0):ℝ≥0∞)
      ≤ horizDevAt (tokenBucket r b)
          (rateLatency R T) t := by
  unfold horizDevAt
  refine le_iInf ?_
  rintro ⟨d, hd⟩
  rw [ENNReal.coe_le_coe, tsub_le_iff_right]
  have hbnd := dlb r b R T t d hb ht hd
  rw [← NNReal.coe_le_coe] at hbnd ⊢
  push_cast [NNReal.coe_sub_def] at hbnd ⊢
  have hRpos : (0:ℝ) < R := by exact_mod_cast hR
  refine le_of_mul_le_mul_right ?_ hRpos
  have e1 : ((T:ℝ) + b/R) * R = R*T + b := by
    field_simp
  have e2 : ((d:ℝ) + max ((R:ℝ)-r) 0 / R * t) * R
      = R*d + max ((R:ℝ)-r) 0 * t := by field_simp
  rw [e1, e2]; linarith [hbnd]

/-- `T + b/R ≤ hDev (tokenBucket r b) βRT` (`0 < R`, `0 < b`). -/
theorem hDev_tokenBucket_rateLatency_ge
    (r b R T : ℝ≥0) (hR : 0 < R) (hb : 0 < b) :
    ((T + b/R : ℝ≥0):ℝ≥0∞)
      ≤ hDev (tokenBucket r b) (rateLatency R T) := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  set c : ℝ≥0 := (R-r)/R with hc
  set s : ℝ≥0 := ε / (c + 1) with hs
  have hsne : s ≠ 0 := by rw [hs]; positivity
  have h1 : (((T + b/R) - c*s : ℝ≥0):ℝ≥0∞)
      ≤ hDev (tokenBucket r b) (rateLatency R T) := by
    refine le_trans
      (horizDevAt_rateLatency_ge r b R T s hR hb hsne) ?_
    unfold hDev; exact le_iSup _ s
  have hcs_le : ((c*s : ℝ≥0):ℝ≥0∞) ≤ (ε:ℝ≥0∞) := by
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    rw [hs]; push_cast
    have hd : (0:ℝ) < (c:ℝ) + 1 := by positivity
    rw [mul_div_assoc', div_le_iff₀ hd]
    nlinarith [c.coe_nonneg, ε.coe_nonneg]
  calc ((T + b/R : ℝ≥0):ℝ≥0∞)
      ≤ (((T+b/R) - c*s : ℝ≥0):ℝ≥0∞) + (c*s : ℝ≥0) := by
        rw [← ENNReal.coe_add]
        exact_mod_cast le_tsub_add
    _ ≤ hDev (tokenBucket r b) (rateLatency R T) + ε :=
        add_le_add h1 hcs_le

/-- `hDev (tokenBucket r b) βRT = T + b/R` (stable case). -/
theorem hDev_tokenBucket_rateLatency (r b R T : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hrR : r ≤ R) :
    hDev (tokenBucket r b) (rateLatency R T)
      = ((T + b/R : ℝ≥0):ℝ≥0∞) :=
  le_antisymm
    (hDev_tokenBucket_rateLatency_le r b R T hR hrR)
    (hDev_tokenBucket_rateLatency_ge r b R T hR hb)

/-- Unstable admissible bound: `(r-R)*t ≤ R*d` when `R < r`. -/
theorem dlb_top (r b R T t d : ℝ≥0) (hR : 0 < R)
    (hb : 0 < b) (hRr : R < r) (ht : t ≠ 0)
    (h : tokenBucket r b t ≤ rateLatency R T (t+d)) :
    (r - R)*t ≤ R*d := by
  have hreal := beta_admissible_imp r b R T t d ht h
  rw [← NNReal.coe_le_coe] at hreal ⊢
  push_cast [NNReal.coe_sub_def] at hreal ⊢
  have hRpos : (0:ℝ) < R := by exact_mod_cast hR
  have hbb : (0:ℝ) < b := by exact_mod_cast hb
  have hRr' : (R:ℝ) < r := by exact_mod_cast hRr
  rw [max_eq_left (by linarith : (0:ℝ) ≤ (r:ℝ)-R)]
  rcases le_total ((t:ℝ)+d-T) 0 with hle|hle
  · rw [max_eq_right hle] at hreal
    nlinarith [hreal,
      mul_nonneg hRpos.le (by positivity:(0:ℝ)≤t)]
  · rw [max_eq_left hle] at hreal
    nlinarith [hreal, T.coe_nonneg, hbb,
      mul_nonneg hRpos.le T.coe_nonneg]

/-- Unstable per-point lower bound growing linearly in `t`. -/
theorem horizDevAt_rateLatency_ge_top (r b R T t : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hRr : R < r) (ht : t ≠ 0) :
    ((((r-R)/R)*t : ℝ≥0):ℝ≥0∞)
      ≤ horizDevAt (tokenBucket r b)
          (rateLatency R T) t := by
  unfold horizDevAt
  refine le_iInf ?_
  rintro ⟨d, hd⟩
  rw [ENNReal.coe_le_coe]
  have hbnd := dlb_top r b R T t d hR hb hRr ht hd
  show ((r-R)/R)*t ≤ d
  rw [div_mul_eq_mul_div, div_le_iff₀ hR, mul_comm d R]
  exact hbnd

/-- `hDev (tokenBucket r b) βRT = ⊤` when `R < r` (unstable). -/
theorem hDev_tokenBucket_rateLatency_top
    (r b R T : ℝ≥0) (hR : 0 < R) (hb : 0 < b)
    (hRr : R < r) :
    hDev (tokenBucket r b) (rateLatency R T) = ⊤ := by
  have hc : 0 < (r - R)/R := by
    have : 0 < r - R := tsub_pos_of_lt hRr
    positivity
  rw [eq_top_iff, ← iSup_coe_mul_eq_top ((r-R)/R) hc]
  refine iSup_le (fun s => ?_)
  rcases eq_or_ne s 0 with hs | hs
  · subst hs; simp
  · refine le_trans
      (horizDevAt_rateLatency_ge_top r b R T s hR hb hRr hs)
      ?_
    exact le_iSup
      (fun t => horizDevAt (tokenBucket r b)
        (rateLatency R T) t) s

/-- `vDev (tokenBucket r b) (delay d) = r*d + b` for `d > 0`. -/
theorem vDev_tokenBucket_delay (r b d : ℝ≥0)
    (hd : 0 < d) :
    vDev (tokenBucket r b) (delay d)
      = (r*d + b : ℝ≥0) := by
  rw [vDev_eq_deconv_zero,
    deconv_tokenBucket_delay r b d hd]
  simp only [affine, ENNReal.coe_zero, mul_zero,
    zero_add]
  push_cast; ring

/-- `vDev (tokenBucket r b) βRT = r*T + b` (`r ≤ R`, `T > 0`). -/
theorem vDev_tokenBucket_rateLatency (r b R T : ℝ≥0)
    (h : r ≤ R) (hT : 0 < T) :
    vDev (tokenBucket r b) (rateLatency R T)
      = (r*T + b : ℝ≥0) := by
  rw [vDev_eq_deconv_zero,
    deconv_tokenBucket_rateLatency r b R T h hT]
  simp only [affine, ENNReal.coe_zero, mul_zero,
    zero_add]
  push_cast; ring

/-- `vDev (tokenBucket r b) βRT = ⊤` when `R < r` (unstable). -/
theorem vDev_tokenBucket_rateLatency_top
    (r b R T : ℝ≥0) (hRr : R < r) :
    vDev (tokenBucket r b) (rateLatency R T) = ⊤ := by
  rw [vDev_eq_deconv_zero,
    deconv_tokenBucket_rateLatency_top r b R T hRr]

end DeepWiki
