import Mathlib.Topology.Instances.EReal.Lemmas
import Book.Continuity
import Book.RealCurves

/-! Regularity of the concrete real curves (defined in `RealCurves`): pointwise /
piecewise continuity and left-continuity over `ℝ≥0 → ℝ≥0∞`. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

/-- `rateEReal C` is continuous. -/
theorem rateEReal_continuous (C : ℝ≥0) : Continuous (rateEReal C) :=
  continuous_coe_real_ereal.comp (NNReal.continuous_coe.comp
    (continuous_const.mul continuous_id))

/-- `rateEReal C` is left-continuous. -/
theorem rateEReal_leftCont (C : ℝ≥0) : IsLeftContinuous (rateEReal C) :=
  isLeftContinuous_of_continuous _ (rateEReal_continuous C)

/-- `rateNN R` is continuous. -/
theorem rateNN_continuous (R : ℝ≥0) : Continuous (rateNN R) :=
  (ENNReal.continuous_const_mul (by simp)).comp
    (by fun_prop)

/-- `rateLatencyNN R T` is continuous. -/
theorem rateLatencyNN_continuous (R T : ℝ≥0) :
    Continuous (rateLatencyNN R T) :=
  (ENNReal.continuous_const_mul (by simp)).comp
    (by fun_prop)

/-- `rateNN R` is piecewise continuous. -/
theorem rateNN_pwc (R : ℝ≥0) :
    IsPiecewiseContinuous (rateNN R) :=
  isPiecewiseContinuous_of_continuous _ (rateNN_continuous R)

/-- `rateLatencyNN R T` is piecewise continuous. -/
theorem rateLatencyNN_pwc (R T : ℝ≥0) :
    IsPiecewiseContinuous (rateLatencyNN R T) :=
  isPiecewiseContinuous_of_continuous _
    (rateLatencyNN_continuous R T)

/-- `delayNN d` is continuous at every `t ≠ d`. -/
theorem delayNN_continuousAt (d t : ℝ≥0) (h : t ≠ d) :
    ContinuousAt (delayNN d) t := by
  rcases lt_or_gt_of_ne h with h | h
  · refine (continuousAt_const (y := (0:ℝ≥0∞))).congr ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    simp [delayNN, le_of_lt (Set.mem_Iio.mp hs)]
  · refine (continuousAt_const (y := (⊤:ℝ≥0∞))).congr ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    simp [delayNN, not_le.mpr (Set.mem_Ioi.mp hs)]

/-- `delayNN d` is piecewise continuous (one jump at `d`). -/
theorem delayNN_pwc (d : ℝ≥0) :
    IsPiecewiseContinuous (delayNN d) := by
  intro T
  apply Set.Finite.subset (Set.finite_singleton d)
  rintro t ⟨ht, _⟩
  by_contra hne
  exact ht (delayNN_continuousAt d t hne)

/-- `unitStep T` is continuous at every `t ≠ T`. -/
theorem unitStep_continuousAt (T t : ℝ≥0) (h : t ≠ T) :
    ContinuousAt (unitStep T) t := by
  rcases lt_or_gt_of_ne h with h | h
  · refine (continuousAt_const (y := (0:ℝ≥0∞))).congr ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    simp [unitStep, le_of_lt (Set.mem_Iio.mp hs)]
  · refine (continuousAt_const (y := (1:ℝ≥0∞))).congr ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    simp [unitStep, not_le.mpr (Set.mem_Ioi.mp hs)]

/-- `unitStep T` is piecewise continuous (one jump at `T`). -/
theorem unitStep_pwc (T : ℝ≥0) :
    IsPiecewiseContinuous (unitStep T) := by
  intro S
  apply Set.Finite.subset (Set.finite_singleton T)
  rintro t ⟨ht, _⟩
  by_contra hne
  exact ht (unitStep_continuousAt T t hne)

/-- `tokenBucketNN r b` is continuous at every `t ≠ 0`. -/
theorem tokenBucketNN_continuousAt (r b t : ℝ≥0)
    (h : t ≠ 0) : ContinuousAt (tokenBucketNN r b) t := by
  rw [tokenBucketNN_eq]
  refine Filter.Tendsto.min ?_ (delayNN_continuousAt 0 t h)
  have h1 : ContinuousAt
      (fun s : ℝ≥0 => (r:ℝ≥0∞) * s) t :=
    (ENNReal.continuous_const_mul
      (by simp)).continuousAt.comp (by fun_prop)
  exact h1.add continuousAt_const

/-- `tokenBucketNN r b` is piecewise continuous (one jump at `0`). -/
theorem tokenBucketNN_pwc (r b : ℝ≥0) :
    IsPiecewiseContinuous (tokenBucketNN r b) := by
  intro T
  apply Set.Finite.subset (Set.finite_singleton 0)
  rintro t ⟨ht, _⟩
  by_contra hne
  exact ht (tokenBucketNN_continuousAt r b t hne)

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
  refine Filter.Tendsto.min ?_ (delayNN_continuousAt 0 t h0)
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

/-- `rateNN R` is left-continuous. -/
theorem rateNN_leftCont (R : ℝ≥0) :
    IsLeftContinuous (rateNN R) :=
  isLeftContinuous_of_continuous _ (rateNN_continuous R)

/-- `rateLatencyNN R T` is left-continuous. -/
theorem rateLatencyNN_leftCont (R T : ℝ≥0) :
    IsLeftContinuous (rateLatencyNN R T) :=
  isLeftContinuous_of_continuous _ (rateLatencyNN_continuous R T)

/-- `delayNN d` is left-continuous. -/
theorem delayNN_leftCont (d : ℝ≥0) :
    IsLeftContinuous (delayNN d) := by
  intro t
  rcases le_or_gt t d with h | h
  · refine ContinuousWithinAt.congr
      (f := fun _ => (0:ℝ≥0∞)) continuousWithinAt_const
      (fun s hs => ?_) ?_
    · simp only [delayNN, delay_apply,
        if_pos (le_of_lt (lt_of_lt_of_le hs h))]
    · simp [delayNN, h]
  · have hev : (delayNN d) =ᶠ[𝓝[Iio t] t]
        (fun _ => (⊤:ℝ≥0∞)) := by
      filter_upwards [Ioo_mem_nhdsLT h] with s hs
      simp [delayNN, not_le.mpr hs.1]
    exact continuousWithinAt_const.congr_of_eventuallyEq
      hev (by simp [delayNN, not_le.mpr h])

/-- `unitStep T` is left-continuous. -/
theorem unitStep_leftCont (T : ℝ≥0) :
    IsLeftContinuous (unitStep T) := by
  intro t
  rcases le_or_gt t T with h | h
  · refine ContinuousWithinAt.congr
      (f := fun _ => (0:ℝ≥0∞)) continuousWithinAt_const
      (fun s hs => ?_) ?_
    · simp only [unitStep,
        if_pos (le_of_lt (lt_of_lt_of_le hs h))]
    · simp [unitStep, h]
  · have hev : (unitStep T) =ᶠ[𝓝[Iio t] t]
        (fun _ => (1:ℝ≥0∞)) := by
      filter_upwards [Ioo_mem_nhdsLT h] with s hs
      simp [unitStep, not_le.mpr hs.1]
    exact continuousWithinAt_const.congr_of_eventuallyEq
      hev (by simp [unitStep, not_le.mpr h])

/-- `tokenBucketNN r b` is left-continuous. -/
theorem tokenBucketNN_leftCont (r b : ℝ≥0) :
    IsLeftContinuous (tokenBucketNN r b) := by
  intro t
  rw [tokenBucketNN_eq]
  refine Filter.Tendsto.min ?_ (delayNN_leftCont 0 t)
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
    (staircase_val_leftCont P h hP J t) (delayNN_leftCont 0 t)

/-- `staircaseFun T b d` is continuous at every `u` off the jump set
`{d + k·T | k ∈ ℕ}`. -/
theorem staircaseFun_continuousAt {T : ℝ≥0} (hT : 0 < T) (b d : ℝ≥0)
    {u : ℝ≥0} (h : ∀ k : ℕ, (u : ℝ) ≠ (d : ℝ) + k * T) :
    ContinuousAt (staircaseFun T b d) u := by
  have hT' : (0 : ℝ) < (T : ℝ) := NNReal.coe_pos.mpr hT
  have hud : (u : ℝ) ≠ (d : ℝ) := by simpa using h 0
  rcases lt_or_gt_of_ne hud with hlt | hgt
  · -- below the delay: locally `0`
    have hud' : u < d := by exact_mod_cast hlt
    refine (continuousAt_const (y := (0 : ℝ≥0))).congr ?_
    filter_upwards [Iio_mem_nhds hud'] with s hs
    rw [staircaseFun_eq_zero_of_le (le_of_lt hs)]
  · -- strictly between two jumps: locally `b·(m + 1)`
    set x : ℝ := ((u : ℝ) - d) / T with hx
    have hxpos : 0 < x := div_pos (by linarith) hT'
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌈x⌉₊ = m + 1 :=
      ⟨⌈x⌉₊ - 1, (Nat.succ_pred_eq_of_pos (Nat.ceil_pos.mpr hxpos)).symm⟩
    have hxne : x ≠ ((m + 1 : ℕ) : ℝ) := by
      intro hxeq
      refine h (m + 1) ?_
      have h1 : (u : ℝ) - d = ((m + 1 : ℕ) : ℝ) * T :=
        (div_eq_iff hT'.ne').mp hxeq
      push_cast at h1 ⊢
      linarith
    have hxlt : x < (m : ℝ) + 1 := by
      have hle : x ≤ ((m + 1 : ℕ) : ℝ) := hm ▸ Nat.le_ceil x
      have := lt_of_le_of_ne hle hxne
      exact_mod_cast this
    have hxgt : (m : ℝ) < x := by
      have hmlt : m < ⌈x⌉₊ := hm ▸ m.lt_succ_self
      exact_mod_cast Nat.lt_ceil.mp hmlt
    have hcont : Continuous fun s : ℝ≥0 => ((s : ℝ) - d) / T :=
      (NNReal.continuous_coe.sub continuous_const).div_const (T : ℝ)
    have hev : ∀ᶠ s : ℝ≥0 in 𝓝 u,
        ((s : ℝ) - d) / T ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1) :=
      hcont.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds ⟨hxgt, hxlt⟩)
    refine (continuousAt_const (y := b * ((m + 1 : ℕ) : ℝ≥0))).congr ?_
    filter_upwards [hev] with s hs
    symm
    show staircaseFun T b d s = b * ((m + 1 : ℕ) : ℝ≥0)
    unfold staircaseFun
    congr 2
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero m)]
    refine ⟨by simpa using hs.1, ?_⟩
    push_cast
    exact hs.2.le

/-- `staircaseFun T b d` is piecewise continuous: at most `⌈M/T⌉₊ + 1` jumps
on each `[0, M]`. -/
theorem staircaseFun_pwc (T b d : ℝ≥0) :
    IsPiecewiseContinuous (staircaseFun T b d) := by
  rcases eq_zero_or_pos T with rfl | hT
  · rw [staircaseFun_period_zero]
    exact isPiecewiseContinuous_of_continuous _ continuous_const
  intro M
  have hT' : (0 : ℝ) < (T : ℝ) := NNReal.coe_pos.mpr hT
  refine Set.Finite.subset
    ((Set.finite_Iic ⌈(M : ℝ) / T⌉₊).image fun k : ℕ => d + (k : ℝ≥0) * T) ?_
  rintro u ⟨hu, -, huM⟩
  have hk : ∃ k : ℕ, (u : ℝ) = (d : ℝ) + k * T := by
    by_contra hcon
    push Not at hcon
    exact hu (staircaseFun_continuousAt hT b d hcon)
  obtain ⟨k, hk⟩ := hk
  refine ⟨k, ?_, ?_⟩
  · -- the jump index is bounded on `[0, M]`
    have hM : (u : ℝ) ≤ M := NNReal.coe_le_coe.mpr huM
    have hd : (0 : ℝ) ≤ d := d.coe_nonneg
    have hkT : (k : ℝ) * T ≤ (M : ℝ) := by linarith
    have hdiv : (k : ℝ) ≤ (M : ℝ) / T := (le_div_iff₀ hT').mpr hkT
    have hN : (k : ℝ) ≤ (⌈(M : ℝ) / T⌉₊ : ℝ) := hdiv.trans (Nat.le_ceil _)
    exact_mod_cast hN
  · refine NNReal.coe_injective ?_
    push_cast
    linarith [hk]

/-- `staircaseFun T b d` is left-continuous. -/
theorem staircaseFun_leftCont (T b d : ℝ≥0) :
    IsLeftContinuous (staircaseFun T b d) := by
  rcases eq_zero_or_pos T with rfl | hT
  · rw [staircaseFun_period_zero]
    exact isLeftContinuous_of_continuous _ continuous_const
  intro t
  have hT' : (0 : ℝ) < (T : ℝ) := NNReal.coe_pos.mpr hT
  rcases le_or_gt t d with htd | hdt
  · -- at or below the delay: locally `0`
    refine ContinuousWithinAt.congr (f := fun _ => (0 : ℝ≥0))
      continuousWithinAt_const (fun s hs => ?_) ?_
    · exact staircaseFun_eq_zero_of_le ((le_of_lt hs).trans htd)
    · exact staircaseFun_eq_zero_of_le htd
  · -- strictly after the delay: constant `b·(m + 1)` on `(d + m·T, t]`
    set x : ℝ := ((t : ℝ) - d) / T with hx
    have hdt' : (d : ℝ) < t := NNReal.coe_lt_coe.mpr hdt
    have hxpos : 0 < x := div_pos (by linarith) hT'
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌈x⌉₊ = m + 1 :=
      ⟨⌈x⌉₊ - 1, (Nat.succ_pred_eq_of_pos (Nat.ceil_pos.mpr hxpos)).symm⟩
    set t₀ : ℝ≥0 := d + (m : ℝ≥0) * T with ht₀
    have hmx : (m : ℝ) < x := by
      have hmlt : m < ⌈x⌉₊ := hm ▸ m.lt_succ_self
      exact_mod_cast Nat.lt_ceil.mp hmlt
    have ht₀t : t₀ < t := by
      rw [← NNReal.coe_lt_coe, ht₀]
      have := (lt_div_iff₀ hT').mp hmx
      push_cast
      linarith
    have hval : ∀ s : ℝ≥0, s ∈ Set.Ioc t₀ t →
        staircaseFun T b d s = b * ((m + 1 : ℕ) : ℝ≥0) := by
      intro s hs
      unfold staircaseFun
      congr 2
      have hlow : (m : ℝ) < ((s : ℝ) - d) / T := by
        rw [lt_div_iff₀ hT']
        have h1 : (t₀ : ℝ) < (s : ℝ) := NNReal.coe_lt_coe.mpr hs.1
        rw [ht₀] at h1
        push_cast at h1
        linarith
      have hupp : ((s : ℝ) - d) / T ≤ (m : ℝ) + 1 := by
        have h2 : ((s : ℝ) - d) / T ≤ x := by
          rw [hx, div_eq_mul_inv, div_eq_mul_inv]
          have := NNReal.coe_le_coe.mpr hs.2
          exact mul_le_mul_of_nonneg_right (by linarith)
            (inv_nonneg.mpr T.coe_nonneg)
        have h3 : x ≤ ((m + 1 : ℕ) : ℝ) := hm ▸ Nat.le_ceil x
        push_cast at h3
        linarith
      rw [Nat.ceil_eq_iff (Nat.succ_ne_zero m)]
      exact ⟨by simpa using hlow, by push_cast; exact hupp⟩
    have hev : staircaseFun T b d
        =ᶠ[𝓝[<] t] fun _ => b * ((m + 1 : ℕ) : ℝ≥0) := by
      filter_upwards [Ioo_mem_nhdsLT ht₀t] with s hs
      exact hval s ⟨hs.1, hs.2.le⟩
    exact continuousWithinAt_const.congr_of_eventuallyEq hev
      (hval t ⟨ht₀t, le_rfl⟩)

end DeepWiki
