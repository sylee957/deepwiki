import VersoManual
import Book.Additivity
import Book.Continuity
import Book.Closures

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Classes of usual functions" =>
Network calculus is built from a small repertoire of named curves: pure
delays, guaranteed rates, rate-latencies, token-buckets, staircases, and
a test function. Each is a real function $`\mathbb{R}^{+} \to
\overline{\mathbb{R}}_{\ge 0} = \mathbb{R}_{\ge 0} \cup \{+\infty\}`,
carried by `ℝ≥0∞` — the value $`+\infty` is needed by the pure delay and
the test function. Working with plain numeric values (rather than the
dioid newtype) keeps the definitions one-liners and lets the analytic
notions — continuity, left-continuity, piecewise continuity — apply
directly, since `ℝ≥0∞` carries a topology.

We collect the definitions, then verify the analytic properties: all six
are piecewise continuous and left-continuous and null at the origin, and
the rate and rate-latency are in fact continuous.

```lean
namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter
```

# The curves

We collect the six curves in one place; each is a one-line definition,
introduced by its formula. Finite values are real; the blocking value
of the delay and the saturated value of the test function are
$`+\infty = \top`.

The _pure delay_ $`\delta_d` lets everything through up to time $`d` and
blocks afterwards: it is $`0` for $`t \le d` and $`+\infty` beyond.

*Definition:* $`\delta_d(t) = 0` if $`t \le d`, else $`+\infty`

```lean
noncomputable def delay (d : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => if t ≤ d then 0 else ⊤
```

The _guaranteed rate_ $`\lambda_R` is the linear curve through the
origin with slope $`R`.

*Definition:* $`\lambda_R(t) = R\,t`

```lean
noncomputable def rate (R : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => (R : ℝ≥0∞) * (t : ℝ≥0∞)
```

The _rate-latency_ $`\beta_{R,T}` stays at $`0` until the latency $`T`,
then rises at rate $`R`. The truncated subtraction $`t - T` on
$`\mathbb{R}_{\ge 0}` already realises the non-negative part
$`[t - T]^{+}`.

*Definition:* $`\beta_{R,T}(t) = R\,[t - T]^{+}`

```lean
noncomputable def rateLatency (R T : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => (R : ℝ≥0∞) * ((t - T : ℝ≥0) : ℝ≥0∞)
```

The _token-bucket_ $`\gamma_{r,b}` is the affine curve $`r\,t + b`
capped below by the pure delay at the origin, so that
$`\gamma_{r,b}(0) = 0`. The cap is the pointwise minimum $`\wedge` of two
functions — `Mathlib`'s $`\inf` ($`\sqcap`) on the function type.

*Definition:* $`\gamma_{r,b} = (r\,(\cdot) + b) \wedge \delta_0`

```lean
noncomputable def tokenBucket (r b : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  (fun t => (r : ℝ≥0∞) * t + b) ⊓ delay 0
```

The _staircase_ $`\nu_{P,h,J}` rises in steps of height $`h` every
period $`P`, with phase $`J`: at time $`t` it has taken
$`\lceil (t + J)/P \rceil` steps. Its value is the non-negative part of
$`h\,\lceil (t + J)/P \rceil`, capped by the pure delay at the origin.

*Definition:* $`\nu_{P,h,J}(t) = \bigl[h\,\lceil (t + J)/P \rceil\bigr]^{+} \wedge \delta_0(t)`

```lean
noncomputable def staircase (P h : ℝ≥0) (J : ℝ) :
    ℝ≥0 → ℝ≥0∞ :=
  fun t =>
    min (ENNReal.ofReal
      (max (h * ⌈((t : ℝ) + J) / P⌉) 0)) (delay 0 t)
```

The _test function_ $`\mathbb{1}_{>T}` is $`0` up to time $`T` and
$`1` afterwards.

*Definition:* $`\mathbb{1}_{>T}(t) = 0` if $`t \le T`, else $`1`

```lean
noncomputable def test (T : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => if t ≤ T then 0 else 1
```

# Null at the origin

Every curve vanishes at $`t = 0` (the lone exception in the source — the
delay $`\delta_d` with $`d < 0` — does not arise here, since our
$`d \in \mathbb{R}^{+}`).

*Theorem:* $`\delta_d(0) = 0`

```lean
theorem delay_zero_eq (d : ℝ≥0) : delay d 0 = 0 := by
  simp [delay]
```

*Theorem:* $`\lambda_R(0) = 0`

```lean
theorem rate_zero_eq (R : ℝ≥0) : rate R 0 = 0 := by
  simp [rate]
```

*Theorem:* $`\beta_{R,T}(0) = 0`

```lean
theorem rateLatency_zero_eq (R T : ℝ≥0) :
    rateLatency R T 0 = 0 := by
  simp [rateLatency]
```

*Theorem:* $`\gamma_{r,b}(0) = 0`

```lean
theorem tokenBucket_zero_eq (r b : ℝ≥0) :
    tokenBucket r b 0 = 0 := by
  simp [tokenBucket, delay]
```

*Theorem:* $`\nu_{P,h,J}(0) = 0`

```lean
theorem staircase_zero_eq (P h : ℝ≥0) (J : ℝ) :
    staircase P h J 0 = 0 := by
  simp [staircase, delay]
```

*Theorem:* $`\mathbb{1}_{>T}(0) = 0`

```lean
theorem test_zero_eq (T : ℝ≥0) : test T 0 = 0 := by
  simp [test]
```

# Continuity of the rate and rate-latency

We now record the analytic regularity of the curves. Piecewise
continuity and left-continuity were developed in the chapter
`Continuity`; we reuse its $`\overline{\mathbb{R}}_{\ge 0}`-valued
notions `IsPiecewiseContinuous` (piecewise continuity) and `IsLeftContinuous`
(left-continuity) here.

The guaranteed rate and the rate-latency are genuinely continuous: each
is a constant multiple of a continuous $`\overline{\mathbb{R}}_{\ge 0}`-
valued function (the finite slope $`R` keeps multiplication continuous).

*Theorem:* $`\lambda_R` is continuous

```lean
theorem rate_continuous (R : ℝ≥0) : Continuous (rate R) :=
  (ENNReal.continuous_const_mul (by simp)).comp
    (by fun_prop)
```

*Theorem:* $`\beta_{R,T}` is continuous

```lean
theorem rateLatency_continuous (R T : ℝ≥0) :
    Continuous (rateLatency R T) :=
  (ENNReal.continuous_const_mul (by simp)).comp
    (by fun_prop)
```

Hence both are piecewise continuous.

*Theorem:* $`\lambda_R` is piecewise continuous

```lean
theorem rate_pwc (R : ℝ≥0) :
    IsPiecewiseContinuous (rate R) :=
  isPiecewiseContinuous_of_continuous _ (rate_continuous R)
```

*Theorem:* $`\beta_{R,T}` is piecewise continuous

```lean
theorem rateLatency_pwc (R T : ℝ≥0) :
    IsPiecewiseContinuous (rateLatency R T) :=
  isPiecewiseContinuous_of_continuous _
    (rateLatency_continuous R T)
```

# Piecewise continuity of the step curves

The pure delay is continuous everywhere except at $`d`: below $`d` it is
constantly $`0`, above it constantly $`+\infty`. So its single jump is
$`d`, and its discontinuity set is finite.

*Theorem:* $`\delta_d` is continuous away from $`d`

```lean
theorem delay_continuousAt (d t : ℝ≥0) (h : t ≠ d) :
    ContinuousAt (delay d) t := by
  rcases lt_or_gt_of_ne h with h | h
  · refine (continuousAt_const (y := (0:ℝ≥0∞))).congr ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    simp [delay, le_of_lt (Set.mem_Iio.mp hs)]
  · refine (continuousAt_const (y := (⊤:ℝ≥0∞))).congr ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    simp [delay, not_le.mpr (Set.mem_Ioi.mp hs)]
```

*Theorem:* $`\delta_d` is piecewise continuous

```lean
theorem delay_pwc (d : ℝ≥0) :
    IsPiecewiseContinuous (delay d) := by
  intro T
  apply Set.Finite.subset (Set.finite_singleton d)
  rintro t ⟨ht, _⟩
  by_contra hne
  exact ht (delay_continuousAt d t hne)
```

The test function is the same shape, jumping only at $`T`.

*Theorem:* $`\mathbb{1}_{>T}` is continuous away from $`T`

```lean
theorem test_continuousAt (T t : ℝ≥0) (h : t ≠ T) :
    ContinuousAt (test T) t := by
  rcases lt_or_gt_of_ne h with h | h
  · refine (continuousAt_const (y := (0:ℝ≥0∞))).congr ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    simp [test, le_of_lt (Set.mem_Iio.mp hs)]
  · refine (continuousAt_const (y := (1:ℝ≥0∞))).congr ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    simp [test, not_le.mpr (Set.mem_Ioi.mp hs)]
```

*Theorem:* $`\mathbb{1}_{>T}` is piecewise continuous

```lean
theorem test_pwc (T : ℝ≥0) :
    IsPiecewiseContinuous (test T) := by
  intro S
  apply Set.Finite.subset (Set.finite_singleton T)
  rintro t ⟨ht, _⟩
  by_contra hne
  exact ht (test_continuousAt T t hne)
```

The token-bucket is the minimum of the continuous affine curve and the
delay $`\delta_0`; away from the origin both pieces are continuous, so
their minimum is, and the only jump is $`0`.

*Theorem:* $`\gamma_{r,b}` is continuous away from the origin

```lean
theorem tokenBucket_continuousAt (r b t : ℝ≥0)
    (h : t ≠ 0) : ContinuousAt (tokenBucket r b) t := by
  refine Filter.Tendsto.min ?_ (delay_continuousAt 0 t h)
  have h1 : ContinuousAt
      (fun s : ℝ≥0 => (r:ℝ≥0∞) * s) t :=
    (ENNReal.continuous_const_mul
      (by simp)).continuousAt.comp (by fun_prop)
  exact h1.add continuousAt_const
```

*Theorem:* $`\gamma_{r,b}` is piecewise continuous

```lean
theorem tokenBucket_pwc (r b : ℝ≥0) :
    IsPiecewiseContinuous (tokenBucket r b) := by
  intro T
  apply Set.Finite.subset (Set.finite_singleton 0)
  rintro t ⟨ht, _⟩
  by_contra hne
  exact ht (tokenBucket_continuousAt r b t hne)
```

# Piecewise continuity of the staircase

The staircase jumps only where the step count $`\lceil (t + J)/P \rceil`
increments — at the times $`t` with $`(t + J)/P \in \mathbb{Z}`. Off
those times the ceiling is locally constant, so the staircase is
continuous; and on any interval $`[0, T]` only finitely many such times
occur (assuming $`P > 0`). We build this from a local-constancy fact for
the ceiling and a finiteness count for the jump times.

The ceiling $`\lceil \cdot \rceil` is locally constant away from the
integers: if $`\lceil x \rceil \ne x` then $`\lceil y \rceil =
\lceil x \rceil` for all $`y` near $`x`.

*Theorem:* $`\lceil \cdot \rceil` is eventually constant near a non-integer

```lean
theorem ceil_eventuallyEq (x : ℝ) (hx : (⌈x⌉ : ℝ) ≠ x) :
    ∀ᶠ y in 𝓝 x, ⌈y⌉ = ⌈x⌉ := by
  have hhi : x < (⌈x⌉ : ℝ) :=
    lt_of_le_of_ne (Int.le_ceil x) (fun h => hx h.symm)
  have hlo : (⌈x⌉ : ℝ) - 1 < x := by
    have := Int.ceil_lt_add_one x; linarith
  filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
  rw [Int.ceil_eq_iff]
  exact ⟨by linarith [hy.1], le_of_lt hy.2⟩
```

Hence the real-valued step count $`t \mapsto \lceil (t + J)/P \rceil` is
continuous at every non-jump time.

*Theorem:* the step count is continuous off the jump times

```lean
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
```

The jump times in $`[0, T]` are finite: a jump time $`t` satisfies
$`(t + J)/P = \lceil (t + J)/P \rceil \in \mathbb{Z}`, and the map
$`t \mapsto \lceil (t + J)/P \rceil` is injective on them (different
jump times give different integers) with image in a bounded integer
interval.

*Theorem:* the jump times in $`[0, T]` are finite

```lean
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
```

Assembling: away from the jump times the staircase is continuous (the
step count is, hence so is its scaling, clamping, and minimum with the
continuous-off-origin $`\delta_0`), and the jump times are finite, so
the staircase is piecewise continuous when $`P > 0`.

*Theorem:* the staircase is continuous off the jump times

```lean
theorem staircase_continuousAt (P h : ℝ≥0) (J : ℝ)
    (t : ℝ≥0) (h0 : t ≠ 0)
    (ht : (⌈((t:ℝ)+J)/P⌉ : ℝ) ≠ ((t:ℝ)+J)/P) :
    ContinuousAt (staircase P h J) t := by
  refine Filter.Tendsto.min ?_ (delay_continuousAt 0 t h0)
  apply ENNReal.continuous_ofReal.continuousAt.comp
  exact Filter.Tendsto.max
    ((stepCount_continuousAt P J t ht).const_mul (h:ℝ))
    continuousAt_const
```

*Theorem:* the staircase is piecewise continuous when $`P > 0`

```lean
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
  push_neg at hmem
  obtain ⟨hjump, h0⟩ := hmem
  apply ht
  refine staircase_continuousAt P h J t ?_ ?_
  · simpa using h0
  · intro hcontra
    exact hjump ⟨hcontra, htT.2⟩
```

# Left-continuity

`Mathlib`-left-continuity asks that a curve be continuous from the left
at every time. The continuous curves are left-continuous a fortiori (by
`leftCont_of_continuous` from the `Continuity` chapter); the step and
staircase curves jump _upward to the right_, so the left limit agrees
with the value, and they too are left-continuous.

*Theorem:* $`\lambda_R` is left-continuous

```lean
theorem rate_leftCont (R : ℝ≥0) :
    IsLeftContinuous (rate R) :=
  leftCont_of_continuous _ (rate_continuous R)
```

*Theorem:* $`\beta_{R,T}` is left-continuous

```lean
theorem rateLatency_leftCont (R T : ℝ≥0) :
    IsLeftContinuous (rateLatency R T) :=
  leftCont_of_continuous _ (rateLatency_continuous R T)
```

The pure delay is left-continuous: at $`t \le d` it is locally $`0`
below, and at $`t > d` the open interval $`(d, t)` lies just below $`t`,
on which it is constantly $`+\infty`.

*Theorem:* $`\delta_d` is left-continuous

```lean
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
```

The test function is left-continuous by the same argument, with the
upper value $`1` in place of $`+\infty`.

*Theorem:* $`\mathbb{1}_{>T}` is left-continuous

```lean
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
```

The token-bucket is the minimum of two left-continuous curves — the
continuous affine part and the left-continuous $`\delta_0` — so it is
left-continuous.

*Theorem:* $`\gamma_{r,b}` is left-continuous

```lean
theorem tokenBucket_leftCont (r b : ℝ≥0) :
    IsLeftContinuous (tokenBucket r b) := by
  intro t
  refine Filter.Tendsto.min ?_ (delay_leftCont 0 t)
  have h1 : ContinuousWithinAt
      (fun s : ℝ≥0 => (r:ℝ≥0∞) * s) (Iio t) t :=
    ((ENNReal.continuous_const_mul
      (by simp)).comp (by fun_prop)).continuousWithinAt
  exact h1.add continuousWithinAt_const
```

The staircase is left-continuous too (for $`P > 0`). Its step count
$`\lceil (t + J)/P \rceil` is _constant just to the left_ of every time
— on the window $`((n-1)P - J,\ t]` with $`n = \lceil (t + J)/P \rceil`
— so the clamped value is eventually constant along $`\mathcal{N}[<] t`,
hence left-continuous; the minimum with the left-continuous $`\delta_0`
is then left-continuous.

*Theorem:* the step count is constant just to the left of $`t`

```lean
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
```

*Theorem:* the staircase value is left-continuous

```lean
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
```

*Theorem:* $`\nu_{P,h,J}` is left-continuous for $`P > 0`

```lean
theorem staircase_leftCont (P h : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ) : IsLeftContinuous (staircase P h J) := by
  intro t
  exact Filter.Tendsto.min
    (staircase_val_leftCont P h hP J t) (delay_leftCont 0 t)
```

# Relations among the usual functions

Several curves coincide at special parameter values. The guaranteed rate
is the rate-latency with zero latency, and the token-bucket with zero
burst; the test function $`\mathbb{1}_{>0}` is the token-bucket with zero
rate and unit burst. (The source's further relation $`\delta_0 = e` — the
delay at the origin being the dioid unit — is a statement about the
function _dioid_; on the bare numeric values used here there is no unit
to compare against. The remaining $`\delta_d = \varepsilon` for $`d < 0`
is vacuous on the $`\mathbb{R}^{+}` domain.)

*Theorem:* $`\lambda_R = \beta_{R,0}`

```lean
theorem rate_eq_rateLatency_zero (R : ℝ≥0) :
    rate R = rateLatency R 0 := by
  funext t; simp [rate, rateLatency]
```

*Theorem:* $`\lambda_R = \gamma_{R,0}`

```lean
theorem rate_eq_tokenBucket_zero (R : ℝ≥0) :
    rate R = tokenBucket R 0 := by
  funext t
  simp only [rate, tokenBucket, Pi.inf_apply,
    ENNReal.coe_zero, add_zero]
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [delay]
  · have ht : ¬ t ≤ 0 := by simpa using h
    simp [delay, ht]
```

*Theorem:* $`\mathbb{1}_{>0} = \gamma_{0,1}`

```lean
theorem test_zero_eq_tokenBucket :
    test (0 : ℝ≥0) = tokenBucket 0 1 := by
  funext t
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [test, tokenBucket, delay]
  · have ht : ¬ t ≤ 0 := by simpa using h
    simp [test, tokenBucket, delay, ht]
```

# Sub- and super-additivity

We now establish the sub/super-additivity of each curve, reusing the
`IsSubadditive` and `IsSuperadditive` predicates from the `Additivity`
chapter.

The guaranteed rate is _additive_ — both sub- and super-additive —
since $`R(u + s) = R\,u + R\,s`.

*Theorem:* $`\lambda_R` is sub-additive

```lean
theorem rate_subadditive (R : ℝ≥0) :
    IsSubadditive (rate R) := by
  intro u s; simp only [rate]; push_cast; rw [mul_add]
```

*Theorem:* $`\lambda_R` is super-additive

```lean
theorem rate_superadditive (R : ℝ≥0) :
    IsSuperadditive (rate R) := by
  intro u s; simp only [rate]; push_cast; rw [mul_add]
```

The pure delay is super-additive: if $`u + s \le d` then both arguments
are $`\le d` and all three values are $`0`; otherwise the right-hand
side is $`+\infty`.

*Theorem:* $`\delta_d` is super-additive

```lean
theorem delay_superadditive (d : ℝ≥0) :
    IsSuperadditive (delay d) := by
  intro u s
  simp only [delay]
  rcases le_or_gt (u + s) d with h | h
  · rw [if_pos h, if_pos (le_trans le_self_add h),
      if_pos (le_trans le_add_self h)]; simp
  · rw [if_neg (not_le.mpr h)]; exact le_top
```

The rate-latency is super-additive: the truncated subtractions satisfy
$`[u - T]^{+} + [s - T]^{+} \le [u + s - T]^{+}` (subtracting $`T` once
on the right loses less than subtracting it from each part), and scaling
by $`R` preserves this.

*Theorem:* $`[u - T]^{+} + [s - T]^{+} \le [(u + s) - T]^{+}`

```lean
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
```

*Theorem:* $`\beta_{R,T}` is super-additive

```lean
theorem rateLatency_superadditive (R T : ℝ≥0) :
    IsSuperadditive (rateLatency R T) := by
  intro u s
  simp only [rateLatency]
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul,
    ← ENNReal.coe_mul, ← ENNReal.coe_add,
    ENNReal.coe_le_coe, ← mul_add]
  exact mul_le_mul_left' (tsub_add_tsub_le_tsub u s T) R
```

The token-bucket is sub-additive. If either argument is $`0` the curve
there is $`0` and the inequality is the identity on the other; with both
positive the cap $`\delta_0` is $`+\infty`, so the value is the affine
part, and $`r(u + s) + b \le (r\,u + b) + (r\,s + b)` because $`b \ge 0`.

*Theorem:* $`\gamma_{r,b}` is sub-additive

```lean
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
```

The test function $`\mathbb{1}_{>T}` is, in general, _neither_ sub- nor
super-additive — the one exception being $`\mathbb{1}_{>0}`, which by the
relation $`\mathbb{1}_{>0} = \gamma_{0,1}` inherits the token-bucket's
sub-additivity.

*Theorem:* $`\mathbb{1}_{>0}` is sub-additive

```lean
theorem test_zero_subadditive :
    IsSubadditive (test (0 : ℝ≥0)) := by
  rw [test_zero_eq_tokenBucket]
  exact tokenBucket_subadditive 0 1
```

# Sub-additivity of the staircase

The staircase is sub-additive when the phase $`J \ge 0`. The heart is a
sub-additivity of the step count: since $`(u + s + J)/P \le (u + J)/P +
(s + J)/P` when $`J \ge 0`, the ceiling — itself sub-additive — gives
$`\lceil (u + s + J)/P \rceil \le \lceil (u + J)/P \rceil + \lceil (s +
J)/P \rceil`.

*Theorem:* the step count is sub-additive for $`J \ge 0`

```lean
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
```

Scaling by $`h \ge 0` and clamping by $`[\cdot]^{+}` preserves the
inequality at the level of values.

*Theorem:* the clamped staircase value is sub-additive

```lean
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
```

Away from the origin the $`\delta_0` cap is $`+\infty` and the staircase
is its clamped value, so sub-additivity of the value lifts to the curve.

*Theorem:* $`\nu_{P,h,J}` is sub-additive for $`J \ge 0`, $`P > 0`

```lean
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
```

# Super-additivity of the staircase

The staircase is _super_-additive when $`J < -P`. The step count is then
super-additive: from $`J/P < -1` one gets $`(u + J)/P + (s + J)/P \le
(u + s + J)/P - 1`, and combining the ceiling bound
$`\lceil a \rceil + \lceil b \rceil \le \lceil a + b \rceil + 1` with
$`\lceil c - 1 \rceil = \lceil c \rceil - 1` yields
$`\lceil (u + J)/P \rceil + \lceil (s + J)/P \rceil \le
\lceil (u + s + J)/P \rceil`.

*Theorem:* $`\lceil a \rceil + \lceil b \rceil \le \lceil a + b \rceil + 1`

```lean
theorem ceil_add_le_ceil_succ (x y : ℝ) :
    ⌈x⌉ + ⌈y⌉ ≤ ⌈x + y⌉ + 1 := by
  have hx := Int.ceil_lt_add_one x
  have hy := Int.ceil_lt_add_one y
  have hxy := Int.le_ceil (x + y)
  have hi : ⌈x⌉ + ⌈y⌉ < ⌈x+y⌉ + 2 := by
    have : (⌈x⌉:ℝ) + ⌈y⌉ < ⌈x+y⌉ + 2 := by linarith
    exact_mod_cast this
  omega
```

*Theorem:* the step count is super-additive for $`J < -P`

```lean
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
```

The clamp interacts with super-additivity through a small integer fact:
if $`n, m \le k` and $`n + m \le k`, then the clamped values satisfy
$`[h\,n]^{+} + [h\,m]^{+} \le [h\,k]^{+}`. The pairwise bounds
$`n \le k`, $`m \le k` (from ceiling monotonicity) are essential — they
rescue the case where one of $`n, m` is negative.

*Theorem:* the clamped values are super-additive under the integer bounds

```lean
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
```

*Theorem:* $`\nu_{P,h,J}` is super-additive for $`J < -P`, $`P > 0`

```lean
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
```

# The closures

Each curve, being sub- or super-additive and null at the origin, is its
own closure (the `Closures` chapter: a sub-additive curve null at $`0`
equals its sub-additive closure $`g^{\star}`, and dually a super-additive
curve its super-additive closure $`g^{\overline{\star}}`).

The sub-additive curves (token-bucket, sub-additive staircase, and the
test $`\mathbb{1}_{>0}`) are their own sub-additive closures.

*Theorem:* $`(\gamma_{r,b})^{\star} = \gamma_{r,b}`

```lean
theorem tokenBucket_closure (r b : ℝ≥0) :
    subadditiveClosureE (tokenBucket r b)
      = tokenBucket r b :=
  subadditiveClosureE_eq_self _
    (tokenBucket_subadditive r b)
    (tokenBucket_zero_eq r b)
```

*Theorem:* $`(\nu_{P,h,J})^{\star} = \nu_{P,h,J}` for $`J \ge 0`

```lean
theorem staircase_closure (P h : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ) (hJ : 0 ≤ J) :
    subadditiveClosureE (staircase P h J)
      = staircase P h J :=
  subadditiveClosureE_eq_self _
    (staircase_subadditive P h hP J hJ)
    (staircase_zero_eq P h J)
```

The super-additive closure lives on the dual carrier `WithBot ℝ≥0∞`, so
we read each super-additive curve there by adding a $`\bot = -\infty`
below — the coercion $`\overline{\mathbb{R}}_{\ge 0} \hookrightarrow
\overline{\mathbb{R}}_{\ge 0} \cup \{-\infty\}`. We register it on whole
curves, so $`\uparrow\!g` lifts $`g : \mathbb{R}^{+} \to
\overline{\mathbb{R}}_{\ge 0}`.

*Definition:* the coercion of a curve into `WithBot ℝ≥0∞`

```lean
instance : Coe (ℝ≥0 → ℝ≥0∞) (ℝ≥0 → WithBot ℝ≥0∞) :=
  ⟨fun g t => ((g t : ℝ≥0∞) : WithBot ℝ≥0∞)⟩
```

A super-additive curve null at the origin is its own super-additive
closure, in the lifted carrier.

*Theorem:* a super-additive curve null at $`0` satisfies $`(\uparrow\!g)^{\overline{\star}} = \uparrow\!g`

```lean
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
```

Projecting the closure back to $`\overline{\mathbb{R}}_{\ge 0}` (the
values are never $`-\infty`, so the projection is faithful) recovers the
curve: the closure identity holds for the _disembedded_ function too.

*Theorem:* the disembedded super-additive closure of a super-additive curve is itself

```lean
theorem superadditiveClosure_unbotD_eq
    (g : ℝ≥0 → ℝ≥0∞)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0)
    (t : ℝ≥0) :
    (superadditiveClosure (↑g) t).unbotD 0 = g t := by
  rw [superadditiveClosure_coe_eq_self g hsup h0]
  show (((g t : ℝ≥0∞) : WithBot ℝ≥0∞)).unbotD 0 = g t
  rw [WithBot.unbotD_coe]
```

The super-additive curves — pure delay, rate, rate-latency, and the
super-additive staircase — are then their own super-additive closures.
We state each in the disembedded form, back on
$`\overline{\mathbb{R}}_{\ge 0}`.

*Theorem:* $`(\delta_d)^{\overline{\star}} = \delta_d`

```lean
theorem delay_closure (d : ℝ≥0) (t : ℝ≥0) :
    (superadditiveClosure (↑(delay d)) t).unbotD 0
      = delay d t :=
  superadditiveClosure_unbotD_eq _
    (delay_superadditive d) (delay_zero_eq d) t
```

*Theorem:* $`(\lambda_R)^{\overline{\star}} = \lambda_R`

```lean
theorem rate_closure (R : ℝ≥0) (t : ℝ≥0) :
    (superadditiveClosure (↑(rate R)) t).unbotD 0
      = rate R t :=
  superadditiveClosure_unbotD_eq _
    (rate_superadditive R) (rate_zero_eq R) t
```

*Theorem:* $`(\beta_{R,T})^{\overline{\star}} = \beta_{R,T}`

```lean
theorem rateLatency_closure (R T : ℝ≥0) (t : ℝ≥0) :
    (superadditiveClosure (↑(rateLatency R T)) t).unbotD 0
      = rateLatency R T t :=
  superadditiveClosure_unbotD_eq _
    (rateLatency_superadditive R T)
    (rateLatency_zero_eq R T) t
```

*Theorem:* $`(\nu_{P,h,J})^{\overline{\star}} = \nu_{P,h,J}` for $`J < -P`

```lean
theorem staircase_closure_super (P h : ℝ≥0)
    (hP : (0:ℝ) < P) (J : ℝ) (hJ : J < -P) (t : ℝ≥0) :
    (superadditiveClosure (↑(staircase P h J)) t).unbotD 0
      = staircase P h J t :=
  superadditiveClosure_unbotD_eq _
    (staircase_superadditive P h hP J hJ)
    (staircase_zero_eq P h J) t
```

# Convolution and deconvolution by pure delays

For a non-decreasing curve `f`, convolving or deconvolving by a pure
delay $`\delta_d` is just a _time-shift_. Convolution shifts forward by
$`d` (clamped at the origin): $`(f \ast \delta_d)(t) = f([t - d]^{+})`.
The split $`u + s = t` with $`s \le d` contributes $`f(u)` (the delay is
$`0` there) with $`u = t - s \ge t - d`, so monotonicity makes
$`f(t - d)` the least; splits with $`s > d` give $`+\infty`.

*Theorem:* $`f \ast \delta_d = f([\,\cdot - d\,]^{+})`

```lean
theorem conv_delay (f : ℝ≥0 → ℝ≥0∞)
    (hf : Monotone f) (d : ℝ≥0) :
    minConvE f (delay d) = fun t => f (t - d) := by
  funext t
  unfold minConvE
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
```

The argument $`t - d` above is the _truncated_ subtraction on
$`\mathbb{R}_{\ge 0}` — it never goes below $`0` — so it is exactly the
non-negative part $`[t - d]^{+}`. Read into $`\mathbb{R}`, it is the
clamp $`\max(t - d, 0)`; hence `conv_delay`'s right-hand side $`f(t - d)`
genuinely computes $`f([t - d]^{+})`.

*Theorem:* $`\uparrow(t - d) = \max(t - d, 0)` — truncated subtraction is the non-negative part

```lean
theorem tsub_eq_posPart (t d : ℝ≥0) :
    ((t - d : ℝ≥0) : ℝ) = max ((t : ℝ) - d) 0 :=
  NNReal.coe_sub_def
```

*Theorem:* $`t - d = \lfloor \max(t - d, 0) \rfloor` as a non-negative real

```lean
theorem tsub_eq_toNNReal_max (t d : ℝ≥0) :
    (t - d) = (max ((t : ℝ) - d) 0).toNNReal := by
  apply NNReal.coe_injective
  rw [tsub_eq_posPart,
    Real.coe_toNNReal _ (le_max_right _ _)]
```

*Theorem:* $`f(t - d) = f([t - d]^{+})`

```lean
theorem conv_delay_posPart (f : ℝ≥0 → ℝ≥0∞) (t d : ℝ≥0) :
    f (t - d) = f ((max ((t : ℝ) - d) 0).toNNReal) := by
  rw [tsub_eq_toNNReal_max]
```

Deconvolution is the dual _(min,plus)_ quotient `minDeconvE` (the
function-dioids chapter), the numeric supremum over forward shifts of
$`f(t + s) - \delta_d(s)`. It shifts _backward_ by $`d`:
$`(f \oslash \delta_d)(t) = f(t + d)`. Where $`s \le d` the delay is
$`0`, leaving $`f(t + s) \le f(t + d)`; where $`s > d` the delay is
$`+\infty`, and the truncated difference floors to $`0`. The $`s = d`
term attains $`f(t + d)`.

*Theorem:* $`f \oslash \delta_d = f(\,\cdot + d\,)`

```lean
theorem deconv_delay (f : ℝ≥0 → ℝ≥0∞)
    (hf : Monotone f) (d : ℝ≥0) :
    minDeconvE f (delay d) = fun t => f (t + d) := by
  funext t
  unfold minDeconvE
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
```

# The closure of a deconvolution by a pure delay

For a _sub-additive_ non-decreasing `f`, the sub-additive closure of the
deconvolution $`f \oslash \delta_d` is the deconvolution itself capped by
$`\delta_0`: $`(f \oslash \delta_d)^{\star} = \delta_0 \wedge
(f \oslash \delta_d)`. The capped curve $`g = \delta_0 \wedge
(f \oslash \delta_d)` is sub-additive and null at the origin, so it is
its own closure; and it sits between the two lowest convolution powers
of $`f \oslash \delta_d` (the unit $`\delta_0` and $`f \oslash \delta_d`
itself), pinning the closure to it.

The capped curve is sub-additive: off the origin both arguments give
$`+\infty` for $`\delta_0`, leaving $`f(s + t + d) \le f(s + d) +
f(t + d)` from sub-additivity and monotonicity of `f`.

*Theorem:* $`\delta_0 \wedge (f \oslash \delta_d)` is sub-additive

```lean
theorem gdelay_subadd (f : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive f) (hmono : Monotone f)
    (d : ℝ≥0) :
    IsSubadditive (delay 0 ⊓ minDeconvE f (delay d)) := by
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
```

*Theorem:* $`(\delta_0 \wedge (f \oslash \delta_d))(0) = 0`

```lean
theorem gdelay_zero (f : ℝ≥0 → ℝ≥0∞)
    (hmono : Monotone f) (d : ℝ≥0) :
    (delay 0 ⊓ minDeconvE f (delay d)) 0 = 0 := by
  rw [deconv_delay f hmono d]
  show min (delay 0 0) (f (0 + d)) = 0
  rw [show delay 0 0 = (0:ℝ≥0∞) by simp [delay]]; simp
```

The pure delay $`\delta_0` lifts to the convolution unit `convUnit` of
the function dioid — the impulse — which is the $`n = 0` power, so the
closure lies below it.

*Theorem:* $`\uparrow\!\delta_0 = e` (the dioid unit)

```lean
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
```

*Theorem:* $`(f \oslash \delta_d)^{\star} = \delta_0 \wedge (f \oslash \delta_d)`

```lean
theorem deconv_delay_closure (f : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive f) (hmono : Monotone f)
    (d : ℝ≥0) :
    subadditiveClosureE (minDeconvE f (delay d))
      = delay 0 ⊓ minDeconvE f (delay d) := by
  set h : ℝ≥0 → ℝ≥0∞ := minDeconvE f (delay d) with hh
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
```

```lean
end DeepWiki
```
