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

Deconvolution is the dual _(min,plus)_ quotient `deconv` (the
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
```

The deconvolution carries the non-decrease of its left argument across,
whatever the right argument: shifting both numerator terms forward by
the same amount keeps each $`f(x + s)` below $`f(y + s)`, and the
truncated difference and the supremum are both monotone. This is the
deconvolution entry of the $`\mathcal{F}^{\uparrow}` table — the
non-negativity entry is automatic, since values live in
$`\overline{\mathbb{R}}_{\ge 0}`, where every element is non-negative.

*Theorem:* $`g` non-decreasing $`\implies g \oslash h` non-decreasing

```lean
theorem minDeconvE_mono (g h : ℝ≥0 → ℝ≥0∞)
    (hg : Monotone g) : Monotone (deconv g h) := by
  intro x y hxy
  unfold deconv
  refine iSup_le (fun s => ?_)
  refine le_iSup_of_le s ?_
  have hxs : x + s ≤ y + s := by gcongr
  exact tsub_le_tsub_right (hg hxs) (h s)
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
```

*Theorem:* $`(\delta_0 \wedge (f \oslash \delta_d))(0) = 0`

```lean
theorem gdelay_zero (f : ℝ≥0 → ℝ≥0∞)
    (hmono : Monotone f) (d : ℝ≥0) :
    (delay 0 ⊓ deconv f (delay d)) 0 = 0 := by
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
```

# Catalog of convolutions

The named curves convolve into one another by simple parameter
arithmetic. Several of the identities are time-shifts (built on the
delay results), one is an infimum of linear functions, one is purely
compositional, and the last collapses to a pointwise minimum.

The delay and rate are non-decreasing — needed to apply the delay
time-shift results.

*Theorem:* $`\delta_d` is non-decreasing

```lean
theorem delay_mono (d : ℝ≥0) : Monotone (delay d) := by
  intro a b hab
  simp only [delay]
  split
  · exact bot_le
  · split
    · rename_i h1 h2; exact absurd (le_trans hab h2) h1
    · exact le_refl _
```

*Theorem:* $`\lambda_R` is non-decreasing

```lean
theorem rate_mono (R : ℝ≥0) : Monotone (rate R) := by
  intro a b hab; simp only [rate]; gcongr
```

Convolving two pure delays adds their delays: it is the delay-shift of a
delay.

*Theorem:* $`\delta_d \ast \delta_{d'} = \delta_{d + d'}`

```lean
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
```

The rate-latency is the delay-shift of the rate: $`\beta_{R,T} =
\delta_T \ast \lambda_R`.

*Theorem:* $`\beta_{R,T} = \delta_T \ast \lambda_R`

```lean
theorem rateLatency_eq_conv (R T : ℝ≥0) :
    rateLatency R T = minConv (delay T) (rate R) := by
  rw [minConvE_comm, conv_delay (rate R) (rate_mono R) T]
  funext t
  simp only [rate, rateLatency]
```

Convolving two rates takes the slower slope: the infimum of the two
linear functions over the splits is the line of minimal slope.

*Theorem:* $`\lambda_R \ast \lambda_{R'} = \lambda_{R \wedge R'}`

```lean
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
```

Convolving two rate-latencies combines both: the slopes meet (minimum)
and the latencies add. This is pure regrouping from the previous three —
$`\beta = \delta \ast \lambda`, then associativity/commutativity gather
the delays and the rates.

*Theorem:* $`\beta_{R,T} \ast \beta_{R',T'} = \beta_{R \wedge R',\ T + T'}`

```lean
theorem conv_rateLatency_rateLatency (R R' T T' : ℝ≥0) :
    minConv (rateLatency R T) (rateLatency R' T')
      = rateLatency (R ⊓ R') (T + T') := by
  rw [rateLatency_eq_conv R T, rateLatency_eq_conv R' T']
  rw [minConvE_assoc, ← minConvE_assoc (rate R),
      minConvE_comm (rate R) (delay T'),
      minConvE_assoc (delay T'), ← minConvE_assoc (delay T),
      conv_delay_delay, conv_rate_rate,
      rateLatency_eq_conv (R ⊓ R') (T + T')]
```

Convolving two token-buckets gives their pointwise minimum. By the
catalog engine `minConvE_eq_inf_of_subadd`, this reduces to showing the
minimum $`\gamma_{r,b} \wedge \gamma_{r',b'}` is sub-additive — which,
off the origin, is an affine-minimum inequality.

A four-way combinator: if $`\min(A, B)` is below each $`a_i + c_j`, it is
below $`\min(a_1, a_2) + \min(c_1, c_2)` (the achieved minimum is one of
the four sums).

*Theorem:* $`\min(A,B) \le \min(a_1, a_2) + \min(c_1, c_2)` from the four corner bounds

```lean
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
```

*Theorem:* the affine minimum is sub-additive

```lean
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
```

Off the origin the token-bucket is its affine part (the $`\delta_0` cap
is $`+\infty`), so the minimum of two token-buckets is the affine
minimum, which is sub-additive; at the origin both vanish.

*Theorem:* $`\gamma_{r,b}` at $`t \ne 0` is $`r\,t + b`

```lean
theorem tokenBucket_apply_pos (r b t : ℝ≥0)
    (ht : t ≠ 0) :
    tokenBucket r b t = (r:ℝ≥0∞) * t + b := by
  have h0 : ¬ t ≤ 0 := by simpa using ht
  simp only [tokenBucket, Pi.inf_apply, delay, if_neg h0,
    min_top_right]
```

*Theorem:* $`\gamma_{r,b} \wedge \gamma_{r',b'}` is sub-additive

```lean
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
```

*Theorem:* $`\gamma_{r,b} \ast \gamma_{r',b'} = \gamma_{r,b} \wedge \gamma_{r',b'}`

```lean
theorem conv_tokenBucket_tokenBucket (r b r' b' : ℝ≥0) :
    minConv (tokenBucket r b) (tokenBucket r' b')
      = tokenBucket r b ⊓ tokenBucket r' b' :=
  minConvE_eq_inf_of_subadd _ _
    (tokenBucket_zero_eq r b) (tokenBucket_zero_eq r' b')
    (tokenBucket_inf_subadd r b r' b')
```

# Catalog of deconvolutions

Deconvolution turns the catalog around. The _uncapped_ affine curve
$`\hat\gamma_{r,b}(t) = r\,t + b` — the token-bucket _without_ the
$`\delta_0` cap at the origin — is the natural shape for these
quotients, and recovers the token-bucket by re-imposing the cap:
$`\hat\gamma_{r,b} \wedge \delta_0 = \gamma_{r,b}`.

*Definition:* $`\hat\gamma_{r,b}(t) = r\,t + b`

```lean
noncomputable def affine (r b : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => (r:ℝ≥0∞) * t + b
```

Capping the uncapped affine with the burst delay $`\delta_0` is the
token-bucket — definitionally.

*Theorem:* $`\hat\gamma_{r,b} \wedge \delta_0 = \gamma_{r,b}`

```lean
theorem affine_inf_delay0 (r b : ℝ≥0) :
    affine r b ⊓ delay 0 = tokenBucket r b := rfl
```

Three bridge identities relating the named curves to the affine and
rate forms — used to specialise the master deconvolution below. The
uncapped affine with zero burst is the rate; the rate-latency with
zero latency is the rate; and the token-bucket with zero burst is the
rate (its $`\delta_0` cap is invisible because $`r\cdot 0 = 0`).

*Theorem:* $`\hat\gamma_{r,0} = \lambda_r`

```lean
theorem affine_zero (r : ℝ≥0) : affine r 0 = rate r := by
  funext t
  simp only [affine, rate, ENNReal.coe_zero, add_zero]
```

*Theorem:* $`\beta_{R,0} = \lambda_R`

```lean
theorem rateLatency_zero (R : ℝ≥0) :
    rateLatency R 0 = rate R := by
  funext t; simp only [rateLatency, rate, tsub_zero]
```

*Theorem:* $`\gamma_{R,0} = \lambda_R`

```lean
theorem tokenBucket_zero_rate (R : ℝ≥0) :
    tokenBucket R 0 = rate R := by
  funext t
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; rw [tokenBucket_zero_eq]; simp [rate]
  · rw [tokenBucket_apply_pos R 0 t ht]; simp [rate]
```

The token-bucket is non-decreasing — both its affine part and its cap
are — which is what the delay-shift quotient needs.

*Theorem:* $`\gamma_{r,b}` is non-decreasing

```lean
theorem tokenBucket_mono (r b : ℝ≥0) :
    Monotone (tokenBucket r b) := by
  intro a c hac
  simp only [tokenBucket, Pi.inf_apply]
  exact min_le_min (by gcongr) (delay_mono 0 hac)
```

## Deconvolutions by a pure delay

Deconvolving by a pure delay is a forward time-shift, so each quotient
by $`\delta_d` is the curve evaluated at $`t + d`. For two delays this
subtracts the delays (when $`d' \le d`, so the shift stays a delay).

*Theorem:* $`\delta_d \oslash \delta_{d'} = \delta_{d - d'}` for $`d' \le d`

```lean
theorem deconv_delay_delay (d d' : ℝ≥0) (h : d' ≤ d) :
    deconv (delay d) (delay d') = delay (d - d') := by
  rw [deconv_delay (delay d) (delay_mono d) d']
  funext t
  show (if t + d' ≤ d then (0:ℝ≥0∞) else ⊤)
      = delay (d - d') t
  simp only [delay]; congr 1; rw [le_tsub_iff_right h]
```

The rate shifts to an uncapped affine: the delay-shift of $`\lambda_R`
adds the burst $`R\,d`.

*Theorem:* $`\lambda_R \oslash \delta_d = \hat\gamma_{R, R d}`

```lean
theorem deconv_rate_delay (R d : ℝ≥0) :
    deconv (rate R) (delay d) = affine R (R * d) := by
  rw [deconv_delay (rate R) (rate_mono R) d]
  funext t; simp only [rate, affine]; push_cast; ring
```

The token-bucket shifts to an uncapped affine with the burst grown by
$`r\,d`. This needs $`0 < d`: at $`d = 0` the quotient is the
token-bucket itself, which is _capped_ at the origin and so differs
from the uncapped affine there.

*Theorem:* $`\gamma_{r,b} \oslash \delta_d = \hat\gamma_{r, b + r d}` for $`0 < d`

```lean
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
```

## Deconvolutions by a rate and a rate-latency

The remaining quotients are the master identity and its
specialisations. The engine is a one-sided affine bound: shifting an
uncapped affine forward by $`u` is dominated by re-burst-ing it and
adding the rate-latency service $`\beta_{R,T}` of any faster server.

*Theorem:* $`\hat\gamma_{r,b}(t + u) \le \hat\gamma_{r, b + r T}(t) + \beta_{R,T}(u)` for $`r \le R`

```lean
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
```

The token-bucket lies below its uncapped affine part everywhere.

*Theorem:* $`\gamma_{r,b}(t) \le \hat\gamma_{r,b}(t)`

```lean
theorem tokenBucket_le_affine (r b t : ℝ≥0) :
    tokenBucket r b t ≤ affine r b t := by
  simp only [tokenBucket, Pi.inf_apply, affine]
  exact min_le_left _ _
```

The master identity: deconvolving a token-bucket by a _faster_
rate-latency server gives the uncapped affine with burst grown by
$`r\,T`. The upper bound is the affine shift bound; the lower bound is
attained at the split $`s = T`, where the rate-latency vanishes. The
hypothesis $`0 < T` is genuine — at $`T = 0` the lower bound would have
to be attained only as a non-attained supremum at the origin, which is
the separate rate identity below.

*Theorem:* $`\gamma_{r,b} \oslash \beta_{R,T} = \hat\gamma_{r, b + r T}` for $`r \le R`, $`0 < T`

```lean
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
```

When the server is _slower_ than the burst rate ($`R < r`) the quotient
diverges: the deconvolution is $`+\infty` everywhere. The lower bound
$`(r - R)(u - T) \le \gamma_{r,b}(t+u) - \beta_{R,T}(u)` grows without
bound in $`u`, so the supremum is $`\top`.

*Theorem:* $`(r - R)(u - T) \le \gamma_{r,b}(t+u) - \beta_{R,T}(u)` for $`R \le r`, $`T \le u`

```lean
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
```

A linear function with positive slope has unbounded supremum.

*Theorem:* $`\sup_s c\,s = +\infty` for $`0 < c`

```lean
theorem iSup_coe_mul_eq_top (c : ℝ≥0) (hc : 0 < c) :
    (⨆ s : ℝ≥0, ((c * s : ℝ≥0):ℝ≥0∞)) = ⊤ := by
  rw [iSup_eq_top]; intro M hM
  lift M to ℝ≥0 using hM.ne with M'
  refine ⟨(M'/c) + 1, ?_⟩
  rw [ENNReal.coe_lt_coe,
    show c * (M'/c + 1) = (M'/c)*c + c by ring,
    div_mul_cancel₀ M' hc.ne']
  exact lt_add_of_le_of_pos le_rfl hc
```

*Theorem:* $`\gamma_{r,b} \oslash \beta_{R,T} = +\infty` for $`R < r`

```lean
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
```

Specialising the master to $`T = 0` would lose the $`0 < T`
hypothesis, so the rate quotient is proved directly. Its lower bound at
the origin is a genuine non-attained supremum: the split-terms
$`b - (R - r)\,s` approach the burst $`b` from below as $`s \to 0`, so
the supremum is $`b` even though no single split attains it.

*Theorem:* $`b \le \sup_s\,(\gamma_{r,b}(s) - \lambda_R(s))` for $`r \le R`

```lean
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
```

The affine shift bound at $`T = 0` is the upper bound for the rate
quotient.

*Theorem:* $`\hat\gamma_{r,b}(t + u) \le \hat\gamma_{r,b}(t) + \lambda_R(u)` for $`r \le R`

```lean
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
```

The token-bucket deconvolved by a _faster_ rate is the uncapped
affine: off the origin the split $`s = 0` attains it; at the origin the
supremum equals the burst as above.

*Theorem:* $`\gamma_{r,b} \oslash \lambda_R = \hat\gamma_{r,b}` for $`r \le R`

```lean
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
```

The other branch: a token-bucket deconvolved by a _slower_ rate
($`R < r`) diverges. It is the master divergence at zero latency,
since $`\beta_{R,0} = \lambda_R`.

*Theorem:* $`\gamma_{r,b} \oslash \lambda_R = +\infty` for $`R < r`

```lean
theorem deconv_tokenBucket_rate_top (r b R : ℝ≥0)
    (hRr : R < r) :
    deconv (tokenBucket r b) (rate R)
      = fun _ => (⊤:ℝ≥0∞) := by
  rw [← rateLatency_zero R]
  exact deconv_tokenBucket_rateLatency_top r b R 0 hRr
```

Finally the rate-by-rate quotient: a slower rate deconvolved by a
faster one is unchanged. It is the token-bucket identity at zero burst.

*Theorem:* $`\lambda_R \oslash \lambda_{R'} = \lambda_R` for $`R \le R'`

```lean
theorem deconv_rate_rate (R R' : ℝ≥0) (h : R ≤ R') :
    deconv (rate R) (rate R') = rate R := by
  conv_lhs => rw [← tokenBucket_zero_rate R]
  rw [deconv_tokenBucket_rate R 0 R' h, affine_zero]
```

And when the divisor rate is _slower_ ($`R' < R`) the quotient
diverges — the previous divergence at zero burst.

*Theorem:* $`\lambda_R \oslash \lambda_{R'} = +\infty` for $`R' < R`

```lean
theorem deconv_rate_rate_top (R R' : ℝ≥0) (h : R' < R) :
    deconv (rate R) (rate R')
      = fun _ => (⊤:ℝ≥0∞) := by
  conv_lhs => rw [← tokenBucket_zero_rate R]
  exact deconv_tokenBucket_rate_top R 0 R' h
```

# Horizontal and vertical deviations

Two scalar measures compare an arrival curve $`f` against a service
curve $`g`. The _horizontal deviation_ measures delay; the _vertical
deviation_ measures backlog. Both are the worst case over time.

The _horizontal deviation at_ $`t` is the smallest forward shift $`d`
that lets $`g` catch up to $`f(t)`: the infimum of those delays for
which $`f(t) \le g(t + d)`. We take it over the subtype of admissible
delays in $`\overline{\mathbb{R}}_{\ge 0}^\infty`. When $`g` never
catches up the admissible set is empty, and — since the infimum of the
empty set is the top element — the deviation is $`+\infty`, exactly the
intended "unbounded delay".

*Definition:* $`hDev(f, g, t) = \inf\,\{\, d \mid f(t) \le g(t + d)\,\}`

```lean
noncomputable def horizDevAt (f g : ℝ≥0 → ℝ≥0∞)
    (t : ℝ≥0) : ℝ≥0∞ :=
  ⨅ d : {d : ℝ≥0 // f t ≤ g (t + d)}, (d.1 : ℝ≥0∞)
```

When no delay suffices, the admissible subtype is empty and the
infimum is the top element $`+\infty`.

*Theorem:* $`hDev(f, g, t) = +\infty` when no $`d` satisfies $`f(t) \le g(t + d)`

```lean
theorem horizDevAt_eq_top (f g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0)
    (h : ∀ d : ℝ≥0, ¬ f t ≤ g (t + d)) :
    horizDevAt f g t = ⊤ := by
  unfold horizDevAt
  rw [iInf_eq_top]
  rintro ⟨d, hd⟩
  exact absurd hd (h d)
```

The _horizontal deviation_ is the worst of these over all times.

*Definition:* $`hDev(f, g) = \sup_{t \ge 0} hDev(f, g, t)`

```lean
noncomputable def hDev (f g : ℝ≥0 → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, horizDevAt f g t
```

The _vertical deviation_ is the worst gap $`f(t) - g(t)` over all
times.

*Definition:* $`vDev(f, g) = \sup_{t \ge 0}\,(f(t) - g(t))`

```lean
noncomputable def vDev (f g : ℝ≥0 → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, f t - g t
```

The vertical deviation is the deconvolution at the origin: at $`t = 0`
the deconvolution $`(f \oslash g)(0) = \sup_s\,(f(s) - g(s))` is
exactly the vertical-deviation supremum.

*Theorem:* $`vDev(f, g) = (f \oslash g)(0)`

```lean
theorem vDev_eq_deconv_zero (f g : ℝ≥0 → ℝ≥0∞) :
    vDev f g = deconv f g 0 := by
  unfold vDev deconv
  simp only [zero_add]
```

## Horizontal deviation against a pure delay

The horizontal deviation of any curve against a pure delay $`\delta_d`
is bounded by $`d`, and equals $`d` exactly when the curve is positive
off the origin. Both halves rest on the shape of $`\delta_d`: it is
$`0` up to $`d` and $`+\infty` beyond.

Past $`d` the delay is $`+\infty`, which dominates any value — so any
shift carrying the argument beyond $`d` is admissible.

*Theorem:* $`\delta_d(t + u) = +\infty` when $`d < t + u`

```lean
theorem delay_top_of_gt (d t u : ℝ≥0) (h : d < t + u) :
    delay d (t + u) = ⊤ := by
  simp only [delay, if_neg (not_le.mpr h)]
```

At each time the deviation against $`\delta_d` is at most $`d`: every
shift $`d + \varepsilon` carries $`t + (d + \varepsilon)` past $`d`,
where $`\delta_d` is $`+\infty` and so dominates $`f(t)`; that shift is
admissible, so the infimum is at most $`d + \varepsilon`, hence at most
$`d`.

*Theorem:* $`hDev(f, \delta_d, t) \le d`

```lean
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
```

The horizontal deviation, as the supremum over time, inherits the
bound. This is the first statement.

*Theorem:* $`hDev(f, \delta_d) \le d`

```lean
theorem hDev_delay_le (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0) :
    hDev f (delay d) ≤ d := by
  unfold hDev
  exact iSup_le (fun t => horizDevAt_delay_le f d t)
```

For the lower bound, suppose $`f(t) > 0`. Below $`d` the delay is
$`0`, so a shift with $`t + d' < d` would force $`f(t) \le 0`,
impossible. Hence every admissible shift has $`d' \ge d - t`, and the
deviation at $`t` is at least $`d - t`.

*Theorem:* $`d - t \le hDev(f, \delta_d, t)` when $`f(t) > 0`

```lean
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
```

When $`f` is positive everywhere off the origin the deviation is
_exactly_ $`d`. We first prove this stronger pointwise form — it
suffices that $`f(t) > 0` for all $`t > 0` — which is the engine; the
faithful right-limit statement follows from it below. Taking the
deviation at the small time $`\varepsilon` gives
$`hDev \ge d - \varepsilon`, and letting $`\varepsilon \to 0` closes
the gap to the upper bound.

*Theorem:* $`hDev(f, \delta_d) = d` when $`f(t) > 0` for all $`t > 0`

```lean
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
```

The statement as usually given asks only for the _right limit_
$`f(0^+) > 0`, weaker than positivity at every $`t > 0`. Both readings
go through the same engine: any positivity _window_ $`(0, \delta)` pins
the deviation to $`d`. We extract that engine once — the lower bound is
taken at a small time $`s = \min(\varepsilon, \delta/2)` inside the
window, so the same $`\varepsilon \to 0` argument as the pointwise form
applies.

*Theorem:* $`hDev(f, \delta_d) = d` given a positivity window $`(0, \delta)`

```lean
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
```

The faithful hypothesis is exactly $`f(0^+) > 0`: a value $`L` to which
$`f` converges from the right at the origin, with $`0 < L`. The
convergence yields the positivity window — no assumption that $`L` equals
$`f(0)`, so a jump at the origin is allowed. This is the form the
token-bucket needs.

*Theorem:* $`hDev(f, \delta_d) = d` when $`f(0^+) > 0`

```lean
theorem hDev_delay_eq_of_rightLimit_pos
    (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0) (L : ℝ≥0∞)
    (hL : TendstoRight f 0 L) (hL0 : 0 < L) :
    hDev f (delay d) = d :=
  hDev_delay_eq_of_pos_window f d
    (pos_near_zero_of_rightLimit_pos f L hL hL0)
```

Right-continuity with a positive value at the origin is the clean
special case: it converges from the right to $`f(0)`, so $`0 < f(0)`
supplies both the witness and the positivity. (The token-bucket is _not_
of this form — it is capped to $`0` at the origin and jumps — so it uses
the right-limit statement above directly.)

*Theorem:* $`hDev(f, \delta_d) = d` when $`f` is right-continuous with $`0 < f(0)`

```lean
theorem hDev_delay_eq_of_rightCont
    (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0)
    (hrc : IsRightContinuous f) (h0 : 0 < f 0) :
    hDev f (delay d) = d :=
  hDev_delay_eq_of_rightLimit_pos f d (f 0)
    (hrc 0).tendsto h0
```

# Catalog of deviations

The deviations of the named curves follow from the two engines above:
the horizontal deviation against a delay (the previous section) and the
identity $`vDev(f, g) = (f \oslash g)(0)` composed with the
deconvolution catalog. The vertical deviations are immediate corollaries
of that identity; the horizontal one against a delay needs the
token-bucket's positive right limit.

The token-bucket has right limit $`b` at the origin: off the origin it
agrees with the continuous affine $`r\,t + b`, which tends to $`b` as
$`t \to 0^+`. So a positive burst $`b` gives a positive right limit.

*Theorem:* $`\gamma_{r,b}` converges from the right to $`b` at the origin

```lean
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
```

The token-bucket has a positive burst right limit, so its horizontal
deviation against a pure delay is exactly the delay — independent of
$`r` and $`b`. The token-bucket is _not_ right-continuous at the origin
(it is capped to $`0` there but jumps up to $`b`), so it uses the right
_limit_ statement: it converges from the right to $`b` at the origin,
positive when $`0 < b`. (With $`b = 0` the limit is $`0` and the
statement does not apply.)

*Theorem:* $`hDev(\gamma_{r,b}, \delta_d) = d` for $`0 < b`

```lean
theorem hDev_tokenBucket_delay (r b d : ℝ≥0)
    (hb : 0 < b) :
    hDev (tokenBucket r b) (delay d) = d :=
  hDev_delay_eq_of_rightLimit_pos (tokenBucket r b) d
    (b:ℝ≥0∞) (tokenBucket_tendsto_right r b)
    (by exact_mod_cast hb)
```

## Horizontal deviation against a rate-latency

The horizontal deviation of a token-bucket against a rate-latency
$`\beta_{R,T}` is $`T + b/R` when the server is fast enough
($`r \le R`), and $`+\infty` when it is too slow ($`R < r`). This one is
a _direct_ horizontal-deviation computation (not a corollary of the
deconvolution catalog): the admissible delays at time $`t` are those $`d`
with $`\gamma_{r,b}(t) \le \beta_{R,T}(t + d)`, i.e. (off the origin)
$`r\,t + b \le R\,[t + d - T]^{+}`. We need $`0 < R` (for $`b/R`) and
$`0 < b` (with $`b = 0` and $`r = 0` the curve is flat and the deviation
is $`0`, not $`T`).

The admissibility condition, read on the numeric values: off the origin
$`\gamma_{r,b}(t) \le \beta_{R,T}(t+d)` is $`r\,t + b \le R\,((t+d) - T)`.

*Theorem:* $`\beta`-admissibility unfolds to a numeric inequality

```lean
theorem rateLatency_coe' (R T u : ℝ≥0) :
    rateLatency R T u = ((R*(u-T):ℝ≥0):ℝ≥0∞) := by
  simp only [rateLatency]; push_cast; ring

theorem beta_admissible_imp
    (r b R T t d : ℝ≥0) (ht : t ≠ 0)
    (h : tokenBucket r b t ≤ rateLatency R T (t+d)) :
    (r*t+b : ℝ≥0) ≤ R*((t+d)-T) := by
  rw [tokenBucket_apply_pos r b t ht, rateLatency_coe',
    show (r:ℝ≥0∞)*t+b = ((r*t+b:ℝ≥0):ℝ≥0∞)
      by push_cast; ring,
    ENNReal.coe_le_coe] at h
  exact h
```

For the upper bound, the fixed shift $`d^\* = T + b/R` is admissible at
_every_ time when $`r \le R`: it makes $`R((t+d^\*)-T) = R\,t + b \ge
r\,t + b`. So the deviation is at most $`T + b/R`.

*Theorem:* $`d^\* = T + b/R` is admissible at every $`t`

```lean
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
```

For the lower bound, every admissible $`d` at $`t` satisfies
$`R\,T + b \le R\,d + (R - r)\,t` (rearranging the admissibility
inequality; positivity of $`b` rules out the degenerate branch where the
shifted argument falls below $`T`).

*Theorem:* admissible $`d` obeys $`R\,T + b \le R\,d + (R - r)\,t`

```lean
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
```

Dividing by $`R`, the deviation at $`t` is at least
$`(T + b/R) - ((R-r)/R)\,t`.

*Theorem:* $`(T + b/R) - ((R-r)/R)\,t \le hDev(\gamma_{r,b}, \beta_{R,T}, t)`

```lean
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
```

As $`t \to 0^{+}` the lower bound approaches $`T + b/R`, so the
supremum reaches it: for every $`\varepsilon`, a small enough time
witnesses $`hDev \ge (T + b/R) - \varepsilon`.

*Theorem:* $`T + b/R \le hDev(\gamma_{r,b}, \beta_{R,T})`

```lean
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
```

Combining the bounds gives the main identity for the fast-server case.

*Theorem:* $`hDev(\gamma_{r,b}, \beta_{R,T}) = T + b/R` for $`r \le R`

```lean
theorem hDev_tokenBucket_rateLatency (r b R T : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hrR : r ≤ R) :
    hDev (tokenBucket r b) (rateLatency R T)
      = ((T + b/R : ℝ≥0):ℝ≥0∞) :=
  le_antisymm
    (hDev_tokenBucket_rateLatency_le r b R T hR hrR)
    (hDev_tokenBucket_rateLatency_ge r b R T hR hb)
```

When the server is too slow ($`R < r`), the admissible delays grow with
$`t`: every admissible $`d` obeys $`(r - R)\,t \le R\,d`, so the
deviation at $`t` is at least $`((r-R)/R)\,t`, whose supremum is
$`+\infty`.

*Theorem:* admissible $`d` obeys $`(r - R)\,t \le R\,d` when $`R < r`

```lean
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
```

*Theorem:* $`hDev(\gamma_{r,b}, \beta_{R,T}) = +\infty` for $`R < r`

```lean
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
```

The vertical deviation against a delay is the deconvolution at the
origin: $`(\gamma_{r,b} \oslash \delta_d)(0) = \hat\gamma_{r,b+rd}(0)
= r\,d + b`. This needs $`0 < d` (the underlying deconvolution
identity does).

*Theorem:* $`vDev(\gamma_{r,b}, \delta_d) = r\,d + b` for $`0 < d`

```lean
theorem vDev_tokenBucket_delay (r b d : ℝ≥0)
    (hd : 0 < d) :
    vDev (tokenBucket r b) (delay d)
      = (r*d + b : ℝ≥0) := by
  rw [vDev_eq_deconv_zero,
    deconv_tokenBucket_delay r b d hd]
  simp only [affine, ENNReal.coe_zero, mul_zero,
    zero_add]
  push_cast; ring
```

Likewise against a rate-latency, when the server is fast enough: the
deconvolution at the origin is $`\hat\gamma_{r, b + rT}(0) = r\,T + b`.

*Theorem:* $`vDev(\gamma_{r,b}, \beta_{R,T}) = r\,T + b` for $`r \le R`, $`0 < T`

```lean
theorem vDev_tokenBucket_rateLatency (r b R T : ℝ≥0)
    (h : r ≤ R) (hT : 0 < T) :
    vDev (tokenBucket r b) (rateLatency R T)
      = (r*T + b : ℝ≥0) := by
  rw [vDev_eq_deconv_zero,
    deconv_tokenBucket_rateLatency r b R T h hT]
  simp only [affine, ENNReal.coe_zero, mul_zero,
    zero_add]
  push_cast; ring
```

When the server is too slow the backlog is unbounded: the
deconvolution diverges, so the vertical deviation is $`+\infty`.

*Theorem:* $`vDev(\gamma_{r,b}, \beta_{R,T}) = +\infty` for $`R < r`

```lean
theorem vDev_tokenBucket_rateLatency_top
    (r b R T : ℝ≥0) (hRr : R < r) :
    vDev (tokenBucket r b) (rateLatency R T) = ⊤ := by
  rw [vDev_eq_deconv_zero,
    deconv_tokenBucket_rateLatency_top r b R T hRr]
```

```lean
end DeepWiki
```
