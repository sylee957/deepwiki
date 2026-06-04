import VersoManual
import Book.LeftContinuity
import Book.PiecewiseContinuous

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
namespace VerifiedWiki

open scoped Classical NNReal ENNReal
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
$`\gamma_{r,b}(0) = 0`. The cap is the numeric minimum $`\wedge`.

*Definition:* $`\gamma_{r,b}(t) = (r\,t + b) \wedge \delta_0(t)`

```lean
noncomputable def tokenBucket (r b : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => min ((r : ℝ≥0∞) * t + b) (delay 0 t)
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

# Piecewise continuity

A curve is _piecewise continuous_ when its discontinuities are locally
finite: only finitely many lie in any bounded initial interval
$`[0, T]`. We state this for `ℝ≥0∞`-valued functions, mirroring the
$`\mathbb{R}_{\ge 0}`-valued notion of the piecewise-continuity chapter.

*Definition:* the discontinuity set of an $`\overline{\mathbb{R}}_{\ge 0}`-valued curve

```lean
def discontSetTop (g : ℝ≥0 → ℝ≥0∞) : Set ℝ≥0 :=
  { t | ¬ ContinuousAt g t }
```

*Definition:* $`g` is piecewise continuous when each $`[0, T]` holds finitely many jumps

```lean
def IsPwcTop (g : ℝ≥0 → ℝ≥0∞) : Prop :=
  ∀ T : ℝ≥0, (discontSetTop g ∩ Set.Icc 0 T).Finite
```

A continuous curve has an empty discontinuity set, so it is piecewise
continuous a fortiori.

*Theorem:* a continuous curve is piecewise continuous

```lean
theorem pwcTop_of_continuous (g : ℝ≥0 → ℝ≥0∞)
    (hg : Continuous g) : IsPwcTop g := by
  intro T
  have : discontSetTop g = ∅ := by
    ext t; simp [discontSetTop, hg.continuousAt]
  simp [this]
```

# Continuity of the rate and rate-latency

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
theorem rate_pwc (R : ℝ≥0) : IsPwcTop (rate R) :=
  pwcTop_of_continuous _ (rate_continuous R)
```

*Theorem:* $`\beta_{R,T}` is piecewise continuous

```lean
theorem rateLatency_pwc (R T : ℝ≥0) :
    IsPwcTop (rateLatency R T) :=
  pwcTop_of_continuous _ (rateLatency_continuous R T)
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
theorem delay_pwc (d : ℝ≥0) : IsPwcTop (delay d) := by
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
theorem test_pwc (T : ℝ≥0) : IsPwcTop (test T) := by
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
    IsPwcTop (tokenBucket r b) := by
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
    (hP : (0:ℝ) < P) : IsPwcTop (staircase P h J) := by
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
at every time. The continuous curves are left-continuous a fortiori; the
step and staircase curves jump _upward to the right_, so the left limit
agrees with the value, and they too are left-continuous.

*Theorem:* a continuous curve is left-continuous

```lean
theorem leftCont_of_continuous (g : ℝ≥0 → ℝ≥0∞)
    (hg : Continuous g) : IsLeftContinuousTop g :=
  fun t => hg.continuousAt.continuousWithinAt
```

*Theorem:* $`\lambda_R` is left-continuous

```lean
theorem rate_leftCont (R : ℝ≥0) :
    IsLeftContinuousTop (rate R) :=
  leftCont_of_continuous _ (rate_continuous R)
```

*Theorem:* $`\beta_{R,T}` is left-continuous

```lean
theorem rateLatency_leftCont (R T : ℝ≥0) :
    IsLeftContinuousTop (rateLatency R T) :=
  leftCont_of_continuous _ (rateLatency_continuous R T)
```

The pure delay is left-continuous: at $`t \le d` it is locally $`0`
below, and at $`t > d` the open interval $`(d, t)` lies just below $`t`,
on which it is constantly $`+\infty`.

*Theorem:* $`\delta_d` is left-continuous

```lean
theorem delay_leftCont (d : ℝ≥0) :
    IsLeftContinuousTop (delay d) := by
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
    IsLeftContinuousTop (test T) := by
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
    IsLeftContinuousTop (tokenBucket r b) := by
  intro t
  refine Filter.Tendsto.min ?_ (delay_leftCont 0 t)
  have h1 : ContinuousWithinAt
      (fun s : ℝ≥0 => (r:ℝ≥0∞) * s) (Iio t) t :=
    ((ENNReal.continuous_const_mul
      (by simp)).comp (by fun_prop)).continuousWithinAt
  exact h1.add continuousWithinAt_const
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
  simp only [rate, tokenBucket, ENNReal.coe_zero, add_zero]
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

```lean
end VerifiedWiki
```
