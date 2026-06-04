import VersoManual
import Book.FunctionDioids

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Classes of usual functions" =>
Network calculus is built from a small repertoire of named curves: pure
delays, guaranteed rates, rate-latencies, token-buckets, staircases, and
a test function. Each is a real function $`\mathbb{R}^{+} \to \mathbb{R}
\cup \{+\infty\}`, so each lives in the _(min,plus)_ function dioid
$`\mathcal{F} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\min}`
(`FminBar`) of the previous chapter — ready to be convolved and ordered
by the dioid machinery. We collect their definitions here.

```lean
namespace VerifiedWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# Embedding real values

A curve assigns to each time $`t` an extended-real value. The finite
values are real numbers lifted into the carrier `WithTop (WithBot ℝ)`
through its two coercions, then wrapped in the `MinPlusExt` newtype; the
infinite value $`+\infty` is the carrier's top, wrapped likewise.

*Definition:* the embedding $`\uparrow r` of a real value into $`\overline{\mathbb{R}}_{\min}`

```lean
noncomputable def emb (r : ℝ) : MinPlusExt :=
  ⟨((r : WithBot ℝ) : WithTop (WithBot ℝ))⟩
```

*Definition:* the value $`+\infty` in $`\overline{\mathbb{R}}_{\min}`

```lean
noncomputable def pinf : MinPlusExt :=
  ⟨(⊤ : WithTop (WithBot ℝ))⟩
```

# The pure delay

The _pure delay_ $`\delta_d` lets everything through up to time $`d` and
blocks afterwards: it is $`0` for $`t \le d` and $`+\infty` beyond.

*Definition:* $`\delta_d(t) = 0` if $`t \le d`, else $`+\infty`

```lean
noncomputable def delay (d : ℝ≥0) : FminBar :=
  fun t => if t ≤ d then emb 0 else pinf
```

# The guaranteed rate

The _guaranteed rate_ $`\lambda_R` is the linear curve through the
origin with slope $`R`.

*Definition:* $`\lambda_R(t) = R\,t`

```lean
noncomputable def rate (R : ℝ≥0) : FminBar :=
  fun t => emb (R * t)
```

# The rate-latency

The _rate-latency_ $`\beta_{R,T}` stays at $`0` until the latency $`T`,
then rises at rate $`R`. The non-negative part $`[x]^{+} = x \vee 0`
clamps the pre-latency values to $`0`.

*Definition:* $`\beta_{R,T}(t) = R\,[t - T]^{+}`

```lean
noncomputable def rateLatency (R T : ℝ≥0) : FminBar :=
  fun t => emb (R * (max ((t : ℝ) - T) 0))
```

# The token-bucket

The _token-bucket_ $`\gamma_{r,b}` is the affine curve $`r\,t + b`
capped below by the pure delay at the origin, so that
$`\gamma_{r,b}(0) = 0`. The cap is the numeric minimum $`\wedge` of the
affine value and $`\delta_0(t)`.

*Definition:* $`\gamma_{r,b}(t) = (r\,t + b) \wedge \delta_0(t)`

```lean
noncomputable def tokenBucket (r b : ℝ≥0) : FminBar :=
  fun t =>
    ⟨min (emb (r * t + b)).toVal (delay 0 t).toVal⟩
```

# The staircase

The _staircase_ $`\nu_{P,h,J}` rises in steps of height $`h` every
period $`P`, with phase $`J`: at time $`t` it has taken
$`\lceil (t + J)/P \rceil` steps. Its value is the non-negative part of
$`h\,\lceil (t + J)/P \rceil`, again capped by the pure delay at the
origin.

*Definition:* $`\nu_{P,h,J}(t) = \bigl[h\,\lceil (t + J)/P \rceil\bigr]^{+} \wedge \delta_0(t)`

```lean
noncomputable def staircase (P h : ℝ≥0) (J : ℝ) : FminBar :=
  fun t =>
    ⟨min
      (emb (max (h * (⌈((t : ℝ) + J) / P⌉ : ℤ)) 0)).toVal
      (delay 0 t).toVal⟩
```

# The test function

The _test function_ $`\mathbb{1}_{>T}` is $`0` up to time $`T` and
$`1` afterwards.

*Definition:* $`\mathbb{1}_{>T}(t) = 0` if $`t \le T`, else $`1`

```lean
noncomputable def test (T : ℝ≥0) : FminBar :=
  fun t => if t ≤ T then emb 0 else emb 1
```

# Relations among the usual functions

The named curves are not independent: several coincide at special
parameter values, recovering the dioid neutrals and collapsing one
family onto another. We record these identities.

The pure delay at the origin _is_ the dioid unit $`e` (the convolution
unit $`\delta_0`): both are $`0` at $`t = 0` and $`+\infty` elsewhere.
(The companion fact $`\delta_d = \varepsilon` for $`d < 0` — the delay
collapsing to the dioid zero — is vacuous here: our domain takes
$`d \in \mathbb{R}^{+}`, so $`d < 0` does not occur.)

*Theorem:* $`\delta_0 = e`

```lean
theorem delay_zero : delay (0 : ℝ≥0) = convUnit := by
  funext t
  rcases eq_or_ne t 0 with h | h
  · subst h
    rw [delay, convUnit, if_pos le_rfl, if_pos rfl]
    apply MinPlusExt.ext; rfl
  · have ht : ¬ t ≤ 0 := by simpa using h
    rw [delay, convUnit, if_neg ht, if_neg h]
    apply MinPlusExt.ext; rfl
```

The guaranteed rate is the rate-latency with _zero latency_: with
$`T = 0` the clamp $`[t - 0]^{+} = t` is inert on $`\mathbb{R}^{+}`, so
$`\beta_{R,0} = \lambda_R`.

*Theorem:* $`\lambda_R = \beta_{R,0}`

```lean
theorem rate_eq_rateLatency_zero (R : ℝ≥0) :
    rate R = rateLatency R 0 := by
  funext t
  rw [rate, rateLatency]
  apply MinPlusExt.ext
  show _ = _
  congr 1
  rw [NNReal.coe_zero, sub_zero,
    max_eq_left t.coe_nonneg]
```

The guaranteed rate is also the token-bucket with _zero burst_: with
$`b = 0` the affine part is $`R\,t`, and the cap by $`\delta_0` only
forces the value at $`t = 0` down to $`0` — which $`R\,t` already is.

*Theorem:* $`\lambda_R = \gamma_{R,0}`

```lean
theorem rate_eq_tokenBucket_zero (R : ℝ≥0) :
    rate R = tokenBucket R 0 := by
  funext t
  rw [rate, tokenBucket]
  apply MinPlusExt.ext
  rcases eq_or_ne t 0 with h | h
  · subst h
    rw [delay, if_pos le_rfl]
    show (emb (R * 0)).toVal
        = min (emb (R*0+0)).toVal (emb 0).toVal
    unfold emb; norm_num
  · have ht : ¬ t ≤ 0 := by simpa using h
    rw [delay, if_neg ht]
    show (emb (R * t)).toVal
        = min (emb (R*t+0)).toVal pinf.toVal
    unfold emb pinf; rw [add_zero, min_top_right]
```

The test function $`\mathbb{1}_{>0}` is the token-bucket with zero rate
and unit burst: $`\gamma_{0,1}(t) = 1 \wedge \delta_0(t)`, which is $`0`
at the origin and $`1` afterwards.

*Theorem:* $`\mathbb{1}_{>0} = \gamma_{0,1}`

```lean
theorem test_zero_eq_tokenBucket :
    test (0 : ℝ≥0) = tokenBucket 0 1 := by
  funext t
  rw [test, tokenBucket]
  apply MinPlusExt.ext
  rcases eq_or_ne t 0 with h | h
  · subst h
    rw [if_pos le_rfl, delay, if_pos le_rfl]
    show (emb 0).toVal
        = min (emb (0*0+1)).toVal (emb 0).toVal
    unfold emb; norm_num
  · have ht : ¬ t ≤ 0 := by simpa using h
    rw [if_neg ht, delay, if_neg ht]
    show (emb 1).toVal
        = min (emb (0*t+1)).toVal pinf.toVal
    unfold emb pinf; norm_num [min_top_right]
```

Finally, the staircase $`\nu_{P,h,J}` is written $`\nu_{P,h}` when the
phase $`J` is null; unlike the other parameters $`J` ranges over all of
$`\mathbb{R}`, a positive value shifting the curve left and a negative
value shifting it right. This is a notational convention, not a
separate identity.

```lean
end VerifiedWiki
```
