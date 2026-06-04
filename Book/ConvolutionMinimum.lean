import VersoManual
import Book.Subadditivity
import Book.Continuity
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Instances.NNReal.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The convolution attains its minimum" =>
The $`(\min, +)` convolution is an _infimum_ over a continuum of
splits,
$$`(g \ast h)(t) = \inf_{0 \le u \le t}\,\bigl(g(u) + h(t - u)\bigr),`
so a priori it need not be _attained_ at any single split. For the
cumulative functions of network calculus — monotone and
left-continuous — it is: the minimum is reached. The argument is the
extreme value theorem in its lower-semicontinuous form. A monotone
left-continuous function is _lower semicontinuous_; the split-map
$`u \mapsto g(u) + h(t - u)` is then lower semicontinuous on the
_compact_ interval $`[0, t]`, where a lower-semicontinuous function
attains its infimum.

```lean
namespace DeepWiki

open Topology Filter Set
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# Monotone left-continuous implies lower semicontinuous

A monotone function that is left-continuous is lower semicontinuous:
splitting a neighbourhood of `t` into its left and right parts, the
left part tends to `g(t)` by left-continuity, and on the right the
values only increase by monotonicity, so they stay above any threshold
below `g(t)`. We use the topological form `IsLeftContinuous`.

*Theorem:* a monotone, left-continuous function is lower semicontinuous

```lean
theorem lowerSemicontinuous_of_mono_leftCont
    (g : ℝ≥0 → ℝ≥0∞) (hmono : Monotone g)
    (hlc : IsLeftContinuous g) :
    LowerSemicontinuous g := by
  intro t y hy
  rw [← nhdsLT_sup_nhdsGE t, eventually_sup]
  refine ⟨(hlc t).eventually (Ioi_mem_nhds hy), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact lt_of_lt_of_le hy (hmono hz)
```

# The split-map is lower semicontinuous on the interval

The convolution at `t` is the infimum, over $`u \in [0, t]`, of the
_split-map_ $`u \mapsto g(u) + h(t - u)`. With `g` and `h` lower
semicontinuous, this map is lower semicontinuous: `g` is, and
$`u \mapsto h(t - u)` is a lower-semicontinuous function composed with
the continuous subtraction $`u \mapsto t - u`; a sum of lower
semicontinuous functions is lower semicontinuous.

*Definition:* the split-map $`u \mapsto g(u) + h(t - u)`

```lean
noncomputable def splitMap
    (g h : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun u => g u + h (t - u)
```

*Theorem:* the split-map is lower semicontinuous

```lean
theorem lowerSemicontinuous_splitMap
    (g h : ℝ≥0 → ℝ≥0∞)
    (hg : LowerSemicontinuous g)
    (hh : LowerSemicontinuous h) (t : ℝ≥0) :
    LowerSemicontinuous (splitMap g h t) := by
  have hsub : Continuous (fun u : ℝ≥0 => t - u) := by
    continuity
  exact hg.add (hh.comp hsub)
```

# Attainment on the compact interval

The interval $`[0, t]` is compact and nonempty, and the split-map is
lower semicontinuous on it, so by the extreme value theorem the
minimum is attained: there is a split $`u_0 \in [0, t]` at which the
split-map is least.

*Theorem:* the split-map attains its minimum on $`[0, t]`

```lean
theorem exists_isMinOn_splitMap
    (g h : ℝ≥0 → ℝ≥0∞)
    (hg : LowerSemicontinuous g)
    (hh : LowerSemicontinuous h) (t : ℝ≥0) :
    ∃ u ∈ Set.Icc (0 : ℝ≥0) t,
      IsMinOn (splitMap g h t) (Set.Icc 0 t) u :=
  LowerSemicontinuousOn.exists_isMinOn ⟨0, by simp⟩
    isCompact_Icc
    ((lowerSemicontinuous_splitMap g h hg hh t)
      |>.lowerSemicontinuousOn _)
```

For monotone left-continuous curves the lower-semicontinuity
hypotheses are met, so the convolution minimum is attained — the
infimum over the splits is a genuine minimum.

*Theorem:* for monotone left-continuous curves the convolution minimum is attained

```lean
theorem exists_isMinOn_splitMap_of_curves
    (g h : ℝ≥0 → ℝ≥0∞)
    (hgm : Monotone g) (hhm : Monotone h)
    (hgc : IsLeftContinuous g)
    (hhc : IsLeftContinuous h) (t : ℝ≥0) :
    ∃ u ∈ Set.Icc (0 : ℝ≥0) t,
      IsMinOn (splitMap g h t) (Set.Icc 0 t) u :=
  exists_isMinOn_splitMap g h
    (lowerSemicontinuous_of_mono_leftCont g hgm hgc)
    (lowerSemicontinuous_of_mono_leftCont h hhm hhc) t
```

# Monotonicity of the convolution

For the record, the (min,plus) convolution `minConvE` of two monotone
functions is monotone — a fact independent of attainment, used
wherever the convolution is treated as a cumulative function.

*Theorem:* $`g \ast h` is monotone when $`g, h` are

```lean
theorem minConvE_mono (g h : ℝ≥0 → ℝ≥0∞)
    (hg : Monotone g) (hh : Monotone h) :
    Monotone (minConvE g h) := by
  intro a b hab
  unfold minConvE
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, (hus : u + s = b)⟩
  by_cases hua : u ≤ a
  · refine iInf_le_of_le
      ⟨(u, a - u), by rw [add_tsub_cancel_of_le hua]⟩ ?_
    show g u + h (a - u) ≤ g u + h s
    gcongr
    have hb : b - u = s := by
      rw [← hus, add_comm u s, add_tsub_cancel_right]
    exact hb ▸ hh (by gcongr)
  · refine iInf_le_of_le ⟨(a, 0), by rw [add_zero]⟩ ?_
    show g a + h 0 ≤ g u + h s
    gcongr
    · exact hg (not_le.mp hua).le
    · exact hh bot_le
```

```lean
end DeepWiki
```
