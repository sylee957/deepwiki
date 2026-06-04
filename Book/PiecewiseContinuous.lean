import VersoManual
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.LeftRight

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Piecewise continuity" =>
The cumulative functions of network calculus are _piecewise
continuous_: continuous except at isolated jumps. Made precise, the
discontinuities are _locally finite_ — on every bounded initial
interval $`[0, T]` there are only finitely many. This chapter records
the notion on real functions $`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}`
and its basic closure facts; it feeds the curve class of the shaper
chapters.

```lean
namespace DeepWiki

open Topology Set
open scoped Classical NNReal ENNReal
```

# The discontinuity set

The _discontinuity set_ of a function collects the points at which it
fails to be continuous.

*Definition:* the discontinuity set $`\{\,t \mid g \text{ not continuous at } t\,\}`

```lean
def discontSet (g : ℝ≥0 → ℝ≥0) : Set ℝ≥0 :=
  { t | ¬ ContinuousAt g t }
```

# Piecewise continuity

A function is _piecewise continuous_ when its discontinuities are
locally finite: only finitely many lie in any bounded initial interval
$`[0, T]`. Equivalently, the jumps do not accumulate.

*Definition:* $`g` is piecewise continuous when each $`[0, T]` holds finitely many jumps

```lean
def IsPiecewiseContinuous (g : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ T : ℝ≥0, (discontSet g ∩ Set.Icc 0 T).Finite
```

# Continuous functions are piecewise continuous

A continuous function has an empty discontinuity set, so trivially
finitely many jumps on every interval.

*Theorem:* a continuous function is piecewise continuous

```lean
theorem isPiecewiseContinuous_of_continuous
    (g : ℝ≥0 → ℝ≥0) (hg : Continuous g) :
    IsPiecewiseContinuous g := by
  intro T
  have hempty : discontSet g = ∅ := by
    ext t
    simp [discontSet, hg.continuousAt]
  rw [hempty, Set.empty_inter]
  exact Set.finite_empty
```

In particular constant functions and the identity are piecewise
continuous.

*Theorem:* constant functions and the identity are piecewise continuous

```lean
theorem isPiecewiseContinuous_const (c : ℝ≥0) :
    IsPiecewiseContinuous (fun _ => c) :=
  isPiecewiseContinuous_of_continuous _ continuous_const

theorem isPiecewiseContinuous_id :
    IsPiecewiseContinuous (id : ℝ≥0 → ℝ≥0) :=
  isPiecewiseContinuous_of_continuous _ continuous_id
```

```lean
end DeepWiki
```
