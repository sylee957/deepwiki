import VersoManual
import Book.FunctionDioids
import Book.Limits
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Continuity" =>
Continuity is the special case of a one-sided limit (developed in the
previous chapter) where the limit _equals the value_: $`g` is continuous
from one side at $`t` when it tends to $`g(t)` along the corresponding
approach filter. We treat the two sides — left and right — symmetrically,
take `Mathlib`'s topological notion as the base definition, recover the
elementary $`\varepsilon`–$`\delta` form as the case $`L = g(t)` of
convergence-to-$`L`, and prove the two equivalent on each side. The
definitions hold for an _arbitrary_ `g`, including ones taking
$`+\infty`, with no monotonicity assumed. The only difference between the
two sides is the window — a left window $`(\delta, t)` versus a right
window $`(t, \delta)` — and the behaviour at the origin: the left window
is empty there, so left-continuity is vacuous, whereas the right window
never is. A cumulative function `f : Fmin` is covered through its values
$`s \mapsto (f\,s)`.

We then record _piecewise continuity_: continuous except at isolated
jumps, made precise as _locally finite_ discontinuities — on every
bounded initial interval $`[0, T]` only finitely many. We state it on
real functions $`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}` with its basic
closure facts; it feeds the curve class of the shaper chapters.

```lean
namespace DeepWiki

open Algebra Topology Filter Set
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# One-sided continuity

The base definition is `Mathlib`'s topological one: `g` is continuous
from the left at `t` when it tends to `g t` along the filter `𝓝[<] t` of
times approaching `t` from below — that is, `ContinuousWithinAt g
(Iio t) t` on the left ray $`(-\infty, t) = ` `Iio t`. This single limit
condition needs no case split: the neighborhoods of `g t` already know
how to be close to a finite value or to $`+\infty`. It depends only on
the codomain's topology, so we state it generically over any codomain
$`X` carrying a topology — covering both the extended-real curves
$`\mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}^\infty` and the
real-valued curves $`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}`.

*Definition:* $`g` is left-continuous at $`t` when it is `ContinuousWithinAt` on $`(-\infty, t)`

```lean
def IsLeftContinuousAt {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) (t : ℝ≥0) : Prop :=
  ContinuousWithinAt g (Iio t) t
```

The function is _left-continuous_ when this holds at every time.

*Definition:* $`g` is left-continuous when it is left-continuous at every $`t`

```lean
def IsLeftContinuous {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) : Prop :=
  ∀ t : ℝ≥0, IsLeftContinuousAt g t
```

At the origin the condition is automatic: the left ray is empty, so the
approach filter `𝓝[<] 0` is `⊥` and every function tends along it. No
positivity guard is therefore needed — left-continuity holds vacuously
at $`0`.

*Theorem:* every `g` is left-continuous at the origin

```lean
theorem isLeftContinuousAt_zero {X : Type*}
    [TopologicalSpace X] (g : ℝ≥0 → X) :
    IsLeftContinuousAt g 0 := by
  have hbot : 𝓝[Iio (0 : ℝ≥0)] 0 = ⊥ := by
    rw [show Set.Iio (0 : ℝ≥0) = ∅ by simp,
      nhdsWithin_empty]
  unfold IsLeftContinuousAt ContinuousWithinAt
  rw [hbot]
  exact tendsto_bot
```

A continuous function is left-continuous a fortiori: continuity at a
point restricts to continuity within any set, in particular the left
ray.

*Theorem:* a continuous function is left-continuous

```lean
theorem leftCont_of_continuous {X : Type*}
    [TopologicalSpace X] (g : ℝ≥0 → X)
    (hg : Continuous g) : IsLeftContinuous g :=
  fun t => hg.continuousAt.continuousWithinAt
```

The mirror notion is _right-continuity_: continuity from above, tending
to $`g t` along the right ray $`(t, \infty) = ` `Ioi t`. Unlike the left
side it carries no special behaviour at the origin — the right ray is
never empty — so the condition is a genuine constraint at every time.

*Definition:* $`g` is right-continuous at $`t` when it is `ContinuousWithinAt` on $`(t, \infty)`

```lean
def IsRightContinuousAt {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) (t : ℝ≥0) : Prop :=
  ContinuousWithinAt g (Ioi t) t
```

The function is _right-continuous_ when this holds at every time.

*Definition:* $`g` is right-continuous when it is right-continuous at every $`t`

```lean
def IsRightContinuous {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) : Prop :=
  ∀ t : ℝ≥0, IsRightContinuousAt g t
```

A continuous function is right-continuous a fortiori, by the same
restriction argument.

*Theorem:* a continuous function is right-continuous

```lean
theorem rightCont_of_continuous {X : Type*}
    [TopologicalSpace X] (g : ℝ≥0 → X)
    (hg : Continuous g) : IsRightContinuous g :=
  fun t => hg.continuousAt.continuousWithinAt
```

The two one-sided notions are not merely consequences of continuity —
together they _characterize_ it. Continuity at a point splits into
approach from below and approach from above, so a function continuous on
every left ray and every right ray is continuous everywhere, and
conversely. At the origin this still holds: the left ray is empty, so
left-continuity adds nothing there, and right-continuity at $`0` is
exactly continuity at $`0` (there is nothing to the left to approach
from).

*Theorem:* $`g` is continuous iff it is both left- and right-continuous

```lean
theorem continuous_iff_left_right
    {X : Type*} [TopologicalSpace X] (g : ℝ≥0 → X) :
    Continuous g ↔
      IsLeftContinuous g ∧ IsRightContinuous g := by
  rw [continuous_iff_continuousAt]
  unfold IsLeftContinuous IsRightContinuous
    IsLeftContinuousAt IsRightContinuousAt
  constructor
  · intro h
    exact ⟨fun t =>
        (continuousAt_iff_continuous_left'_right'.mp
          (h t)).1,
      fun t =>
        (continuousAt_iff_continuous_left'_right'.mp
          (h t)).2⟩
  · rintro ⟨hl, hr⟩ t
    exact continuousAt_iff_continuous_left'_right'.mpr
      ⟨hl t, hr t⟩
```

# The epsilon-delta form

The classical restatement is the elementary $`\varepsilon`–$`\delta`
form, specific to $`\overline{\mathbb{R}}_{\ge 0}^\infty`. It is the
convergence-to-a-value form of the previous chapter taken at the target
$`L = g(t)`, written out by cases on $`g(t)`: where $`g(t)` is finite the
values stay $`\varepsilon`-close (and finite), where it is $`+\infty`
they diverge. The finite clause reads the values through $`\mathbb{R}`
via the `realOf` reading from the Limits chapter.

These are _pointwise_ predicates at a time $`t`, by cases on $`g(t)`.
Left-continuity uses the left window $`(\delta, t)`.

*Definition:* $`g` is left-continuous (ε–δ) at $`t`, by cases on $`g(t)`

```lean
def IsLeftContinuousAtED
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : Prop :=
  (g t ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
      g s ≠ ⊤ ∧ |realOf g s - realOf g t| < ε) ∧
  (g t = ⊤ →
    ∀ M : ℝ≥0, ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
      (M : ℝ≥0∞) < g s)
```

Right-continuity is the mirror, on the right window $`(t, \delta)`.

*Definition:* $`g` is right-continuous (ε–δ) at $`t`, by cases on $`g(t)`

```lean
def IsRightContinuousAtED
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : Prop :=
  (g t ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
      g s ≠ ⊤ ∧ |realOf g s - realOf g t| < ε) ∧
  (g t = ⊤ →
    ∀ M : ℝ≥0, ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
      (M : ℝ≥0∞) < g s)
```

# Left-continuity: the two forms agree

The $`\varepsilon`–$`\delta` definition of left-continuity equals the
topological one — pointwise, at each $`t`. The clauses of
`IsLeftContinuousAtED` are, by cases on $`g(t)`, exactly the
finite/infinite convergence-to-$`g(t)` characterizations of the Limits
chapter, and convergence to $`g(t)` from the left _is_
`IsLeftContinuousAt g t`. The left window $`(\delta, t)` is empty at the
origin, so the equivalence carries a $`0 < t` hypothesis (at $`t = 0`
the ε–δ clause has no admissible $`\delta`, while left-continuity holds
vacuously).

*Theorem:* the $`\varepsilon`–$`\delta` and topological left-continuity agree, at $`t > 0`

```lean
theorem isLeftContinuousAtED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t) :
    IsLeftContinuousAtED g t ↔ IsLeftContinuousAt g t := by
  unfold IsLeftContinuousAtED IsLeftContinuousAt
  by_cases hfin : g t = ⊤
  · have hinf := infinite_tendstoLeftED_iff g t ht
    rw [show (⊤ : ℝ≥0∞) = g t from hfin.symm,
      show TendstoLeft g t (g t)
        = ContinuousWithinAt g (Iio t) t from rfl] at hinf
    rw [← hinf]
    constructor
    · rintro ⟨-, h⟩; exact h hfin
    · intro h
      exact ⟨fun hne => absurd hfin hne, fun _ => h⟩
  · have hf := finite_tendstoLeftED_iff g t ht (g t) hfin
    rw [show TendstoLeft g t (g t)
        = ContinuousWithinAt g (Iio t) t from rfl] at hf
    rw [← hf]
    constructor
    · rintro ⟨h, -⟩; exact h hfin
    · intro h
      exact ⟨fun _ => h, fun hT => absurd hT hfin⟩
```

# Right-continuity: the two forms agree

The right side is the same, on the right window $`(t, \delta)`. No
positivity guard is needed — the right window is nonempty at every time,
so the equivalence is unconditional.

*Theorem:* the $`\varepsilon`–$`\delta` and topological right-continuity agree

```lean
theorem isRightContinuousAtED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    IsRightContinuousAtED g t
      ↔ IsRightContinuousAt g t := by
  unfold IsRightContinuousAtED IsRightContinuousAt
  by_cases hfin : g t = ⊤
  · have hinf := infinite_tendstoRightED_iff g t
    rw [show (⊤ : ℝ≥0∞) = g t from hfin.symm,
      show TendstoRight g t (g t)
        = ContinuousWithinAt g (Ioi t) t from rfl] at hinf
    rw [← hinf]
    constructor
    · rintro ⟨-, h⟩; exact h hfin
    · intro h
      exact ⟨fun hne => absurd hfin hne, fun _ => h⟩
  · have hf := finite_tendstoRightED_iff g t (g t) hfin
    rw [show TendstoRight g t (g t)
        = ContinuousWithinAt g (Ioi t) t from rfl] at hf
    rw [← hf]
    constructor
    · rintro ⟨h, -⟩; exact h hfin
    · intro h
      exact ⟨fun _ => h, fun hT => absurd hT hfin⟩
```

# Continuity as convergence to the value

The whole point of one-sided continuity, in the convergence vocabulary
of the Limits chapter: $`g` is continuous from a side at $`t` exactly
when it converges _to its own value_ $`g(t)` from that side. Both
statements are definitional — `IsLeftContinuousAt g t` is literally
`TendstoLeft g t (g t)`, and likewise on the right — so the equivalences
are `rfl`. We record both, symmetrically.

*Theorem:* left-continuity at $`t` is convergence to $`g(t)` from the left

```lean
theorem tendstoLeft_value_iff_leftContinuousAt
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    TendstoLeft g t (g t)
      ↔ IsLeftContinuousAt g t := Iff.rfl
```

*Theorem:* right-continuity at $`t` is convergence to $`g(t)` from the right

```lean
theorem tendstoRight_value_iff_rightContinuousAt
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    TendstoRight g t (g t)
      ↔ IsRightContinuousAt g t := Iff.rfl
```

Globally: a left-continuous function converges to its value from the
left at every time, and a right-continuous one from the right.

*Theorem:* $`g` left-continuous $`\Rightarrow` it converges to $`g(t)` from the left

```lean
theorem tendstoLeft_value_of_leftContinuous
    (g : ℝ≥0 → ℝ≥0∞) (hlc : IsLeftContinuous g)
    (t : ℝ≥0) : TendstoLeft g t (g t) :=
  (hlc t).tendsto
```

*Theorem:* $`g` right-continuous $`\Rightarrow` it converges to $`g(t)` from the right

```lean
theorem tendstoRight_value_of_rightContinuous
    (g : ℝ≥0 → ℝ≥0∞) (hrc : IsRightContinuous g)
    (t : ℝ≥0) : TendstoRight g t (g t) :=
  (hrc t).tendsto
```

# Continuity versus the existence of a limit

It is tempting to expect "the one-sided limit exists everywhere" to be
equivalent to one-sided continuity, but that is _false_: a jump function
has both one-sided limits at every point yet is discontinuous, because
the limit need not _equal the value_. The correct characterization makes
that explicit — continuity at $`t` is the existence of a one-sided limit
together with its agreeing with $`g(t)`.

*Theorem:* $`g` is left-continuous at $`t` iff a left limit exists and equals $`g(t)`

```lean
theorem leftContinuousAt_iff_limit_eq_value
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    IsLeftContinuousAt g t
      ↔ ∃ L, TendstoLeft g t L ∧ L = g t := by
  constructor
  · intro h; exact ⟨g t, h, rfl⟩
  · rintro ⟨L, hL, rfl⟩; exact hL
```

*Theorem:* $`g` is right-continuous at $`t` iff a right limit exists and equals $`g(t)`

```lean
theorem rightContinuousAt_iff_limit_eq_value
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    IsRightContinuousAt g t
      ↔ ∃ L, TendstoRight g t L ∧ L = g t := by
  constructor
  · intro h; exact ⟨g t, h, rfl⟩
  · rintro ⟨L, hL, rfl⟩; exact hL
```

One direction is unconditional and dropping the value constraint: a
one-sided continuous function has a one-sided limit at every time (the
value itself witnesses it). The converse — existence everywhere implying
continuity — is the false implication above.

*Theorem:* $`g` left-continuous $`\Rightarrow` a left limit exists everywhere

```lean
theorem hasLeftLimit_of_leftContinuous
    (g : ℝ≥0 → ℝ≥0∞) (h : IsLeftContinuous g)
    (t : ℝ≥0) : ∃ L, TendstoLeft g t L :=
  ⟨g t, h t⟩
```

*Theorem:* $`g` right-continuous $`\Rightarrow` a right limit exists everywhere

```lean
theorem hasRightLimit_of_rightContinuous
    (g : ℝ≥0 → ℝ≥0∞) (h : IsRightContinuous g)
    (t : ℝ≥0) : ∃ L, TendstoRight g t L :=
  ⟨g t, h t⟩
```

# A positive right limit at the origin

A regularity used by the deviation results: the informal $`f(0^+) > 0`
means the function converges from the right at the origin to a value
that is strictly positive — there is an $`L` with $`f` tending to $`L`
along $`𝓝[>] 0` and $`0 < L`. Phrased as an existential over the
convergence value, it carries the convergence with it and needs no named
limit value.

A positive right limit forces $`f` to be positive on a whole
right-neighbourhood of the origin: eventually $`f` exceeds $`L`'s lower
neighbourhood, which gives an explicit threshold $`\delta`.

*Theorem:* $`f(0^+) > 0` makes $`f` positive on some $`(0, \delta)`

```lean
theorem pos_near_zero_of_rightLimit_pos
    (f : ℝ≥0 → ℝ≥0∞) (L : ℝ≥0∞)
    (hL : TendstoRight f 0 L) (hL0 : 0 < L) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t : ℝ≥0, 0 < t → t < δ → 0 < f t := by
  unfold TendstoRight at hL
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ≥0), 0 < f t :=
    hL.eventually (eventually_gt_nhds hL0)
  rw [eventually_nhdsWithin_iff,
    Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  refine ⟨⟨δ, hδ.le⟩, by exact_mod_cast hδ, ?_⟩
  intro t ht htδ
  apply hball (y := t)
  · rw [NNReal.dist_eq]
    simp only [NNReal.coe_zero, sub_zero,
      abs_of_nonneg t.coe_nonneg]
    exact_mod_cast htδ
  · exact ht
```

# Cumulative functions

A cumulative function `f : Fmin` is one-sided continuous when its values
are — that is, when the numeric reading $`s \mapsto (f\,s)` into
$`\overline{\mathbb{R}}_{\ge 0}^\infty` is. This specializes the
definitions to the dioid function space, requiring no separate
development.

*Definition:* the numeric reading of a cumulative function

```lean
noncomputable def numFn (f : Fmin) : ℝ≥0 → ℝ≥0∞ :=
  fun s => (f s : ℝ≥0∞)
```

*Definition:* a cumulative function is left-continuous via its values

```lean
def IsLeftContinuousF (f : Fmin) : Prop :=
  ∀ t : ℝ≥0, IsLeftContinuousAt (numFn f) t
```

*Definition:* a cumulative function is right-continuous via its values

```lean
def IsRightContinuousF (f : Fmin) : Prop :=
  ∀ t : ℝ≥0, IsRightContinuousAt (numFn f) t
```

# Piecewise continuity

We turn to _piecewise continuity_. The notion depends only on the
_topology_ of the codomain, so we state it once, generically over any
codomain $`X` carrying a topology — this covers both the real-valued
curves $`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}` and the extended-real
curves $`\mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}` (some curves
take the value $`+\infty`: a blocking delay, a saturating test function).
The codomain $`X` is any type carrying a topology, supplied inline at
each declaration.

The _discontinuity set_ of a function collects the points at which it
fails to be continuous — the raw material for the notion.

*Definition:* the discontinuity set $`\{\,t \mid g \text{ not continuous at } t\,\}`

```lean
def discontSet {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) : Set ℝ≥0 :=
  { t | ¬ ContinuousAt g t }
```

A function is _piecewise continuous_ when its discontinuity set is
locally finite: only finitely many discontinuities lie in any bounded
initial interval $`[0, T]`. Equivalently, the jumps do not accumulate.

*Definition:* $`g` is piecewise continuous when each $`[0, T]` holds finitely many jumps

```lean
def IsPiecewiseContinuous {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) : Prop :=
  ∀ T : ℝ≥0, (discontSet g ∩ Set.Icc 0 T).Finite
```

A continuous function has an empty discontinuity set, so trivially
finitely many jumps on every interval — one proof, valid for every
codomain.

*Theorem:* a continuous function is piecewise continuous

```lean
theorem isPiecewiseContinuous_of_continuous
    {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) (hg : Continuous g) :
    IsPiecewiseContinuous g := by
  intro T
  have hempty : discontSet g = ∅ := by
    ext t
    simp [discontSet, hg.continuousAt]
  rw [hempty, Set.empty_inter]
  exact Set.finite_empty
```

```lean
end DeepWiki
```
