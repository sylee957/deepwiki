import VersoManual
import Book.FunctionDioids
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Continuity" =>
The cumulative functions of network calculus carry two regularity
notions, both properties of the _values_ alone (not of the dioid
structure), stated on functions valued in the non-negative reals —
where `Mathlib`'s order topology lives.

First, _one-sided continuity_ — left and right, treated symmetrically.
Left-continuity is the regularity that keeps shaped and convolved
outputs well-defined; right-continuity is its mirror. We take
`Mathlib`'s topological notion as the base definition, give the
elementary $`\varepsilon`–$`\delta` form as the classical restatement,
and prove the two equivalent on each side; the definitions hold for an
_arbitrary_ `g`, including ones taking $`+\infty`, with no monotonicity
assumed. The only difference between the two sides is the window — a
left window $`(\delta, t)` versus a right window $`(t, \delta)` — and
the behaviour at the origin: the left window is empty there, so
left-continuity is vacuous, whereas the right window never is. A
cumulative function `f : Fmin` is covered through its values
$`s \mapsto (f\,s)`.

Second, _piecewise continuity_: continuous except at isolated jumps,
made precise as _locally finite_ discontinuities — on every bounded
initial interval $`[0, T]` only finitely many. We record it on real
functions $`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}` with its basic
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

*Definition:* $`g` is left-continuous when it is `ContinuousWithinAt` on $`(-\infty, t)`

```lean
def IsLeftContinuous {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) : Prop :=
  ∀ t : ℝ≥0, ContinuousWithinAt g (Iio t) t
```

At the origin the condition is automatic: the left ray is empty, so the
approach filter `𝓝[<] 0` is `⊥` and every function tends along it. No
positivity guard is therefore needed — left-continuity holds vacuously
at $`0`.

*Theorem:* every `g` is left-continuous at the origin

```lean
theorem continuousWithinAt_Iio_zero (g : ℝ≥0 → ℝ≥0∞) :
    ContinuousWithinAt g (Iio 0) 0 := by
  have hbot : 𝓝[Iio (0 : ℝ≥0)] 0 = ⊥ := by
    rw [show Set.Iio (0 : ℝ≥0) = ∅ by simp,
      nhdsWithin_empty]
  unfold ContinuousWithinAt
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

*Definition:* $`g` is right-continuous when it is `ContinuousWithinAt` on $`(t, \infty)`

```lean
def IsRightContinuous {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) : Prop :=
  ∀ t : ℝ≥0, ContinuousWithinAt g (Ioi t) t
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
form, specific to $`\overline{\mathbb{R}}_{\ge 0}^\infty`. One-sided
continuity at `t` splits by cases on `g t`, on a one-sided window — an
open interval of times just before `t` (for the left) or just after (for
the right). Where `g t` is _finite_, on a small enough window the values
are _finite_ and stay $`\varepsilon`-close to `g t`; the finiteness is
part of the clause, so a stray $`+\infty` adjacent to `t` correctly
breaks it rather than being read as a real number. Where `g t` is
$`+\infty`, the values must _diverge_ to $`+\infty`: every finite
threshold `M` is eventually exceeded. The finite clause reads the values
through `ℝ` via `toReal`.

*Definition:* the real reading $`s \mapsto g(s)` into $`\mathbb{R}`

```lean
noncomputable def realOf (g : ℝ≥0 → ℝ≥0∞) : ℝ≥0 → ℝ :=
  fun s => (g s).toReal
```

Left-continuity uses the left window $`(\delta, t)`.

*Definition:* $`g` is left-continuous (ε–δ), by cases on $`g(t)`

```lean
def IsLeftContinuousED (g : ℝ≥0 → ℝ≥0∞) : Prop :=
  ∀ t : ℝ≥0, 0 < t →
    (g t ≠ ⊤ →
      ∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        g s ≠ ⊤ ∧ |realOf g s - realOf g t| < ε) ∧
    (g t = ⊤ →
      ∀ M : ℝ≥0, ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        (M : ℝ≥0∞) < g s)
```

The origin is excluded: there is nothing strictly before it, so the
condition constrains only `t > 0`.

Right-continuity is the mirror, on the right window $`(t, \delta)`. No
positivity guard is needed — the right window is nonempty at every time,
including the origin.

*Definition:* $`g` is right-continuous (ε–δ), by cases on $`g(t)`

```lean
def IsRightContinuousED (g : ℝ≥0 → ℝ≥0∞) : Prop :=
  ∀ t : ℝ≥0,
    (g t ≠ ⊤ →
      ∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        g s ≠ ⊤ ∧ |realOf g s - realOf g t| < ε) ∧
    (g t = ⊤ →
      ∀ M : ℝ≥0, ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        (M : ℝ≥0∞) < g s)
```

# Left-continuity: the two forms agree

We prove the $`\varepsilon`–$`\delta` definition equals the topological
one, one case at a time on the left-window basis
$`\{(\delta, t) \mid \delta < t\}` of `𝓝[<] t`. Both directions hold
for an arbitrary `g`. The right side, proved in the same shape on the
right-window basis of `𝓝[>] t`, follows in the next section.

The auxiliary form drops the finiteness conjunct, expressing only the
$`\varepsilon`-closeness of the _real_ reading.

*Theorem:* the bare $`\varepsilon`-closeness clause is left-continuity of the real reading

```lean
theorem real_close_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t) :
    (∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        |realOf g s - realOf g t| < ε)
      ↔ ContinuousWithinAt (realOf g) (Iio t) t := by
  have hbasis : (𝓝[<] t).HasBasis (· < t) (Ioo · t) :=
    nhdsLT_basis_of_exists_lt ⟨0, ht⟩
  unfold ContinuousWithinAt
  rw [hbasis.tendsto_iff Metric.nhds_basis_ball]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδt, hδ⟩ := h ε hε
    refine ⟨δ, hδt, fun s hs => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact hδ s hs
  · intro h ε hε
    obtain ⟨δ, hδt, hδ⟩ := h ε hε
    refine ⟨δ, hδt, fun s hs => ?_⟩
    have := hδ s hs
    rwa [Metric.mem_ball, Real.dist_eq] at this
```

In the _finite_ case, the full clause — finiteness together with
closeness — is exactly left-continuity at `t`. The forward direction
rebuilds `g` as $`\uparrow\!(\cdot)` of its real reading on a window
where the values are finite; the backward direction reads off
finiteness from convergence to a finite value (the values eventually
avoid $`+\infty`) and closeness from continuity of `toReal`.

*Theorem:* at a finite point, the finite $`\varepsilon`–$`\delta` clause is left-continuity

```lean
theorem finite_ed_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t)
    (hfin : g t ≠ ⊤) :
    (∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        g s ≠ ⊤ ∧ |realOf g s - realOf g t| < ε)
      ↔ ContinuousWithinAt g (Iio t) t := by
  have hbasis : (𝓝[<] t).HasBasis (· < t) (Ioo · t) :=
    nhdsLT_basis_of_exists_lt ⟨0, ht⟩
  constructor
  · intro h
    have hreal :
        ContinuousWithinAt (realOf g) (Iio t) t := by
      rw [← real_close_iff g t ht]
      intro ε hε
      obtain ⟨δ, hδt, hδ⟩ := h ε hε
      exact ⟨δ, hδt, fun s hs => (hδ s hs).2⟩
    have hfin_ev : ∀ᶠ s in 𝓝[<] t, g s ≠ ⊤ := by
      rw [hbasis.eventually_iff]
      obtain ⟨δ, hδt, hδ⟩ := h 1 one_pos
      exact ⟨δ, hδt, fun s hs => (hδ s hs).1⟩
    have hcoe : ContinuousAt ENNReal.ofReal (realOf g t) :=
      ENNReal.continuous_ofReal.continuousAt
    have hgcont := hcoe.comp_continuousWithinAt hreal
    refine hgcont.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hfin_ev] with s hs
      show g s = ENNReal.ofReal (realOf g s)
      rw [realOf, ENNReal.ofReal_toReal hs]
    · show g t = ENNReal.ofReal (realOf g t)
      rw [realOf, ENNReal.ofReal_toReal hfin]
  · intro h
    have hfin_ev : ∀ᶠ s in 𝓝[<] t, g s ≠ ⊤ := by
      have hmem : Iio (⊤ : ℝ≥0∞) ∈ 𝓝 (g t) :=
        Iio_mem_nhds hfin.lt_top
      filter_upwards [h hmem] with s hs
        using (Set.mem_Iio.mp hs).ne
    have hreal :
        ContinuousWithinAt (realOf g) (Iio t) t := by
      have hto : ContinuousAt ENNReal.toReal (g t) :=
        ENNReal.continuousAt_toReal hfin
      exact hto.comp_continuousWithinAt h
    rw [← real_close_iff g t ht] at hreal
    intro ε hε
    obtain ⟨δ₁, hδ₁t, hδ₁⟩ := hreal ε hε
    rw [hbasis.eventually_iff] at hfin_ev
    obtain ⟨δ₂, hδ₂t, hδ₂⟩ := hfin_ev
    refine ⟨max δ₁ δ₂, max_lt hδ₁t hδ₂t, fun s hs => ?_⟩
    have hs1 : s ∈ Ioo δ₁ t :=
      ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, hs.2⟩
    have hs2 : s ∈ Ioo δ₂ t :=
      ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, hs.2⟩
    exact ⟨hδ₂ hs2, hδ₁ s hs1⟩
```

In the _infinite_ case, left-continuity is divergence to $`+\infty`:
`Mathlib`'s characterization of the neighborhoods of $`\top` says the
values tend to $`\top` exactly when every threshold is eventually
exceeded, which on the left-window basis is the divergence clause.

*Theorem:* the infinite divergence clause is left-continuity at $`t`

```lean
theorem infinite_ed_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t)
    (hinf : g t = ⊤) :
    (∀ M : ℝ≥0, ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        (M : ℝ≥0∞) < g s)
      ↔ ContinuousWithinAt g (Iio t) t := by
  have hbasis : (𝓝[<] t).HasBasis (· < t) (Ioo · t) :=
    nhdsLT_basis_of_exists_lt ⟨0, ht⟩
  unfold ContinuousWithinAt
  rw [hinf, ENNReal.tendsto_nhds_top_iff_nnreal]
  constructor
  · intro h M
    obtain ⟨δ, hδt, hδ⟩ := h M
    rw [hbasis.eventually_iff]
    exact ⟨δ, hδt, fun s hs => hδ s hs⟩
  · intro h M
    have hM := h M
    rw [hbasis.eventually_iff] at hM
    obtain ⟨δ, hδt, hδ⟩ := hM
    exact ⟨δ, hδt, fun s hs => hδ hs⟩
```

Combining the two cases, the $`\varepsilon`–$`\delta` definition and
the topological one agree at every positive time, for every `g`.

*Theorem:* the $`\varepsilon`–$`\delta` and topological definitions agree

```lean
theorem isLeftContinuousED_iff (g : ℝ≥0 → ℝ≥0∞) :
    IsLeftContinuousED g ↔ IsLeftContinuous g := by
  unfold IsLeftContinuousED IsLeftContinuous
  refine forall_congr' fun t => ?_
  rcases eq_zero_or_pos t with h0 | ht
  · -- at the origin: LHS vacuous, RHS automatic
    subst h0
    simp only [lt_irrefl, false_implies, true_iff]
    exact continuousWithinAt_Iio_zero g
  · rw [forall_congr_pos ht]
    by_cases hfin : g t = ⊤
    · rw [infinite_ed_iff g t ht hfin]
      constructor
      · rintro ⟨-, h⟩; exact h hfin
      · intro h
        exact ⟨fun hne => absurd hfin hne, fun _ => h⟩
    · rw [finite_ed_iff g t ht hfin]
      constructor
      · rintro ⟨h, -⟩; exact h hfin
      · intro h
        exact ⟨fun _ => h, fun hT => absurd hT hfin⟩
where
  forall_congr_pos {t : ℝ≥0} (ht : 0 < t)
      {P : Prop} : (0 < t → P) ↔ P :=
    ⟨fun h => h ht, fun h _ => h⟩
```

# Right-continuity: the two forms agree

The right side mirrors all of this on the right-window basis
$`\{(t, \delta) \mid t < \delta\}` of `𝓝[>] t`, supplied directly (no
$`\exists\, x > t` witness is needed — the non-negative reals have no
greatest element). First the bare closeness clause.

*Theorem:* the bare $`\varepsilon`-closeness clause is right-continuity of the real reading

```lean
theorem real_close_iff_right
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    (∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        |realOf g s - realOf g t| < ε)
      ↔ ContinuousWithinAt (realOf g) (Ioi t) t := by
  have hbasis : (𝓝[>] t).HasBasis (t < ·) (Ioo t ·) :=
    nhdsGT_basis t
  unfold ContinuousWithinAt
  rw [hbasis.tendsto_iff Metric.nhds_basis_ball]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδt, hδ⟩ := h ε hε
    refine ⟨δ, hδt, fun s hs => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact hδ s hs
  · intro h ε hε
    obtain ⟨δ, hδt, hδ⟩ := h ε hε
    refine ⟨δ, hδt, fun s hs => ?_⟩
    have := hδ s hs
    rwa [Metric.mem_ball, Real.dist_eq] at this
```

The finite case, mirrored. The window-intersection step takes the
$`\min` of the two thresholds (the right side shrinks the window from
above, where the left side took the $`\max`).

*Theorem:* at a finite point, the finite $`\varepsilon`–$`\delta` clause is right-continuity

```lean
theorem finite_ed_iff_right
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (hfin : g t ≠ ⊤) :
    (∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        g s ≠ ⊤ ∧ |realOf g s - realOf g t| < ε)
      ↔ ContinuousWithinAt g (Ioi t) t := by
  have hbasis : (𝓝[>] t).HasBasis (t < ·) (Ioo t ·) :=
    nhdsGT_basis t
  constructor
  · intro h
    have hreal :
        ContinuousWithinAt (realOf g) (Ioi t) t := by
      rw [← real_close_iff_right g t]
      intro ε hε
      obtain ⟨δ, hδt, hδ⟩ := h ε hε
      exact ⟨δ, hδt, fun s hs => (hδ s hs).2⟩
    have hfin_ev : ∀ᶠ s in 𝓝[>] t, g s ≠ ⊤ := by
      rw [hbasis.eventually_iff]
      obtain ⟨δ, hδt, hδ⟩ := h 1 one_pos
      exact ⟨δ, hδt, fun s hs => (hδ s hs).1⟩
    have hcoe : ContinuousAt ENNReal.ofReal (realOf g t) :=
      ENNReal.continuous_ofReal.continuousAt
    have hgcont := hcoe.comp_continuousWithinAt hreal
    refine hgcont.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hfin_ev] with s hs
      show g s = ENNReal.ofReal (realOf g s)
      rw [realOf, ENNReal.ofReal_toReal hs]
    · show g t = ENNReal.ofReal (realOf g t)
      rw [realOf, ENNReal.ofReal_toReal hfin]
  · intro h
    have hfin_ev : ∀ᶠ s in 𝓝[>] t, g s ≠ ⊤ := by
      have hmem : Iio (⊤ : ℝ≥0∞) ∈ 𝓝 (g t) :=
        Iio_mem_nhds hfin.lt_top
      filter_upwards [h hmem] with s hs
        using (Set.mem_Iio.mp hs).ne
    have hreal :
        ContinuousWithinAt (realOf g) (Ioi t) t := by
      have hto : ContinuousAt ENNReal.toReal (g t) :=
        ENNReal.continuousAt_toReal hfin
      exact hto.comp_continuousWithinAt h
    rw [← real_close_iff_right g t] at hreal
    intro ε hε
    obtain ⟨δ₁, hδ₁t, hδ₁⟩ := hreal ε hε
    rw [hbasis.eventually_iff] at hfin_ev
    obtain ⟨δ₂, hδ₂t, hδ₂⟩ := hfin_ev
    refine ⟨min δ₁ δ₂, lt_min hδ₁t hδ₂t, fun s hs => ?_⟩
    have hs1 : s ∈ Ioo t δ₁ :=
      ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
    have hs2 : s ∈ Ioo t δ₂ :=
      ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
    exact ⟨hδ₂ hs2, hδ₁ s hs1⟩
```

The infinite case, mirrored.

*Theorem:* the infinite divergence clause is right-continuity at $`t`

```lean
theorem infinite_ed_iff_right
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (hinf : g t = ⊤) :
    (∀ M : ℝ≥0, ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        (M : ℝ≥0∞) < g s)
      ↔ ContinuousWithinAt g (Ioi t) t := by
  have hbasis : (𝓝[>] t).HasBasis (t < ·) (Ioo t ·) :=
    nhdsGT_basis t
  unfold ContinuousWithinAt
  rw [hinf, ENNReal.tendsto_nhds_top_iff_nnreal]
  constructor
  · intro h M
    obtain ⟨δ, hδt, hδ⟩ := h M
    rw [hbasis.eventually_iff]
    exact ⟨δ, hδt, fun s hs => hδ s hs⟩
  · intro h M
    have hM := h M
    rw [hbasis.eventually_iff] at hM
    obtain ⟨δ, hδt, hδ⟩ := hM
    exact ⟨δ, hδt, fun s hs => hδ hs⟩
```

Combining the two cases gives the right-side equivalence at every time.
There is no origin case split — the right condition is uniform across
all $`t`.

*Theorem:* the $`\varepsilon`–$`\delta` and topological right-continuity agree

```lean
theorem isRightContinuousED_iff (g : ℝ≥0 → ℝ≥0∞) :
    IsRightContinuousED g ↔ IsRightContinuous g := by
  unfold IsRightContinuousED IsRightContinuous
  refine forall_congr' fun t => ?_
  by_cases hfin : g t = ⊤
  · rw [infinite_ed_iff_right g t hfin]
    constructor
    · rintro ⟨-, h⟩; exact h hfin
    · intro h
      exact ⟨fun hne => absurd hfin hne, fun _ => h⟩
  · rw [finite_ed_iff_right g t hfin]
    constructor
    · rintro ⟨h, -⟩; exact h hfin
    · intro h
      exact ⟨fun _ => h, fun hT => absurd hT hfin⟩
```

# One-sided limits

Left-continuity was phrased as a convergence; the limit it converges to
is a value worth naming. The _left limit_ and _right limit_ of $`g` at
$`t` are the limits along the approach filters $`𝓝[<] t` and $`𝓝[>] t`
— the times just below and just above $`t`. We take them as `Mathlib`'s
`limUnder`: the genuine limit when one exists, and an unspecified value
otherwise (so the value is only meaningful paired with a convergence
fact, exactly as the classical "$`g(t^-)`'' / "$`g(t^+)`'' notation is).

*Definition:* the left limit $`g(t^-)`

```lean
noncomputable def leftLimit
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : ℝ≥0∞ :=
  limUnder (𝓝[<] t) g
```

*Definition:* the right limit $`g(t^+)`

```lean
noncomputable def rightLimit
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : ℝ≥0∞ :=
  limUnder (𝓝[>] t) g
```

The right-approach filter is nontrivial at _every_ time — there are
always times just above any $`t`, the non-negative reals having no
greatest element — so a right limit is genuinely pinned by any
convergence, with no positivity guard (in contrast to the left side,
empty at the origin).

```lean
instance instNeBotNhdsGT (t : ℝ≥0) :
    (𝓝[>] t).NeBot := nhdsGT_neBot t
```

When $`g` is left-continuous and the left-approach filter at $`t` is
nontrivial (i.e. $`t > 0`), the left limit _is_ the value: the limit
`limUnder` converges to is $`g(t)`. This is the value-level reading of
left-continuity, $`g(t^-) = g(t)`. We phrase it against the named
`IsLeftContinuous` predicate, applied at $`t`.

*Theorem:* $`g(t^-) = g(t)` when $`g` is left-continuous, at $`t > 0`

```lean
theorem leftLimit_eq_of_leftContinuous
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0)
    (hlc : IsLeftContinuous g)
    [(𝓝[<] t).NeBot] :
    leftLimit g t = g t :=
  (hlc t).tendsto.limUnder_eq
```

Dually, a convergence from the right pins the right limit to the value
it converges to.

*Theorem:* $`g(t^+) = L` when $`g` tends to $`L` from the right

```lean
theorem rightLimit_eq_of_tendsto
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞)
    (h : Tendsto g (𝓝[>] t) (𝓝 L)) :
    rightLimit g t = L :=
  h.limUnder_eq
```

In particular, against the named `IsRightContinuous` predicate this
gives the value-level reading $`g(t^+) = g(t)` at every time — no
positivity guard, the right filter being always nontrivial.

*Theorem:* $`g(t^+) = g(t)` when $`g` is right-continuous

```lean
theorem rightLimit_eq_of_rightContinuous
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0)
    (hrc : IsRightContinuous g) :
    rightLimit g t = g t :=
  (hrc t).tendsto.limUnder_eq
```

# A positive right limit at the origin

A regularity used by the deviation results, naming a use of the right
limit just introduced: the informal $`f(0^+) > 0` means the function
converges from the right at the origin to a value that is strictly
positive — i.e. $`f` tends to its right limit $`f(0^+)` along $`𝓝[>] 0`
and $`0 < f(0^+)`. Stated this way the positivity is a plain inequality
on the named value `rightLimit f 0`, with the convergence carried
explicitly (the right limit value alone is not meaningful without it).

A positive right limit forces $`f` to be positive on a whole
right-neighbourhood of the origin: eventually $`f` exceeds its limit's
lower neighbourhood, which gives an explicit threshold $`\delta`.

*Theorem:* $`f(0^+) > 0` makes $`f` positive on some $`(0, \delta)`

```lean
theorem pos_near_zero_of_rightLimit_pos
    (f : ℝ≥0 → ℝ≥0∞) (L : ℝ≥0∞)
    (hL : Tendsto f (𝓝[>] (0:ℝ≥0)) (𝓝 L))
    (hpos : 0 < rightLimit f 0) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t : ℝ≥0, 0 < t → t < δ → 0 < f t := by
  have hLeq : rightLimit f 0 = L :=
    rightLimit_eq_of_tendsto f 0 L hL
  rw [hLeq] at hpos
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ≥0), 0 < f t :=
    hL.eventually (eventually_gt_nhds hpos)
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
  IsLeftContinuousED (numFn f)
```

*Definition:* a cumulative function is right-continuous via its values

```lean
def IsRightContinuousF (f : Fmin) : Prop :=
  IsRightContinuousED (numFn f)
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
