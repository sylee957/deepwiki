import VersoManual
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Limits" =>
Before continuity we develop the more primitive notion it rests on:
_one-sided limits_ of a function $`g : \mathbb{R}^{+} \to
\overline{\mathbb{R}}_{\ge 0}^\infty`. A one-sided limit is the value
$`g` approaches along the times just below $`t` (from the left) or just
above (from the right). We give the elementary $`\varepsilon`–$`\delta`
form of convergence to a value, relate it to `Mathlib`'s `Tendsto`
along the one-sided approach filters $`𝓝[<] t` / $`𝓝[>] t`, name the
limit _value_ and its _existence_, and connect the two. Continuity is
then, in the next chapter, the special case where the one-sided limit
equals $`g(t)`.

Everything is on the bare value type, with `Mathlib`'s order topology;
no dioid structure is involved.

```lean
namespace DeepWiki

open Topology Filter Set
open scoped Classical NNReal ENNReal
```

# One-sided convergence and limit existence

The headline notions. _One-sided convergence_ is `Mathlib`'s `Tendsto`
along the one-sided approach filters $`𝓝[<] t` (times just below $`t`)
and $`𝓝[>] t` (just above) — we name them so the chapter speaks one
vocabulary rather than spelling out the filter each time.

*Definition:* $`g` converges to $`L` from the left

```lean
def TendstoLeft
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞) : Prop :=
  Tendsto g (𝓝[<] t) (𝓝 L)
```

*Definition:* $`g` converges to $`L` from the right

```lean
def TendstoRight
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞) : Prop :=
  Tendsto g (𝓝[>] t) (𝓝 L)
```

A one-sided limit _exists_ when the function converges to some value on
that side — written directly as the existential $`\exists L,`
`TendstoLeft g t L` (and the right analogue), with no separate predicate.
This is the primitive on which continuity (next chapter) is built —
continuity will be the case where the limit equals $`g(t)`.

The rest of the chapter develops these: an elementary
$`\varepsilon`–$`\delta` characterization of one-sided convergence and
its quantified existence reading.

# Convergence to a value: the epsilon-delta form

The elementary form of one-sided convergence splits by cases on the
target $`L`, on a one-sided window — an open interval of times just
before $`t` (for the left) or just after (for the right). Where $`L` is
_finite_, on a small enough window the values are _finite_ and stay
$`\varepsilon`-close to $`L`; the finiteness is part of the clause, so a
stray $`+\infty` adjacent to $`t` correctly breaks it rather than being
read as a real number. Where $`L` is $`+\infty`, the values must
_diverge_: every finite threshold $`M` is eventually exceeded. The
finite clause reads the values through $`\mathbb{R}` via `toReal`.

*Definition:* the real reading $`s \mapsto g(s)` into $`\mathbb{R}`

```lean
noncomputable def realOf (g : ℝ≥0 → ℝ≥0∞) : ℝ≥0 → ℝ :=
  fun s => (g s).toReal
```

*Definition:* $`g` converges to $`L` from the left (ε–δ)

```lean
def TendstoLeftED
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞) : Prop :=
  (L ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
      g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε) ∧
  (L = ⊤ →
    ∀ M : ℝ≥0, ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
      (M : ℝ≥0∞) < g s)
```

*Definition:* $`g` converges to $`L` from the right (ε–δ)

```lean
def TendstoRightED
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞) : Prop :=
  (L ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
      g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε) ∧
  (L = ⊤ →
    ∀ M : ℝ≥0, ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
      (M : ℝ≥0∞) < g s)
```

We relate these clauses to `Mathlib`'s `Tendsto` along the one-sided
filters, one case at a time, then combine. We first record the bare
closeness reductions (no finiteness conjunct) on each side.

*Theorem:* the bare $`\varepsilon`-closeness clause is left-convergence of the real reading

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

The finite-target left case: convergence to a finite $`L` in the
$`\varepsilon`–$`\delta` form is `Tendsto` to $`L` from the left.

*Theorem:* finite-target left convergence agrees with `Tendsto`

```lean
theorem finite_tendstoLeftED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t)
    (L : ℝ≥0∞) (hLfin : L ≠ ⊤) :
    (∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε)
      ↔ TendstoLeft g t L := by
  unfold TendstoLeft
  have hbasis : (𝓝[<] t).HasBasis (· < t) (Ioo · t) :=
    nhdsLT_basis_of_exists_lt ⟨0, ht⟩
  constructor
  · intro h
    have hreal :
        Tendsto (realOf g) (𝓝[<] t) (𝓝 L.toReal) := by
      rw [hbasis.tendsto_iff Metric.nhds_basis_ball]
      intro ε hε
      obtain ⟨δ, hδt, hδ⟩ := h ε hε
      exact ⟨δ, hδt, fun s hs => by
        rw [Metric.mem_ball, Real.dist_eq]
        exact (hδ s hs).2⟩
    have hfin_ev : ∀ᶠ s in 𝓝[<] t, g s ≠ ⊤ := by
      rw [hbasis.eventually_iff]
      obtain ⟨δ, hδt, hδ⟩ := h 1 one_pos
      exact ⟨δ, hδt, fun s hs => (hδ s hs).1⟩
    have hcoe :
        ContinuousAt ENNReal.ofReal L.toReal :=
      ENNReal.continuous_ofReal.continuousAt
    have := hcoe.tendsto.comp hreal
    rw [ENNReal.ofReal_toReal hLfin] at this
    refine this.congr' ?_
    filter_upwards [hfin_ev] with s hs
    show ENNReal.ofReal (realOf g s) = g s
    rw [realOf, ENNReal.ofReal_toReal hs]
  · intro h
    have hfin_ev : ∀ᶠ s in 𝓝[<] t, g s ≠ ⊤ := by
      have hmem : Iio (⊤ : ℝ≥0∞) ∈ 𝓝 L :=
        Iio_mem_nhds hLfin.lt_top
      filter_upwards [h hmem] with s hs
        using (Set.mem_Iio.mp hs).ne
    have hreal :
        Tendsto (realOf g) (𝓝[<] t) (𝓝 L.toReal) := by
      have hto : ContinuousAt ENNReal.toReal L :=
        ENNReal.continuousAt_toReal hLfin
      exact hto.tendsto.comp h
    rw [hbasis.tendsto_iff Metric.nhds_basis_ball] at hreal
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

The infinite-target left case: divergence to $`+\infty` is `Tendsto` to
$`\top`.

*Theorem:* infinite-target left convergence agrees with `Tendsto`

```lean
theorem infinite_tendstoLeftED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t) :
    (∀ M : ℝ≥0, ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        (M : ℝ≥0∞) < g s)
      ↔ TendstoLeft g t ⊤ := by
  unfold TendstoLeft
  have hbasis : (𝓝[<] t).HasBasis (· < t) (Ioo · t) :=
    nhdsLT_basis_of_exists_lt ⟨0, ht⟩
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
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

Combining the two cases, $`\varepsilon`–$`\delta` convergence to $`L`
from the left is exactly `Tendsto` to $`L`.

*Theorem:* $`g` converges to $`L` from the left iff it `Tendsto` to $`L`

```lean
theorem tendstoLeftED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t)
    (L : ℝ≥0∞) :
    TendstoLeftED g t L ↔ TendstoLeft g t L := by
  unfold TendstoLeftED
  by_cases hfin : L = ⊤
  · subst hfin
    rw [← infinite_tendstoLeftED_iff g t ht]
    constructor
    · rintro ⟨-, h⟩; exact h rfl
    · intro h
      exact ⟨fun hne => absurd rfl hne, fun _ => h⟩
  · rw [← finite_tendstoLeftED_iff g t ht L hfin]
    constructor
    · rintro ⟨h, -⟩; exact h hfin
    · intro h
      exact ⟨fun _ => h, fun hT => absurd hT hfin⟩
```

The right side, on the right-window basis of $`𝓝[>] t` (nontrivial at
every time, so no positivity guard). First the bare closeness reduction.

*Theorem:* the bare $`\varepsilon`-closeness clause is right-convergence of the real reading

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

The finite-target right case.

*Theorem:* finite-target right convergence agrees with `Tendsto`

```lean
theorem finite_tendstoRightED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0)
    (L : ℝ≥0∞) (hLfin : L ≠ ⊤) :
    (∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε)
      ↔ TendstoRight g t L := by
  unfold TendstoRight
  have hbasis : (𝓝[>] t).HasBasis (t < ·) (Ioo t ·) :=
    nhdsGT_basis t
  constructor
  · intro h
    have hreal :
        Tendsto (realOf g) (𝓝[>] t) (𝓝 L.toReal) := by
      rw [hbasis.tendsto_iff Metric.nhds_basis_ball]
      intro ε hε
      obtain ⟨δ, hδt, hδ⟩ := h ε hε
      exact ⟨δ, hδt, fun s hs => by
        rw [Metric.mem_ball, Real.dist_eq]
        exact (hδ s hs).2⟩
    have hfin_ev : ∀ᶠ s in 𝓝[>] t, g s ≠ ⊤ := by
      rw [hbasis.eventually_iff]
      obtain ⟨δ, hδt, hδ⟩ := h 1 one_pos
      exact ⟨δ, hδt, fun s hs => (hδ s hs).1⟩
    have hcoe :
        ContinuousAt ENNReal.ofReal L.toReal :=
      ENNReal.continuous_ofReal.continuousAt
    have := hcoe.tendsto.comp hreal
    rw [ENNReal.ofReal_toReal hLfin] at this
    refine this.congr' ?_
    filter_upwards [hfin_ev] with s hs
    show ENNReal.ofReal (realOf g s) = g s
    rw [realOf, ENNReal.ofReal_toReal hs]
  · intro h
    have hfin_ev : ∀ᶠ s in 𝓝[>] t, g s ≠ ⊤ := by
      have hmem : Iio (⊤ : ℝ≥0∞) ∈ 𝓝 L :=
        Iio_mem_nhds hLfin.lt_top
      filter_upwards [h hmem] with s hs
        using (Set.mem_Iio.mp hs).ne
    have hreal :
        Tendsto (realOf g) (𝓝[>] t) (𝓝 L.toReal) := by
      have hto : ContinuousAt ENNReal.toReal L :=
        ENNReal.continuousAt_toReal hLfin
      exact hto.tendsto.comp h
    rw [hbasis.tendsto_iff Metric.nhds_basis_ball] at hreal
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

The infinite-target right case.

*Theorem:* infinite-target right convergence agrees with `Tendsto`

```lean
theorem infinite_tendstoRightED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    (∀ M : ℝ≥0, ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        (M : ℝ≥0∞) < g s)
      ↔ TendstoRight g t ⊤ := by
  unfold TendstoRight
  have hbasis : (𝓝[>] t).HasBasis (t < ·) (Ioo t ·) :=
    nhdsGT_basis t
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
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

Combining, on the right.

*Theorem:* $`g` converges to $`L` from the right iff it `Tendsto` to $`L`

```lean
theorem tendstoRightED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞) :
    TendstoRightED g t L ↔ TendstoRight g t L := by
  unfold TendstoRightED
  by_cases hfin : L = ⊤
  · subst hfin
    rw [← infinite_tendstoRightED_iff g t]
    constructor
    · rintro ⟨-, h⟩; exact h rfl
    · intro h
      exact ⟨fun hne => absurd rfl hne, fun _ => h⟩
  · rw [← finite_tendstoRightED_iff g t L hfin]
    constructor
    · rintro ⟨h, -⟩; exact h hfin
    · intro h
      exact ⟨fun _ => h, fun hT => absurd hT hfin⟩
```

# Existence of one-sided limits

We work with limit _existence_ directly, as an existential over the
convergence value — $`\exists L,` `TendstoRight g t L` — rather than
naming a possibly-undefined limit value: a fact about "the limit" is
stated as "there is an $`L` the function converges to, and $`L` has the
property". This sidesteps the need for a junk value when no limit exists,
and its $`\varepsilon`–$`\delta` reading is just the convergence
equivalences above quantified over the target.

The right-approach filter is nontrivial at _every_ time — there are
always times just above any $`t`, the non-negative reals having no
greatest element — so the limit value, where it exists, is unique.

```lean
instance instNeBotNhdsGT (t : ℝ≥0) :
    (𝓝[>] t).NeBot := nhdsGT_neBot t
```

```lean
end DeepWiki
```
