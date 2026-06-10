import Book.FunctionDioids

/-! # Arrival curves
For a cumulative function `A` (a plain function `ℝ≥0 → T` into an ordered
codomain — `ℝ≥0`, or `EReal` for server outputs), a non-decreasing `α` is:

* a **maximal** (upper) arrival curve when `A ≤ A ∗ α` (`∗` = min-plus
  convolution `minConv`): `A` is dominated by its min-plus self-convolution.
* a **minimal** (lower) arrival curve when `A ≥ A ⊼ α` (`⊼` = max-plus
  convolution `maxConv`): `A` dominates its max-plus self-convolution.

Each has an equivalent **increment** characterization: `A (t + d) ≤ A t + α d`
for the maximal curve, and `A t + α d ≤ A (t + d)` for the minimal one. The
maximal-curve properties live in `Book.ArrivalCurvesMaximal`, the minimal-curve
ones in `Book.ArrivalCurvesMinimal`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- `α` is a maximal (upper) arrival curve for `A`: `A ≤ A ∗ α` in the
natural pointwise order, with `∗` the min-plus convolution (over any ordered
codomain `T` with `+` and infima, e.g. `ℝ≥0` or `EReal`). -/
def IsMaximalArrivalCurve {T : Type*} [Add T] [ConditionallyCompleteLattice T]
    (A α : ℝ≥0 → T) : Prop :=
  A ≤ minConv A α

/-- `α` is a minimal (lower) arrival curve for `A`: `A ⊼ α ≤ A` in the
natural pointwise order, with `⊼` the max-plus convolution (over any ordered
codomain `T` with `+` and suprema). -/
def IsMinimalArrivalCurve {T : Type*} [Add T] [ConditionallyCompleteLattice T]
    (A α : ℝ≥0 → T) : Prop :=
  maxConv A α ≤ A

/-! ## Increment characterizations -/

/-- Equivalent definition of a maximal arrival curve: `A ≤ A ∗ α` holds iff the
increment bound `A (t + d) ≤ A t + α d` holds for all `t, d`. -/
theorem isMaximalArrivalCurve_iff_increment {T : Type*} [Add T]
    [ConditionallyCompleteLattice T] [OrderBot T] (A α : ℝ≥0 → T) :
    IsMaximalArrivalCurve A α ↔ ∀ t d : ℝ≥0, A (t + d) ≤ A t + α d := by
  constructor
  · -- `A (t + d) ≤ ⨅ {A u + α s | u + s = t + d} ≤ A t + α d`
    intro h t d
    exact le_trans (h (t + d)) (minConv_le_add A α rfl)
  · -- each split `u + s = t` gives `A t = A (u + s) ≤ A u + α s`
    intro h t
    exact le_minConv fun u s hus => hus ▸ h u s

/-- A sufficient increment condition for a minimal arrival curve: if
`A t + α d ≤ A (t + d)` for all `t, d`, then `A ≥ A ⊼ α`. This direction holds
unconditionally on `ℝ≥0`; the converse needs `MaxConvBddAbove` (see
`isMinimalArrivalCurve_iff_increment_of_bddAbove`), since otherwise the `ℝ≥0`
supremum is junk `0` and `A ≥ A ⊼ α` holds vacuously while the increment bound
may fail. -/
theorem isMinimalArrivalCurve_of_increment (A α : ℝ≥0 → ℝ≥0)
    (h : ∀ t d : ℝ≥0, A t + α d ≤ A (t + d)) :
    IsMinimalArrivalCurve A α :=
  fun t => maxConv_le fun u s (hus : u + s = t) => hus ▸ h u s

/-- The max-plus convolution family `{A u + α s | u + s = t}` is bounded above
for every `t` — the condition making the `ℝ≥0` supremum `A ⊼ α` well-defined
(not junk), needed for the converse of the increment characterization. -/
def MaxConvBddAbove (A α : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, BddAbove (Set.range
    (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} => A p.1.1 + α p.1.2))

/-- Equivalent definition of a minimal arrival curve, under `MaxConvBddAbove`:
`A ≥ A ⊼ α` holds iff the increment bound `A t + α d ≤ A (t + d)` holds for all
`t, d`. The bound on the convolution family makes the supremum well-defined, so
each term lies below it. -/
theorem isMinimalArrivalCurve_iff_increment_of_bddAbove
    (A α : ℝ≥0 → ℝ≥0) (hbdd : MaxConvBddAbove A α) :
    IsMinimalArrivalCurve A α ↔ ∀ t d : ℝ≥0, A t + α d ≤ A (t + d) :=
  ⟨fun h t d => (le_ciSup (hbdd (t + d)) ⟨(t, d), rfl⟩).trans (h (t + d)),
    isMinimalArrivalCurve_of_increment A α⟩

/-- When `A` and `α` are non-decreasing, the max-plus convolution family at `t`
is bounded above by `A t + α t` (each split has `u, s ≤ t`). Cumulative `A` and
`α ∈ ℱ↑` are non-decreasing, so this holds in the book's setting. -/
theorem maxConvBddAbove_of_monotone (A α : ℝ≥0 → ℝ≥0)
    (hA : Monotone A) (hα : Monotone α) : MaxConvBddAbove A α := by
  intro t
  refine ⟨A t + α t, ?_⟩
  rintro x ⟨⟨⟨u, s⟩, rfl⟩, rfl⟩
  exact add_le_add (hA (le_add_right le_rfl)) (hα (le_add_left le_rfl))

/-- Equivalent definition of a minimal arrival curve for non-decreasing `A`, `α`:
`A ≥ A ⊼ α` holds iff `A t + α d ≤ A (t + d)` for all `t, d`. Monotonicity bounds
the max-plus convolution, discharging `MaxConvBddAbove`. -/
theorem isMinimalArrivalCurve_iff_increment_of_monotone
    (A α : ℝ≥0 → ℝ≥0) (hA : Monotone A) (hα : Monotone α) :
    IsMinimalArrivalCurve A α ↔ ∀ t d : ℝ≥0, A t + α d ≤ A (t + d) :=
  isMinimalArrivalCurve_iff_increment_of_bddAbove A α
    (maxConvBddAbove_of_monotone A α hA hα)

/-! ## Crossing of one curve below another
The set of positive times where a curve falls to or below another — for an
arrival curve against a service curve, the lengths at which service catches
arrivals — and its infimum, the first crossing. -/

/-- The crossing set of `f` below `g`: the positive times where `f x ≤ g x`. -/
def crossingSet {T : Type*} [LE T] (f g : ℝ≥0 → T) : Set ℝ≥0 :=
  {x | 0 < x ∧ f x ≤ g x}

/-- Membership in `crossingSet f g` is positivity plus the crossing
inequality. -/
theorem mem_crossingSet_iff {T : Type*} [LE T] {f g : ℝ≥0 → T} {x : ℝ≥0} :
    x ∈ crossingSet f g ↔ 0 < x ∧ f x ≤ g x := Iff.rfl

/-- The crossing set grows as the left curve shrinks: `α' ≤ α` gives
`crossingSet α β ⊆ crossingSet α' β`. -/
theorem crossingSet_anti_left {T : Type*} [Preorder T] {α α' β : ℝ≥0 → T}
    (hle : ∀ t, α' t ≤ α t) :
    crossingSet α β ⊆ crossingSet α' β :=
  fun x hx => ⟨hx.1, (hle x).trans hx.2⟩

/-- The first crossing of `f` below `g`, read in `ℝ≥0∞` (`⊤` when the curves
never cross). -/
noncomputable def firstCrossing {T : Type*} [LE T] (f g : ℝ≥0 → T) : ℝ≥0∞ :=
  ⨅ x ∈ crossingSet f g, (x : ℝ≥0∞)

/-- Intro: a bound below every crossing point is below the first crossing. -/
theorem le_firstCrossing {T : Type*} [LE T] {f g : ℝ≥0 → T} {c : ℝ≥0∞}
    (h : ∀ x ∈ crossingSet f g, c ≤ (x : ℝ≥0∞)) :
    c ≤ firstCrossing f g :=
  le_iInf₂ h

end DeepWiki
