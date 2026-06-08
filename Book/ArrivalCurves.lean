import Book.FunctionDioids

/-! # Arrival curves
For a cumulative function `A` (taken as a plain `ℝ≥0 → ℝ≥0` function), a
non-decreasing function `α` is:

* a **maximal** (upper) arrival curve when `A ≤ A ∗ α` (`∗` = min-plus
  convolution `minConv`): `A` is dominated by its min-plus self-convolution.
* a **minimal** (lower) arrival curve when `A ≥ A ⊼ α` (`⊼` = max-plus
  convolution `maxConv`): `A` dominates its max-plus self-convolution.

Each has an equivalent **increment** characterization: `A (t + d) ≤ A t + α d`
for the maximal curve, and `A t + α d ≤ A (t + d)` for the minimal one. -/

namespace DeepWiki

open scoped Classical NNReal

/-- `α` is a maximal (upper) arrival curve for `A`: `A t ≤ (A ∗ α) t` for all
`t`, the natural-order form of `A ≤ A ∗ α` with `∗` the min-plus convolution. -/
def IsMaximalArrivalCurve (A α : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, A t ≤ minConv A α t

/-- `α` is a minimal (lower) arrival curve for `A`: `(A ⊼ α) t ≤ A t` for all
`t`, the natural-order form of `A ≥ A ⊼ α` with `⊼` the max-plus convolution. -/
def IsMinimalArrivalCurve (A α : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, maxConv A α t ≤ A t

/-- Equivalent definition of a maximal arrival curve: `A ≤ A ∗ α` holds iff the
increment bound `A (t + d) ≤ A t + α d` holds for all `t, d`. -/
theorem isMaximalArrivalCurve_iff_increment (A α : ℝ≥0 → ℝ≥0) :
    IsMaximalArrivalCurve A α ↔ ∀ t d : ℝ≥0, A (t + d) ≤ A t + α d := by
  constructor
  · -- `A (t + d) ≤ ⨅ {A u + α s | u + s = t + d} ≤ A t + α d`
    intro h t d
    refine le_trans (h (t + d)) ?_
    show (⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t + d}, A p.1.1 + α p.1.2)
        ≤ A t + α d
    exact ciInf_le (OrderBot.bddBelow _)
      (⟨(t, d), rfl⟩ : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t + d})
  · -- each split `u + s = t` gives `A t = A (u + s) ≤ A u + α s`, so `A t ≤ ⨅`
    intro h t
    show A t ≤ ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t}, A p.1.1 + α p.1.2
    refine le_ciInf ?_
    rintro ⟨⟨u, s⟩, rfl⟩
    exact h u s

/-- A sufficient increment condition for a minimal arrival curve: if
`A t + α d ≤ A (t + d)` for all `t, d`, then `A ≥ A ⊼ α`. This direction holds
unconditionally on `ℝ≥0`; the converse needs `MaxConvBddAbove` (see
`isMinimalArrivalCurve_iff_increment_of_bddAbove`), since otherwise the `ℝ≥0`
supremum is junk `0` and `A ≥ A ⊼ α` holds vacuously while the increment bound
may fail. -/
theorem isMinimalArrivalCurve_of_increment (A α : ℝ≥0 → ℝ≥0)
    (h : ∀ t d : ℝ≥0, A t + α d ≤ A (t + d)) :
    IsMinimalArrivalCurve A α := by
  -- each split `u + s = t` gives `A u + α s ≤ A (u + s) = A t`, so `⨆ ≤ A t`
  intro t
  refine ciSup_le ?_
  rintro ⟨⟨u, s⟩, rfl⟩
  exact h u s

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
    IsMinimalArrivalCurve A α ↔ ∀ t d : ℝ≥0, A t + α d ≤ A (t + d) := by
  refine ⟨fun h t d => ?_, isMinimalArrivalCurve_of_increment A α⟩
  -- `A t + α d` is the `(t, d)`-split term, so it is `≤` the supremum `≤ A (t+d)`
  refine le_trans ?_ (h (t + d))
  exact le_ciSup_of_le (hbdd (t + d))
    (⟨(t, d), rfl⟩ : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t + d}) le_rfl

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

end DeepWiki
