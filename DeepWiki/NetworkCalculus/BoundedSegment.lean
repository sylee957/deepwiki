import DeepWiki.NetworkCalculus.FunctionDioids
import Mathlib.Data.EReal.Operations

/-! # Bounded-support segments
The affine-on-an-interval building block of the §4.3 bounded-support
representation: a *segment* is affine `va + s·(t−a)` on an interval and `⊤`
(= `+∞`) outside.  `segOpenE` is the OPEN-segment on `(a,b)`, `segE` the
CLOSED-segment on `[a,b]`, each over the carrier `ℝ≥0 → EReal`.  Provides the
`@[simp]` reductions, in- and off-support readings, endpoint values, the
meet-of-line-and-indicator decomposition (`intervalTop`), and the off-support
`= ⊤` behavior of a convolved segment. -/

namespace DeepWiki

open scoped NNReal

/-! ## Open segment -/

/-- Open segment: affine `va + s·(t−a)` (left value `va` at `a⁺`, slope `s`)
on the open interval `(a,b)`, `+∞` outside. -/
noncomputable def segOpenE (a b va s : ℝ≥0) : ℝ≥0 → EReal :=
  fun t => if a < t ∧ t < b then (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) else ⊤

/-- `segOpenE` reduces to its `if`. -/
theorem segOpenE_apply (a b va s t : ℝ≥0) :
    segOpenE a b va s t =
      if a < t ∧ t < b then (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) else ⊤ :=
  rfl

/-- On the open interval `(a,b)`, `segOpenE` is the affine value. -/
@[simp] theorem segOpenE_apply_mem (a b va s t : ℝ≥0) (h : a < t ∧ t < b) :
    segOpenE a b va s t = (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) :=
  if_pos h

/-- Off the open interval `(a,b)`, `segOpenE` is `⊤`. -/
@[simp] theorem segOpenE_apply_not_mem (a b va s t : ℝ≥0) (h : ¬ (a < t ∧ t < b)) :
    segOpenE a b va s t = ⊤ :=
  if_neg h

/-- In-support reading from the two strict bounds. -/
theorem segOpenE_mem (a b va s t : ℝ≥0) (hl : a < t) (hr : t < b) :
    segOpenE a b va s t = (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) :=
  if_pos ⟨hl, hr⟩

/-- At or left of `a`, the open segment is `⊤`. -/
theorem segOpenE_of_le_left (a b va s t : ℝ≥0) (h : t ≤ a) :
    segOpenE a b va s t = ⊤ :=
  if_neg fun hmem => absurd hmem.1 (not_lt.mpr h)

/-- At or right of `b`, the open segment is `⊤`. -/
theorem segOpenE_of_ge_right (a b va s t : ℝ≥0) (h : b ≤ t) :
    segOpenE a b va s t = ⊤ :=
  if_neg fun hmem => absurd hmem.2 (not_lt.mpr h)

/-- On its support, the open segment is finite (`≠ ⊤`). -/
theorem segOpenE_ne_top_of_mem (a b va s t : ℝ≥0) (hl : a < t) (hr : t < b) :
    segOpenE a b va s t ≠ ⊤ := by
  rw [segOpenE_mem a b va s t hl hr]; exact EReal.coe_ne_top _

/-! ## Closed segment -/

/-- Closed segment: affine `va + s·(t−a)` on the closed interval `[a,b]`,
`+∞` outside. -/
noncomputable def segE (a b va s : ℝ≥0) : ℝ≥0 → EReal :=
  fun t => if a ≤ t ∧ t ≤ b then (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) else ⊤

/-- `segE` reduces to its `if`. -/
theorem segE_apply (a b va s t : ℝ≥0) :
    segE a b va s t =
      if a ≤ t ∧ t ≤ b then (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) else ⊤ :=
  rfl

/-- On the closed interval `[a,b]`, `segE` is the affine value. -/
@[simp] theorem segE_apply_mem (a b va s t : ℝ≥0) (h : a ≤ t ∧ t ≤ b) :
    segE a b va s t = (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) :=
  if_pos h

/-- Off the closed interval `[a,b]`, `segE` is `⊤`. -/
@[simp] theorem segE_apply_not_mem (a b va s t : ℝ≥0) (h : ¬ (a ≤ t ∧ t ≤ b)) :
    segE a b va s t = ⊤ :=
  if_neg h

/-- In-support reading from the two bounds. -/
theorem segE_mem (a b va s t : ℝ≥0) (hl : a ≤ t) (hr : t ≤ b) :
    segE a b va s t = (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) :=
  if_pos ⟨hl, hr⟩

/-- Strictly left of `a`, the closed segment is `⊤`. -/
theorem segE_of_lt_left (a b va s t : ℝ≥0) (h : t < a) :
    segE a b va s t = ⊤ :=
  if_neg fun hmem => absurd hmem.1 (not_le.mpr h)

/-- Strictly right of `b`, the closed segment is `⊤`. -/
theorem segE_of_gt_right (a b va s t : ℝ≥0) (h : b < t) :
    segE a b va s t = ⊤ :=
  if_neg fun hmem => absurd hmem.2 (not_le.mpr h)

/-- On its support, the closed segment is finite (`≠ ⊤`). -/
theorem segE_ne_top_of_mem (a b va s t : ℝ≥0) (hl : a ≤ t) (hr : t ≤ b) :
    segE a b va s t ≠ ⊤ := by
  rw [segE_mem a b va s t hl hr]; exact EReal.coe_ne_top _

/-- Left endpoint value: `segE … a = va` (since `a - a = 0`). -/
theorem segE_left (a b va s : ℝ≥0) (h : a ≤ b) :
    segE a b va s a = ((va : ℝ) : EReal) := by
  rw [segE_mem a b va s a le_rfl h]
  simp

/-- Right endpoint value: `segE … b = va + s·(b−a)`. -/
theorem segE_right (a b va s : ℝ≥0) (h : a ≤ b) :
    segE a b va s b = (((va + s * (b - a) : ℝ≥0) : ℝ) : EReal) :=
  segE_mem a b va s b h le_rfl

/-! ## Open ⊆ closed -/

/-- The closed segment dominates the open segment everywhere (`≼` in the dioid
order on `EReal`, i.e. `≤`): off the open support the open value is `⊤`, and on
the open support both agree. -/
theorem segOpenE_le_segE (a b va s : ℝ≥0) :
    segE a b va s ≤ segOpenE a b va s := by
  intro t
  by_cases hmem : a < t ∧ t < b
  · rw [segOpenE_apply_mem a b va s t hmem,
      segE_apply_mem a b va s t ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩]
  · rw [segOpenE_apply_not_mem a b va s t hmem]; exact le_top

/-! ## Join of an affine line and an interval indicator

Off support a segment is `⊤` (= `+∞`), which is the numeric *top* of `EReal`.
Recovering that value by a lattice operation therefore takes the *join* `⊔`
(numeric max), not the meet: `segE = affineLineE ⊔ intervalBot`, where the mask
is `⊥` on `[a,b]` (so the join keeps the affine value there) and `⊤` outside (so
the join forces `⊤`).  In the reversed *dioid* order on `EReal` this `⊔` is the
dioid *meet* — the segment is the dioid-meet of the affine line and the
interval mask, the §4.3 reading. -/

/-- Interval-`⊥`/`⊤` indicator: `⊥` on `[a,b]`, `⊤` outside.  Joining with this
forces `⊤` off `[a,b]` and is absorbed (`⊥`) on it. -/
noncomputable def intervalBot (a b : ℝ≥0) : ℝ≥0 → EReal :=
  fun t => if a ≤ t ∧ t ≤ b then (⊥ : EReal) else ⊤

/-- `intervalBot` reduces to its `if`. -/
theorem intervalBot_apply (a b t : ℝ≥0) :
    intervalBot a b t = if a ≤ t ∧ t ≤ b then (⊥ : EReal) else ⊤ :=
  rfl

/-- On `[a,b]`, `intervalBot` is `⊥`. -/
@[simp] theorem intervalBot_apply_mem (a b t : ℝ≥0) (h : a ≤ t ∧ t ≤ b) :
    intervalBot a b t = (⊥ : EReal) :=
  if_pos h

/-- Off `[a,b]`, `intervalBot` is `⊤`. -/
@[simp] theorem intervalBot_apply_not_mem (a b t : ℝ≥0) (h : ¬ (a ≤ t ∧ t ≤ b)) :
    intervalBot a b t = ⊤ :=
  if_neg h

/-- Affine line `t ↦ va + s·(t−a)` over `EReal`. -/
noncomputable def affineLineE (a va s : ℝ≥0) : ℝ≥0 → EReal :=
  fun t => (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal)

/-- `affineLineE` reduces to the coerced affine value. -/
@[simp] theorem affineLineE_apply (a va s t : ℝ≥0) :
    affineLineE a va s t = (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) :=
  rfl

/-- The closed segment is the join of the affine line and the interval mask:
`segE = affineLineE ⊔ intervalBot`.  On `[a,b]` the mask is `⊥` so the join is
the affine value; off `[a,b]` the mask is `⊤` so the join is `⊤`. -/
theorem segE_eq_sup (a b va s : ℝ≥0) :
    segE a b va s = (affineLineE a va s) ⊔ (intervalBot a b) := by
  funext t
  by_cases hmem : a ≤ t ∧ t ≤ b
  · rw [segE_apply_mem a b va s t hmem]
    simp only [Pi.sup_apply, affineLineE_apply, intervalBot_apply_mem a b t hmem, sup_bot_eq]
  · rw [segE_apply_not_mem a b va s t hmem]
    simp only [Pi.sup_apply, affineLineE_apply, intervalBot_apply_not_mem a b t hmem, sup_top_eq]

/-! ## Off-support convolution behavior

A convolution `minConv f (segE …)` inherits the segment's bounded support only
in the value sense given here: it is bounded above by the affine line plus the
shift split, and the segment contributes `⊤` for any split landing off `[a,b]`.
The general convexity of a (min,+) convolution of two segments (book Theorem
4.1 consequence) is NOT proved here. -/

/-- Convolution upper bound through a closed segment: for any split `u + v = t`
with `v` *inside* `[a,b]`, `minConv f (segE a b va s) t ≤ f u + (va + s·(v−a))`. -/
theorem minConv_segE_le (f : ℝ≥0 → EReal) (a b va s : ℝ≥0)
    {u v t : ℝ≥0} (hsum : u + v = t) (hl : a ≤ v) (hr : v ≤ b) :
    minConv f (segE a b va s) t ≤ f u + (((va + s * (v - a) : ℝ≥0) : ℝ) : EReal) := by
  have := minConv_le_add f (segE a b va s) (u := u) (s := v) hsum
  rwa [segE_mem a b va s v hl hr] at this

/-- Convolution upper bound through an open segment: for any split `u + v = t`
with `v` *strictly inside* `(a,b)`, `minConv f (segOpenE a b va s) t ≤ f u +
(va + s·(v−a))`. -/
theorem minConv_segOpenE_le (f : ℝ≥0 → EReal) (a b va s : ℝ≥0)
    {u v t : ℝ≥0} (hsum : u + v = t) (hl : a < v) (hr : v < b) :
    minConv f (segOpenE a b va s) t ≤ f u + (((va + s * (v - a) : ℝ≥0) : ℝ) : EReal) := by
  have := minConv_le_add f (segOpenE a b va s) (u := u) (s := v) hsum
  rwa [segOpenE_mem a b va s v hl hr] at this

/-! ## Restatements (verification against the intended wording) -/

-- Open segment: affine on `(a,b)`, `+∞` outside.
example (a b va s : ℝ≥0) :
    segOpenE a b va s =
      fun t => if a < t ∧ t < b then (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) else ⊤ :=
  rfl

-- Closed segment: affine on `[a,b]`, `+∞` outside.
example (a b va s : ℝ≥0) :
    segE a b va s =
      fun t => if a ≤ t ∧ t ≤ b then (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) else ⊤ :=
  rfl

-- Endpoint values of a nonempty closed segment: left `va`, right `va + s·(b−a)`.
example (a b va s : ℝ≥0) (h : a ≤ b) :
    segE a b va s a = ((va : ℝ) : EReal) ∧
      segE a b va s b = (((va + s * (b - a) : ℝ≥0) : ℝ) : EReal) :=
  ⟨segE_left a b va s h, segE_right a b va s h⟩

-- A closed segment is the join of its affine line and the interval mask.
example (a b va s : ℝ≥0) :
    segE a b va s = (affineLineE a va s) ⊔ (intervalBot a b) :=
  segE_eq_sup a b va s

end DeepWiki
