import DeepWiki.NetworkCalculus.BoundedSegment
import DeepWiki.NetworkCalculus.FunctionDioids

/-! # (min,+) convolution of two bounded segments
The building block of the §4.3 bounded-support representation (book Theorem 4.2,
p.77: "the (min,+) convolution of two segments is convex"). For two closed
segments `f = segE a₁ b₁ v₁ s₁`, `g = segE a₂ b₂ v₂ s₂`, the convolution
`minConv f g` is supported on `[a₁+a₂, b₁+b₂]` and is there a piecewise-affine
*convex* curve whose value at a split `u + v = t` is the affine objective
`(v₁ + s₁·(u−a₁)) + (v₂ + s₂·(v−a₂))`. This file proves the off-support `= ⊤`
behavior, the corner values at `a₁+a₂` and `b₁+b₂`, the per-split upper bound by
the real objective, and the convex lower bound by the objective at the two
admissible-`u` range endpoints — pinning the value between the convex
two-affine endpoint objectives (inf-at-an-endpoint of an affine function). -/

namespace DeepWiki

open scoped NNReal

/-! ## A segment value is never `⊥`

Every value of `segE`/`segOpenE` is either `⊤` or a real coercion, hence `≠ ⊥`.
This is what makes `⊤`-absorbing addition apply at any split touching the
off-support `⊤`. -/

/-- A closed-segment value is never `⊥` (it is `⊤` off support, finite on it). -/
theorem segE_ne_bot (a b va s t : ℝ≥0) : segE a b va s t ≠ ⊥ := by
  rw [segE_apply]
  split
  · exact EReal.coe_ne_bot _
  · exact (by decide : (⊤ : EReal) ≠ ⊥)

/-- An open-segment value is never `⊥`. -/
theorem segOpenE_ne_bot (a b va s t : ℝ≥0) : segOpenE a b va s t ≠ ⊥ := by
  rw [segOpenE_apply]
  split
  · exact EReal.coe_ne_bot _
  · exact (by decide : (⊤ : EReal) ≠ ⊥)

/-! ## On-support real-affine reading

On its support (`a ≤ t`) the ℝ≥0 truncated subtraction `t − a` is the genuine
real difference, so a closed-segment value reads as the *real* affine
`va + s·((t:ℝ) − a)`.  This linear-in-`ℝ` form is what lets the affine-in-`u`
infimum argument run over `ℝ` rather than fighting truncated `ℝ≥0` subtraction. -/

/-- On its support, `segE` reads as the real affine value `va + s·((t:ℝ)−a)`. -/
theorem segE_mem_real (a b va s t : ℝ≥0) (hl : a ≤ t) (hr : t ≤ b) :
    segE a b va s t
      = (((va : ℝ) + (s : ℝ) * ((t : ℝ) - (a : ℝ))) : EReal) := by
  rw [segE_mem a b va s t hl hr]
  congr 1
  push_cast [NNReal.coe_sub hl]
  ring

/-! ## Off-support: the convolution is `⊤` outside `[a₁+a₂, b₁+b₂]`

If `t < a₁+a₂` then every split `u + v = t` cannot have both `a₁ ≤ u` and
`a₂ ≤ v` (that would force `a₁+a₂ ≤ t`); the violating segment is `⊤`, and `⊤`
absorbs the other (finite-or-`⊤`, never `⊥`) term, so every objective is `⊤`
and the infimum is `⊤`. Symmetrically for `t > b₁+b₂` via the right endpoints. -/

/-- Below the support: `minConv (segE …) (segE …) t = ⊤` for `t < a₁+a₂`. -/
theorem minConv_segE_segE_of_lt_left (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ : ℝ≥0)
    {t : ℝ≥0} (ht : t < a₁ + a₂) :
    minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) t = ⊤ := by
  refine top_le_iff.mp (le_minConv fun u v hsum => ?_)
  by_cases hu : u < a₁
  · rw [segE_of_lt_left a₁ b₁ v₁ s₁ u hu,
      EReal.top_add_of_ne_bot (segE_ne_bot a₂ b₂ v₂ s₂ v)]
  · have hv : v < a₂ := by
      by_contra hv
      rw [not_lt] at hv
      have : a₁ + a₂ ≤ u + v := add_le_add (not_lt.mp hu) hv
      rw [hsum] at this
      exact absurd (lt_of_lt_of_le ht this) (lt_irrefl t)
    rw [segE_of_lt_left a₂ b₂ v₂ s₂ v hv,
      EReal.add_top_of_ne_bot (segE_ne_bot a₁ b₁ v₁ s₁ u)]

/-- Above the support: `minConv (segE …) (segE …) t = ⊤` for `b₁+b₂ < t`. -/
theorem minConv_segE_segE_of_gt_right (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ : ℝ≥0)
    {t : ℝ≥0} (ht : b₁ + b₂ < t) :
    minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) t = ⊤ := by
  refine top_le_iff.mp (le_minConv fun u v hsum => ?_)
  by_cases hu : b₁ < u
  · rw [segE_of_gt_right a₁ b₁ v₁ s₁ u hu,
      EReal.top_add_of_ne_bot (segE_ne_bot a₂ b₂ v₂ s₂ v)]
  · have hv : b₂ < v := by
      by_contra hv
      rw [not_lt] at hv
      have : u + v ≤ b₁ + b₂ := add_le_add (not_lt.mp hu) hv
      rw [hsum] at this
      exact absurd (lt_of_le_of_lt this ht) (lt_irrefl t)
    rw [segE_of_gt_right a₂ b₂ v₂ s₂ v hv,
      EReal.add_top_of_ne_bot (segE_ne_bot a₁ b₁ v₁ s₁ u)]

/-! ## Corner values

At the lower corner `t = a₁+a₂` the only admissible split is `(a₁, a₂)` (any
other split sends one factor strictly left of its support, giving `⊤`), so the
value is `v₁ + v₂`. At the upper corner `t = b₁+b₂` it is the sum of the two
right-endpoint values. Both need the segments nonempty (`a ≤ b`). -/

/-- Lower-corner value: `minConv (segE …) (segE …) (a₁+a₂) = v₁ + v₂`. -/
theorem minConv_segE_segE_left (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ : ℝ≥0)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) (a₁ + a₂)
      = ((v₁ : ℝ) : EReal) + ((v₂ : ℝ) : EReal) := by
  apply le_antisymm
  · have := minConv_le_add (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂)
      (u := a₁) (s := a₂) rfl
    rwa [segE_left a₁ b₁ v₁ s₁ h₁, segE_left a₂ b₂ v₂ s₂ h₂] at this
  · refine le_minConv fun u v hsum => ?_
    by_cases hu : u < a₁
    · rw [segE_of_lt_left a₁ b₁ v₁ s₁ u hu,
        EReal.top_add_of_ne_bot (segE_ne_bot a₂ b₂ v₂ s₂ v)]
      exact le_top
    · have hv : v < a₂ ∨ (u = a₁ ∧ v = a₂) := by
        rw [not_lt] at hu
        rcases eq_or_lt_of_le hu with hu' | hu'
        · right
          rw [hu'] at hsum
          exact ⟨hu'.symm, add_left_cancel hsum⟩
        · left
          by_contra hv
          rw [not_lt] at hv
          have : a₁ + a₂ < u + v := add_lt_add_of_lt_of_le hu' hv
          rw [hsum] at this
          exact lt_irrefl _ this
      rcases hv with hv | ⟨hu', hv'⟩
      · rw [segE_of_lt_left a₂ b₂ v₂ s₂ v hv,
          EReal.add_top_of_ne_bot (segE_ne_bot a₁ b₁ v₁ s₁ u)]
        exact le_top
      · rw [hu', hv', segE_left a₁ b₁ v₁ s₁ h₁, segE_left a₂ b₂ v₂ s₂ h₂]

/-- Upper-corner value: `minConv (segE …) (segE …) (b₁+b₂)` is the sum of the
two right-endpoint values `(v₁ + s₁(b₁−a₁)) + (v₂ + s₂(b₂−a₂))`. -/
theorem minConv_segE_segE_right (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ : ℝ≥0)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) (b₁ + b₂)
      = (((v₁ + s₁ * (b₁ - a₁) : ℝ≥0) : ℝ) : EReal)
        + (((v₂ + s₂ * (b₂ - a₂) : ℝ≥0) : ℝ) : EReal) := by
  apply le_antisymm
  · have := minConv_le_add (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂)
      (u := b₁) (s := b₂) rfl
    rwa [segE_right a₁ b₁ v₁ s₁ h₁, segE_right a₂ b₂ v₂ s₂ h₂] at this
  · refine le_minConv fun u v hsum => ?_
    by_cases hu : b₁ < u
    · rw [segE_of_gt_right a₁ b₁ v₁ s₁ u hu,
        EReal.top_add_of_ne_bot (segE_ne_bot a₂ b₂ v₂ s₂ v)]
      exact le_top
    · have hv : b₂ < v ∨ (u = b₁ ∧ v = b₂) := by
        rw [not_lt] at hu
        rcases eq_or_lt_of_le hu with hu' | hu'
        · right
          rw [hu'] at hsum
          exact ⟨hu', add_left_cancel hsum⟩
        · left
          by_contra hv
          rw [not_lt] at hv
          have : u + v < b₁ + b₂ := add_lt_add_of_lt_of_le hu' hv
          rw [hsum] at this
          exact lt_irrefl _ this
      rcases hv with hv | ⟨hu', hv'⟩
      · rw [segE_of_gt_right a₂ b₂ v₂ s₂ v hv,
          EReal.add_top_of_ne_bot (segE_ne_bot a₁ b₁ v₁ s₁ u)]
        exact le_top
      · rw [hu', hv', segE_right a₁ b₁ v₁ s₁ h₁, segE_right a₂ b₂ v₂ s₂ h₂]

/-! ## The affine split objective and its convexity

At time `t`, a split `u + v = t` with both factors on-support contributes the
*real* affine objective
`obj u = (v₁ + s₁·(u−a₁)) + (v₂ + s₂·((t−u)−a₂))`,
which is affine in `u` with slope `s₁ − s₂`.  A real affine function attains its
minimum over an interval at an endpoint (`affine_min_le`), so the infimum of the
objective — and hence the convolution value — is determined by the two
admissible-`u` endpoints: this is the "convex / min-slope-first" content of
book Theorem 4.2. -/

/-- A real affine function `u ↦ c + d·u` is, on `[lo,hi]`, at least the min of
its two endpoint values: `min (c + d·lo) (c + d·hi) ≤ c + d·u`. -/
theorem affine_min_le (c d lo hi u : ℝ) (hlo : lo ≤ u) (hhi : u ≤ hi) :
    min (c + d * lo) (c + d * hi) ≤ c + d * u := by
  rcases le_or_gt 0 d with hd | hd
  · exact le_trans (min_le_left _ _) (by nlinarith [mul_le_mul_of_nonneg_left hlo hd])
  · exact le_trans (min_le_right _ _)
      (by nlinarith [mul_le_mul_of_nonpos_left hhi (le_of_lt hd)])

/-- Real affine split objective: the value `(v₁ + s₁·(u−a₁)) + (v₂ + s₂·((t−u)−a₂))`
contributed (as a real) by the split `u + (t−u) = t` of two closed segments. -/
noncomputable def segPairObj (a₁ v₁ s₁ a₂ v₂ s₂ t u : ℝ) : ℝ :=
  ((v₁ : ℝ) + s₁ * (u - a₁)) + (v₂ + s₂ * ((t - u) - a₂))

/-- `segPairObj` is the affine function `u ↦ C + (s₁−s₂)·u` with
`C = v₁ − s₁·a₁ + v₂ + s₂·(t−a₂)`. -/
theorem segPairObj_eq_affine (a₁ v₁ s₁ a₂ v₂ s₂ t u : ℝ) :
    segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t u
      = (v₁ - s₁ * a₁ + v₂ + s₂ * (t - a₂)) + (s₁ - s₂) * u := by
  unfold segPairObj; ring

/-- Convexity of the split objective: `segPairObj` over `[lo,hi]` is at least the
min of its two endpoint values.  (An affine function is minimized at an endpoint.) -/
theorem segPairObj_min_le (a₁ v₁ s₁ a₂ v₂ s₂ t lo hi u : ℝ)
    (hlo : lo ≤ u) (hhi : u ≤ hi) :
    min (segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t lo) (segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t hi)
      ≤ segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t u := by
  simp only [segPairObj_eq_affine]
  exact affine_min_le _ _ lo hi u hlo hhi

/-! ## Convolution value as the split objective

Combining the on-support real reading with the convolution intro/elim API: an
admissible split (both factors on-support) bounds the convolution above by its
real objective (`minConv_segE_segE_le_obj`), and conversely every split is at
least the min of its two admissible-`u` endpoint objectives, so the convolution
value is bounded below by that endpoint-min (`segPairObj_le_minConv_segE_segE`).
Together these pin `minConv` between the convex two-endpoint objective values. -/

/-- The on-support sum of two segment values equals the coerced real objective:
`segE … u + segE … v = ↑(segPairObj … t u)` when `u + v = t` with both factors
on-support. -/
theorem segE_add_segE_eq_obj (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ : ℝ≥0)
    {u v t : ℝ≥0} (hsum : u + v = t)
    (h₁l : a₁ ≤ u) (h₁r : u ≤ b₁) (h₂l : a₂ ≤ v) (h₂r : v ≤ b₂) :
    segE a₁ b₁ v₁ s₁ u + segE a₂ b₂ v₂ s₂ v
      = ((segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t u : ℝ) : EReal) := by
  rw [segE_mem a₁ b₁ v₁ s₁ u h₁l h₁r, segE_mem a₂ b₂ v₂ s₂ v h₂l h₂r,
    ← EReal.coe_add]
  congr 1
  have hv : (v : ℝ) = (t : ℝ) - (u : ℝ) := by rw [← hsum]; push_cast; ring
  unfold segPairObj
  push_cast [NNReal.coe_sub h₁l, NNReal.coe_sub h₂l]
  rw [hv]

/-- Upper bound by the real objective: for an admissible split `u + v = t` with
both factors on-support, `minConv (segE …) (segE …) t ≤ segPairObj … t u`. -/
theorem minConv_segE_segE_le_obj (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ : ℝ≥0)
    {u v t : ℝ≥0} (hsum : u + v = t)
    (h₁l : a₁ ≤ u) (h₁r : u ≤ b₁) (h₂l : a₂ ≤ v) (h₂r : v ≤ b₂) :
    minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) t
      ≤ ((segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t u : ℝ) : EReal) := by
  rw [← segE_add_segE_eq_obj a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ hsum h₁l h₁r h₂l h₂r]
  exact minConv_le_add (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) (u := u) (s := v) hsum

/-- Lower bound by the endpoint-min objective: if every admissible split `u`
(both factors on-support) has `lo ≤ (u:ℝ) ≤ hi`, then the endpoint-min objective
`min (obj at lo) (obj at hi)` bounds the convolution below.  Together with the
admissible-`u` range `[max a₁ (t−b₂), min b₁ (t−a₂)]` this gives the convex
two-piece value (book Theorem 4.2). -/
theorem segPairObj_le_minConv_segE_segE (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ t : ℝ≥0)
    (lo hi : ℝ)
    (hadm : ∀ u v : ℝ≥0, u + v = t → a₁ ≤ u → u ≤ b₁ → a₂ ≤ v → v ≤ b₂ →
      lo ≤ (u : ℝ) ∧ (u : ℝ) ≤ hi) :
    ((min (segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t lo)
          (segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t hi) : ℝ) : EReal)
      ≤ minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) t := by
  refine le_minConv fun u v hsum => ?_
  by_cases h₁l : u < a₁
  · rw [segE_of_lt_left a₁ b₁ v₁ s₁ u h₁l,
      EReal.top_add_of_ne_bot (segE_ne_bot a₂ b₂ v₂ s₂ v)]; exact le_top
  by_cases h₁r : b₁ < u
  · rw [segE_of_gt_right a₁ b₁ v₁ s₁ u h₁r,
      EReal.top_add_of_ne_bot (segE_ne_bot a₂ b₂ v₂ s₂ v)]; exact le_top
  by_cases h₂l : v < a₂
  · rw [segE_of_lt_left a₂ b₂ v₂ s₂ v h₂l,
      EReal.add_top_of_ne_bot (segE_ne_bot a₁ b₁ v₁ s₁ u)]; exact le_top
  by_cases h₂r : b₂ < v
  · rw [segE_of_gt_right a₂ b₂ v₂ s₂ v h₂r,
      EReal.add_top_of_ne_bot (segE_ne_bot a₁ b₁ v₁ s₁ u)]; exact le_top
  rw [not_lt] at h₁l h₁r h₂l h₂r
  have hu_mem := hadm u v hsum h₁l h₁r h₂l h₂r
  rw [segE_add_segE_eq_obj a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ hsum h₁l h₁r h₂l h₂r,
    EReal.coe_le_coe_iff]
  exact segPairObj_min_le a₁ v₁ s₁ a₂ v₂ s₂ t lo hi (u : ℝ) hu_mem.1 hu_mem.2

/-- The admissible split range: any on-support split `u + v = t` has
`(u:ℝ) ∈ [max a₁ (t−b₂), min b₁ (t−a₂)]`.  (`u ≥ a₁` and `v ≤ b₂ ⇒ u ≥ t−b₂`;
`u ≤ b₁` and `a₂ ≤ v ⇒ u ≤ t−a₂`.) -/
theorem segE_split_mem_range (a₁ b₁ a₂ b₂ t : ℝ≥0)
    {u v : ℝ≥0} (hsum : u + v = t)
    (h₁l : a₁ ≤ u) (h₁r : u ≤ b₁) (h₂l : a₂ ≤ v) (h₂r : v ≤ b₂) :
    max (a₁ : ℝ) ((t : ℝ) - (b₂ : ℝ)) ≤ (u : ℝ) ∧
      (u : ℝ) ≤ min (b₁ : ℝ) ((t : ℝ) - (a₂ : ℝ)) := by
  have htr : (u : ℝ) + (v : ℝ) = (t : ℝ) := by rw [← hsum]; push_cast; ring
  refine ⟨max_le ?_ ?_, le_min ?_ ?_⟩
  · exact_mod_cast h₁l
  · have : (v : ℝ) ≤ (b₂ : ℝ) := by exact_mod_cast h₂r
    linarith
  · exact_mod_cast h₁r
  · have : (a₂ : ℝ) ≤ (v : ℝ) := by exact_mod_cast h₂l
    linarith

/-- Convex lower bound at the concrete admissible endpoints: the convolution of
two closed segments is bounded below by the min of the split objective at the two
range endpoints `lo = max a₁ (t−b₂)`, `hi = min b₁ (t−a₂)`.  With the per-split
upper bound `minConv_segE_segE_le_obj`, this is the convex (min-of-two-affine)
pinning of the §4.3 segment-convolution value (book Theorem 4.2). -/
theorem segPairObj_endpoints_le_minConv (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ t : ℝ≥0) :
    ((min (segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t (max (a₁ : ℝ) ((t : ℝ) - (b₂ : ℝ))))
          (segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t (min (b₁ : ℝ) ((t : ℝ) - (a₂ : ℝ)))) : ℝ)
        : EReal)
      ≤ minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) t :=
  segPairObj_le_minConv_segE_segE a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ t _ _
    (fun _ _ hsum h₁l h₁r h₂l h₂r =>
      segE_split_mem_range a₁ b₁ a₂ b₂ t hsum h₁l h₁r h₂l h₂r)

/-! ## Restatements (verification against the intended wording) -/

-- Off support (both sides), the convolution of two closed segments is `+∞`.
example (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ : ℝ≥0) {t : ℝ≥0}
    (ht : t < a₁ + a₂ ∨ b₁ + b₂ < t) :
    minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) t = ⊤ :=
  ht.elim (minConv_segE_segE_of_lt_left a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂)
    (minConv_segE_segE_of_gt_right a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂)

-- Lower corner: value `v₁ + v₂`.
example (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ : ℝ≥0) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) (a₁ + a₂)
      = ((v₁ : ℝ) : EReal) + ((v₂ : ℝ) : EReal) :=
  minConv_segE_segE_left a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ h₁ h₂

-- Convex pinning: the convolution value lies between the endpoint-min objective
-- (below) and the objective at any admissible split (above) — the two-affine /
-- min-slope-first content of the segment-convolution being convex.
example (a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ t : ℝ≥0) {u v : ℝ≥0} (hsum : u + v = t)
    (h₁l : a₁ ≤ u) (h₁r : u ≤ b₁) (h₂l : a₂ ≤ v) (h₂r : v ≤ b₂) :
    ((min (segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t (max (a₁ : ℝ) ((t : ℝ) - (b₂ : ℝ))))
          (segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t (min (b₁ : ℝ) ((t : ℝ) - (a₂ : ℝ)))) : ℝ)
        : EReal)
      ≤ minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) t ∧
    minConv (segE a₁ b₁ v₁ s₁) (segE a₂ b₂ v₂ s₂) t
      ≤ ((segPairObj a₁ v₁ s₁ a₂ v₂ s₂ t u : ℝ) : EReal) :=
  ⟨segPairObj_endpoints_le_minConv a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ t,
    minConv_segE_segE_le_obj a₁ b₁ v₁ s₁ a₂ b₂ v₂ s₂ hsum h₁l h₁r h₂l h₂r⟩

end DeepWiki
