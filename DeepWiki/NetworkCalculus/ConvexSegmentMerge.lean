import DeepWiki.NetworkCalculus.ConvexPWLNormalForm

/-! # Theorem 4.1 — the segment-merge algorithm for convex PWL convolution (foundation)
A convex piecewise-linear function in `F₀↑` (ultimately linear) is represented by a base value
`f0 = f(0)`, an asymptotic `finalSlope` (the slope of the last semi-infinite segment), and a list
of `(slope, length)` finite segments applied left to right (slopes increasing and `≤ finalSlope`
for convexity). `convexSegEval` evaluates this representation; `mergeBySlope` merges two
slope-sorted segment lists into one. Theorem 4.1 — that the `(min,plus)` convolution of two convex
PWL functions is the slope-merge of their segments starting from `f(0)+g(0)` — is the correctness
target this layer is built toward (the transform-domain "why" is `thm_4_1_legendre`). -/

namespace DeepWiki

open scoped NNReal

/-- Evaluate a convex PWL given by base value `f0`, asymptotic `finalSlope`, and a list of
`(slope, length)` finite segments applied left to right; once the finite segments are exhausted the
curve continues with `finalSlope`. -/
noncomputable def convexSegEval (f0 finalSlope : ℝ≥0) : List (ℝ≥0 × ℝ≥0) → ℝ≥0 → ℝ≥0
  | [], t => f0 + finalSlope * t
  | (s, ℓ) :: rest, t =>
      if t ≤ ℓ then f0 + s * t else convexSegEval (f0 + s * ℓ) finalSlope rest (t - ℓ)

@[simp] theorem convexSegEval_nil (f0 fs t : ℝ≥0) :
    convexSegEval f0 fs [] t = f0 + fs * t := rfl

theorem convexSegEval_cons (f0 fs s ℓ : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    convexSegEval f0 fs ((s, ℓ) :: rest) t
      = if t ≤ ℓ then f0 + s * t else convexSegEval (f0 + s * ℓ) fs rest (t - ℓ) := rfl

/-- A convex PWL takes its base value `f0` at the origin. -/
@[simp] theorem convexSegEval_zero (f0 fs : ℝ≥0) (l : List (ℝ≥0 × ℝ≥0)) :
    convexSegEval f0 fs l 0 = f0 := by
  cases l with
  | nil => simp
  | cons hd tl => obtain ⟨s, ℓ⟩ := hd; rw [convexSegEval_cons]; simp

/-- Merge two slope-sorted `(slope, length)` segment lists into one, ordering by increasing slope
(the comparison key is the first component, the slope). -/
noncomputable def mergeBySlope : List (ℝ≥0 × ℝ≥0) → List (ℝ≥0 × ℝ≥0) → List (ℝ≥0 × ℝ≥0)
  | [], l => l
  | l, [] => l
  | a :: as, b :: bs =>
      if a.1 ≤ b.1 then a :: mergeBySlope as (b :: bs) else b :: mergeBySlope (a :: as) bs
  termination_by l1 l2 => l1.length + l2.length
  decreasing_by all_goals (simp_wf; try omega)

@[simp] theorem mergeBySlope_nil_left (l : List (ℝ≥0 × ℝ≥0)) : mergeBySlope [] l = l := by
  simp [mergeBySlope]

@[simp] theorem mergeBySlope_nil_right (l : List (ℝ≥0 × ℝ≥0)) : mergeBySlope l [] = l := by
  cases l <;> simp [mergeBySlope]

end DeepWiki
