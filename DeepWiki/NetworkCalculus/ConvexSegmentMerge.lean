import DeepWiki.NetworkCalculus.ConvexPWLNormalForm
import DeepWiki.NetworkCalculus.FunctionDioids

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

/-- Merge step when the leading slopes compare `a.1 ≤ b.1`: the `a`-segment comes first. -/
theorem mergeBySlope_cons_le {a b : ℝ≥0 × ℝ≥0} {as bs : List (ℝ≥0 × ℝ≥0)} (h : a.1 ≤ b.1) :
    mergeBySlope (a :: as) (b :: bs) = a :: mergeBySlope as (b :: bs) := by
  rw [mergeBySlope, if_pos h]

/-- Merge step when `b.1 < a.1`: the `b`-segment comes first. -/
theorem mergeBySlope_cons_gt {a b : ℝ≥0 × ℝ≥0} {as bs : List (ℝ≥0 × ℝ≥0)} (h : ¬ a.1 ≤ b.1) :
    mergeBySlope (a :: as) (b :: bs) = b :: mergeBySlope (a :: as) bs := by
  rw [mergeBySlope, if_neg h]

/-- **Theorem 4.1, base case** (the single semi-infinite segment, i.e. affine curves). The
`(min,plus)` convolution of two affine curves `u ↦ a + p·u` and `u ↦ b + q·u` is the affine curve
`a + b + min(p,q)·t` — the slower slope wins, with the bursts added. (This is the merge of two
empty segment lists: `convexSegEval f0 sf [] = f0 + sf·t`, and the result has slope `min(sf,sg)`
from `f(0)+g(0)`.) -/
theorem minConv_affine (a p b q t : ℝ≥0) :
    minConv (fun u => (((a + p * u : ℝ≥0) : ℝ) : EReal))
            (fun u => (((b + q * u : ℝ≥0) : ℝ) : EReal)) t
      = (((a + b + min p q * t : ℝ≥0) : ℝ) : EReal) := by
  have coeadd : ∀ x y : ℝ≥0,
      (((x : ℝ) : EReal)) + (((y : ℝ) : EReal)) = (((x + y : ℝ≥0) : ℝ) : EReal) := by
    intro x y; rw [← EReal.coe_add, ← NNReal.coe_add]
  apply le_antisymm
  · rcases le_total p q with hpq | hpq
    · refine le_trans (minConv_le_add _ _ (add_zero t)) (le_of_eq ?_)
      rw [coeadd, min_eq_left hpq]; norm_cast; ring
    · refine le_trans (minConv_le_add _ _ (zero_add t)) (le_of_eq ?_)
      rw [coeadd, min_eq_right hpq]; norm_cast; ring
  · refine le_minConv (fun u v huv => ?_)
    rw [coeadd, EReal.coe_le_coe_iff, NNReal.coe_le_coe]
    have hmin : min p q * t ≤ p * u + q * v := by
      have h2 : min p q * t = min p q * u + min p q * v := by rw [← huv]; ring
      rw [h2]; gcongr
      · exact min_le_left p q
      · exact min_le_right p q
    calc a + b + min p q * t ≤ a + b + (p * u + q * v) := by gcongr
      _ = (a + p * u) + (b + q * v) := by ring

end DeepWiki
