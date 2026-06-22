import DeepWiki.NetworkCalculus.Convex
import DeepWiki.NetworkCalculus.RealCurves

/-! # Piecewise-linear convex functions (the convex dual of `ConcavePWLNormalForm`)
A convex piecewise-linear function is the pointwise supremum of finitely many *rate-latency*
curves `β_{R,T}(t) = R·(t−T)₊` — the dual of the concave "minimum of token-buckets". This file
lays the convex layer for DNC §4.2: each rate-latency curve is convex (`isConvexEReal_rateLatencyEReal`,
the dual of `isConcaveEReal_tbEReal`), and the supremum evaluation `convexNFEval` is convex. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Function

/-- The `ℝ≥0` truncated subtraction, read in `ℝ`, is the relu `max (x − T) 0`. -/
private theorem coe_tsub_eq_max (x T : ℝ≥0) : ((x - T : ℝ≥0) : ℝ) = max ((x : ℝ) - T) 0 := by
  rcases le_total T x with h | h
  · rw [NNReal.coe_sub h, max_eq_left (by have := NNReal.coe_le_coe.mpr h; linarith)]
  · rw [tsub_eq_zero_of_le h, NNReal.coe_zero,
      max_eq_right (by have := NNReal.coe_le_coe.mpr h; linarith)]

/-- The rate-latency curve `β_{R,T}(t) = R·(t − T)₊` is convex (the dual of
`isConcaveEReal_tbEReal`): a non-negative scalar times the relu of an affine function. The chord
RHS is `≥ 0` and `≥` the shifted affine value, hence `≥` their maximum. -/
theorem isConvexEReal_rateLatencyEReal (R T : ℝ≥0) : IsConvexEReal (rateLatencyEReal R T) := by
  intro s t p hp
  simp only [rateLatencyEReal]
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  simp only [NNReal.coe_mul]
  rw [coe_tsub_eq_max (p * s + (1 - p) * t) T, coe_tsub_eq_max s T, coe_tsub_eq_max t T]
  push_cast [NNReal.coe_sub hp]
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := R.coe_nonneg
  have hP : (0 : ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have hP1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hQ : (0 : ℝ) ≤ 1 - (p : ℝ) := by linarith
  have h1 : (p : ℝ) * ((s : ℝ) - T) ≤ (p : ℝ) * max ((s : ℝ) - T) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hP
  have h2 : (1 - (p : ℝ)) * ((t : ℝ) - T) ≤ (1 - (p : ℝ)) * max ((t : ℝ) - T) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hQ
  have hkey : max ((p : ℝ) * (s : ℝ) + (1 - (p : ℝ)) * (t : ℝ) - T) 0
      ≤ (p : ℝ) * max ((s : ℝ) - T) 0 + (1 - (p : ℝ)) * max ((t : ℝ) - T) 0 := by
    apply max_le
    · have heq : (p : ℝ) * (s : ℝ) + (1 - (p : ℝ)) * (t : ℝ) - T
          = (p : ℝ) * ((s : ℝ) - T) + (1 - (p : ℝ)) * ((t : ℝ) - T) := by ring
      rw [heq]; linarith [h1, h2]
    · have h3 := mul_nonneg hP (le_max_right ((s : ℝ) - T) 0)
      have h4 := mul_nonneg hQ (le_max_right ((t : ℝ) - T) 0)
      linarith
  calc (R : ℝ) * max ((p : ℝ) * (s : ℝ) + (1 - (p : ℝ)) * (t : ℝ) - T) 0
      ≤ (R : ℝ) * ((p : ℝ) * max ((s : ℝ) - T) 0 + (1 - (p : ℝ)) * max ((t : ℝ) - T) 0) :=
        mul_le_mul_of_nonneg_left hkey hRnn
    _ = (p : ℝ) * ((R : ℝ) * max ((s : ℝ) - T) 0)
          + (1 - (p : ℝ)) * ((R : ℝ) * max ((t : ℝ) - T) 0) := by ring

/-- A list of `(rate, latency)` pairs evaluated as a convex piecewise-linear curve: the pointwise
supremum of the rate-latency curves `β_{Rᵢ,Tᵢ}` (`⊥` for the empty list). -/
noncomputable def convexNFEval (l : List (ℝ≥0 × ℝ≥0)) : ℝ≥0 → EReal :=
  l.foldr (fun rt acc => rateLatencyEReal rt.1 rt.2 ⊔ acc) (const ℝ≥0 (⊥ : EReal))

@[simp] theorem convexNFEval_nil : convexNFEval [] = const ℝ≥0 (⊥ : EReal) := rfl

@[simp] theorem convexNFEval_cons (rt : ℝ≥0 × ℝ≥0) (l : List (ℝ≥0 × ℝ≥0)) :
    convexNFEval (rt :: l) = rateLatencyEReal rt.1 rt.2 ⊔ convexNFEval l := rfl

/-- The constant `⊥` curve is convex (its chord value `⊥` lies below everything). -/
theorem isConvexEReal_botCurve : IsConvexEReal (const ℝ≥0 (⊥ : EReal)) := fun _ _ _ _ => bot_le

/-- A convex piecewise-linear function (the supremum of rate-latencies) is convex — the supremum
of convex curves is convex. The dual of `isConcaveEReal_concaveNFEval`. -/
theorem isConvexEReal_convexNFEval (l : List (ℝ≥0 × ℝ≥0)) : IsConvexEReal (convexNFEval l) := by
  induction l with
  | nil => exact isConvexEReal_botCurve
  | cons rt l ih =>
      rw [convexNFEval_cons]
      exact IsConvexEReal.sup _ _ (isConvexEReal_rateLatencyEReal rt.1 rt.2) ih

/-- Each rate-latency curve `β_{R,T}` is nondecreasing. -/
theorem monotone_rateLatencyEReal (R T : ℝ≥0) : Monotone (rateLatencyEReal R T) := by
  intro a b hab
  simp only [rateLatencyEReal]
  rw [EReal.coe_le_coe_iff, NNReal.coe_le_coe]
  gcongr

/-- A convex piecewise-linear function is nondecreasing — a supremum of nondecreasing
rate-latencies. -/
theorem monotone_convexNFEval (l : List (ℝ≥0 × ℝ≥0)) : Monotone (convexNFEval l) := by
  induction l with
  | nil => exact monotone_const
  | cons rt l ih => rw [convexNFEval_cons]; exact (monotone_rateLatencyEReal rt.1 rt.2).sup ih

end DeepWiki
