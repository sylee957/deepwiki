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

/-- A convex PWL never drops below its base value (all slopes are `≥ 0`). -/
theorem convexSegEval_base_le (fs : ℝ≥0) (l : List (ℝ≥0 × ℝ≥0)) (f0 t : ℝ≥0) :
    f0 ≤ convexSegEval f0 fs l t := by
  induction l generalizing f0 t with
  | nil => rw [convexSegEval_nil]; exact le_self_add
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      rw [convexSegEval_cons]
      split
      · exact le_self_add
      · exact le_trans le_self_add (ih (f0 + s * ℓ) (t - ℓ))

/-- A convex PWL is nondecreasing. -/
theorem monotone_convexSegEval (fs : ℝ≥0) (l : List (ℝ≥0 × ℝ≥0)) (f0 : ℝ≥0) :
    Monotone (convexSegEval f0 fs l) := by
  induction l generalizing f0 with
  | nil => intro t1 t2 h; simp only [convexSegEval_nil]; gcongr
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      intro t1 t2 h
      rw [convexSegEval_cons, convexSegEval_cons]
      split
      · split
        · gcongr
        · rename_i h1 h2
          exact le_trans (by gcongr) (convexSegEval_base_le fs tl (f0 + s * ℓ) (t2 - ℓ))
      · split
        · rename_i h1 h2
          exact absurd (le_trans h h2) h1
        · exact ih (f0 + s * ℓ) (tsub_le_tsub_right h ℓ)

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

/-- Peel the leading segment `(s, ℓ)`: evaluating past its length is the tail evaluated from the
shifted base, `convexSegEval f0 fs ((s, ℓ) :: rest) (ℓ + r) = convexSegEval (f0 + s·ℓ) fs rest r`.
(At `r = 0` both sides are the corner value `f0 + s·ℓ`.) -/
theorem convexSegEval_cons_peel (f0 fs s ℓ r : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) :
    convexSegEval f0 fs ((s, ℓ) :: rest) (ℓ + r)
      = convexSegEval (f0 + s * ℓ) fs rest r := by
  rw [convexSegEval_cons]
  rcases eq_or_ne r 0 with hr0 | hr0
  · subst hr0
    rw [add_zero, if_pos le_rfl, convexSegEval_zero]
  · have hr : ℓ < ℓ + r := lt_add_of_pos_right ℓ (pos_iff_ne_zero.mpr hr0)
    rw [if_neg (not_le.mpr hr), add_tsub_cancel_left]

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

/-- A convex PWL whose every slope is `≥ p` grows at least at rate `p` from its base:
`g0 + p·s ≤ convexSegEval g0 sg l s` (generalizes `convexSegEval_base_le`, the `p = 0` case). -/
theorem convexSegEval_lower (sg p : ℝ≥0) :
    ∀ l : List (ℝ≥0 × ℝ≥0), (∀ seg ∈ l, p ≤ seg.1) → p ≤ sg → ∀ g0 s : ℝ≥0,
      g0 + p * s ≤ convexSegEval g0 sg l s := by
  intro l
  induction l with
  | nil => intro _ hsg g0 s; rw [convexSegEval_nil]; gcongr
  | cons hd tl ih =>
      intro hl hsg g0 s
      obtain ⟨sseg, ℓ⟩ := hd
      have hsseg : p ≤ sseg := hl (sseg, ℓ) List.mem_cons_self
      have htl : ∀ seg ∈ tl, p ≤ seg.1 := fun seg h => hl seg (List.mem_cons_of_mem _ h)
      rw [convexSegEval_cons]
      split
      · gcongr
      · rename_i hsℓ
        have hℓs : ℓ ≤ s := (not_le.mp hsℓ).le
        refine le_trans ?_ (ih htl hsg (g0 + sseg * ℓ) (s - ℓ))
        have hps : p * s = p * ℓ + p * (s - ℓ) := by rw [← mul_add, add_tsub_cancel_of_le hℓs]
        rw [hps, show g0 + (p * ℓ + p * (s - ℓ)) = (g0 + p * ℓ) + p * (s - ℓ) from by ring]
        gcongr

/-- A convex PWL whose every slope is `≥ p` grows at least at rate `p` between *any* two points:
`convexSegEval g0 sg l x + p·d ≤ convexSegEval g0 sg l (x + d)` (the from-any-point strengthening
of `convexSegEval_lower`, which is its `x = 0` case via `convexSegEval_zero`). -/
theorem convexSegEval_rate (sg p : ℝ≥0) :
    ∀ l : List (ℝ≥0 × ℝ≥0), (∀ seg ∈ l, p ≤ seg.1) → p ≤ sg → ∀ g0 x d : ℝ≥0,
      convexSegEval g0 sg l x + p * d ≤ convexSegEval g0 sg l (x + d) := by
  intro l
  induction l with
  | nil =>
      intro _ hsg g0 x d
      rw [convexSegEval_nil, convexSegEval_nil]
      have hpsg : p * d ≤ sg * d := by gcongr
      calc g0 + sg * x + p * d ≤ g0 + sg * x + sg * d := by gcongr
        _ = g0 + sg * (x + d) := by ring
  | cons hd tl ih =>
      intro hl hsg g0 x d
      obtain ⟨sseg, ℓ⟩ := hd
      have hsseg : p ≤ sseg := hl (sseg, ℓ) List.mem_cons_self
      have htl : ∀ seg ∈ tl, p ≤ seg.1 := fun seg h => hl seg (List.mem_cons_of_mem _ h)
      rw [convexSegEval_cons, convexSegEval_cons]
      by_cases hxd : x + d ≤ ℓ
      · -- both `x` and `x + d` on the leading segment
        have hx : x ≤ ℓ := le_trans le_self_add hxd
        rw [if_pos hx, if_pos hxd]
        have hpsseg : p * d ≤ sseg * d := by gcongr
        calc g0 + sseg * x + p * d ≤ g0 + sseg * x + sseg * d := by gcongr
          _ = g0 + sseg * (x + d) := by ring
      · by_cases hx : x ≤ ℓ
        · -- `x` on the leading segment, `x + d` past it
          rw [if_pos hx, if_neg hxd]
          have hℓxd : ℓ ≤ x + d := (not_le.mp hxd).le
          refine le_trans ?_ (convexSegEval_lower sg p tl htl hsg (g0 + sseg * ℓ) (x + d - ℓ))
          -- reduce to `sseg·x + p·d ≤ sseg·ℓ + p·(x+d-ℓ)`
          have hpsub : p * (x + d) = p * ℓ + p * (x + d - ℓ) := by
            rw [← mul_add, add_tsub_cancel_of_le hℓxd]
          have hkey : sseg * x + p * d ≤ sseg * ℓ + p * (x + d - ℓ) := by
            have hstep : sseg * x + p * ℓ ≤ sseg * ℓ + p * x := by
              have : p * (ℓ - x) ≤ sseg * (ℓ - x) := by gcongr
              have hxℓ : x ≤ ℓ := hx
              calc sseg * x + p * ℓ = sseg * x + (p * x + p * (ℓ - x)) := by
                      rw [← mul_add, add_tsub_cancel_of_le hxℓ]
                _ ≤ sseg * x + (p * x + sseg * (ℓ - x)) := by gcongr
                _ = sseg * ℓ + p * x := by
                      rw [show sseg * x + (p * x + sseg * (ℓ - x))
                            = (sseg * x + sseg * (ℓ - x)) + p * x from by ring,
                        ← mul_add, add_tsub_cancel_of_le hxℓ]
            -- now combine with `p·x + p·d = p·ℓ + p·(x+d-ℓ)`
            have hpxd : p * x + p * d = p * ℓ + p * (x + d - ℓ) := by
              rw [← mul_add, hpsub]
            -- add `p·x` to both sides; the goal then reduces to `hstep` after `hpxd`
            rw [← add_le_add_iff_right (p * x)]
            calc sseg * x + p * d + p * x
                = sseg * x + (p * x + p * d) := by ring
              _ = sseg * x + (p * ℓ + p * (x + d - ℓ)) := by rw [hpxd]
              _ = (sseg * x + p * ℓ) + p * (x + d - ℓ) := by ring
              _ ≤ (sseg * ℓ + p * x) + p * (x + d - ℓ) := by gcongr
              _ = sseg * ℓ + p * (x + d - ℓ) + p * x := by ring
          calc g0 + sseg * x + p * d = g0 + (sseg * x + p * d) := by ring
            _ ≤ g0 + (sseg * ℓ + p * (x + d - ℓ)) := by gcongr
            _ = g0 + sseg * ℓ + p * (x + d - ℓ) := by ring
        · -- both past the leading segment
          rw [if_neg hx, if_neg hxd]
          have hℓx : ℓ ≤ x := (not_le.mp hx).le
          have hsplit : x + d - ℓ = (x - ℓ) + d := by
            rw [tsub_add_eq_add_tsub hℓx]
          rw [hsplit]
          exact ih htl hsg (g0 + sseg * ℓ) (x - ℓ) d

/-- **Theorem 4.1, the flat case** (convolution by a flatter line; the book's `f ∗ g = f + g(0)`
when each slope of `f` is `≤` each slope of `g`). If a line `u ↦ a + p·u` is flatter than the
convex PWL `g` (every slope of `g` is `≥ p`), their `(min,plus)` convolution is the line shifted by
`g(0)`: `(a + p·u) ∗ g = a + g0 + p·t`. The flatter operand absorbs all the mass. -/
theorem minConv_flatLine_convexSegEval (a p g0 sg : ℝ≥0) (l : List (ℝ≥0 × ℝ≥0))
    (hl : ∀ seg ∈ l, p ≤ seg.1) (hsg : p ≤ sg) (t : ℝ≥0) :
    minConv (fun u => (((a + p * u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval g0 sg l v : ℝ≥0) : ℝ) : EReal)) t
      = (((a + g0 + p * t : ℝ≥0) : ℝ) : EReal) := by
  have coeadd : ∀ x y : ℝ≥0,
      (((x : ℝ) : EReal)) + (((y : ℝ) : EReal)) = (((x + y : ℝ≥0) : ℝ) : EReal) := by
    intro x y; rw [← EReal.coe_add, ← NNReal.coe_add]
  apply le_antisymm
  · refine le_trans (minConv_le_add _ _ (add_zero t)) (le_of_eq ?_)
    simp only [convexSegEval_zero]
    rw [coeadd]; norm_cast; ring
  · refine le_minConv (fun u v huv => ?_)
    rw [coeadd, EReal.coe_le_coe_iff, NNReal.coe_le_coe]
    have hlow : g0 + p * v ≤ convexSegEval g0 sg l v := convexSegEval_lower sg p l hl hsg g0 v
    calc a + g0 + p * t = (a + p * u) + (g0 + p * v) := by rw [← huv]; ring
      _ ≤ (a + p * u) + convexSegEval g0 sg l v := by gcongr

end DeepWiki
