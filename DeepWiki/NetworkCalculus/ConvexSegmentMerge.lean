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

/-- **Theorem 4.1 — the convolution slope-peel** (the single inductive step). If `F`'s leading
segment has slope `sa` and `G` grows at least at rate `sa` everywhere (`hGrate`), then for times
`t ≥ ℓa` the `(min,plus)` convolution past the leading length equals the convolution of `F`'s
*tail* `F' = convexSegEval (f0+sa·ℓa) sf as` with `G`: `(F ∗ G) t = (F' ∗ G) (t − ℓa)`. The
flattest segment is consumed first, peeling one block off the merge. -/
theorem minConv_peel_leadSeg (f0 sf sa ℓa : ℝ≥0) (as : List (ℝ≥0 × ℝ≥0))
    (G : ℝ≥0 → ℝ≥0)
    (hGrate : ∀ x d : ℝ≥0, G x + sa * d ≤ G (x + d)) {t : ℝ≥0} (ht : ℓa ≤ t) :
    minConv (fun u => (((convexSegEval f0 sf ((sa, ℓa) :: as) u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((G v : ℝ≥0) : ℝ) : EReal)) t
      = minConv (fun u => (((convexSegEval (f0 + sa * ℓa) sf as u : ℝ≥0) : ℝ) : EReal))
                (fun v => (((G v : ℝ≥0) : ℝ) : EReal)) (t - ℓa) := by
  apply le_antisymm
  · -- (≤) each tail-split `u'+v = t-ℓa` lifts to an `F`-split `(ℓa+u')+v = t` via the peel
    refine le_minConv (fun u' v huv => ?_)
    have hsplit : (ℓa + u') + v = t := by
      rw [add_assoc, huv, add_tsub_cancel_of_le ht]
    refine le_trans (minConv_le_add _ _ hsplit) (le_of_eq ?_)
    rw [convexSegEval_cons_peel]
  · -- (≥) each `F`-split `u+v=t`: if `u ≥ ℓa` peel; else slide `sa·(ℓa−u)` of g-mass to f
    refine le_minConv (fun u v huv => ?_)
    by_cases hu : ℓa ≤ u
    · -- `u` past the leading segment: peel directly
      have hsplit : u - ℓa + v = t - ℓa := by
        rw [tsub_add_eq_add_tsub hu, huv]
      refine le_trans (minConv_le_add _ _ hsplit) (le_of_eq ?_)
      rw [← convexSegEval_cons_peel f0 sf sa ℓa (u - ℓa) as, add_tsub_cancel_of_le hu]
    · -- `u` on the leading segment: use the split `(0, v-(ℓa-u))` of `t-ℓa`
      have huℓa : u ≤ ℓa := (not_le.mp hu).le
      set d := ℓa - u with hd
      have hvt : v = t - u := (eq_tsub_of_add_eq (by rw [add_comm]; exact huv))
      have hvd : d ≤ v := by
        rw [hd, hvt]; exact tsub_le_tsub_right ht u
      have hsplit : (0 : ℝ≥0) + (v - d) = t - ℓa := by
        rw [zero_add, hd, hvt, tsub_tsub_tsub_cancel_right huℓa]
      refine le_trans (minConv_le_add _ _ hsplit) ?_
      -- now: `↑(F' 0) + ↑(G (v-d)) ≤ ↑(F u) + ↑(G v)` in EReal, via `hGrate` + `F u = f0+sa·u`
      have coeadd : ∀ x y : ℝ≥0,
          (((x : ℝ) : EReal)) + (((y : ℝ) : EReal)) = (((x + y : ℝ≥0) : ℝ) : EReal) := by
        intro x y; rw [← EReal.coe_add, ← NNReal.coe_add]
      rw [coeadd, coeadd, EReal.coe_le_coe_iff, NNReal.coe_le_coe]
      have hF'0 : convexSegEval (f0 + sa * ℓa) sf as 0 = f0 + sa * ℓa := convexSegEval_zero _ _ _
      have hFu : convexSegEval f0 sf ((sa, ℓa) :: as) u = f0 + sa * u := by
        rw [convexSegEval_cons, if_pos huℓa]
      rw [hF'0, hFu]
      have hGstep : G (v - d) + sa * d ≤ G v := by
        have := hGrate (v - d) d
        rwa [tsub_add_cancel_of_le hvd] at this
      have hℓa : sa * ℓa = sa * u + sa * d := by
        rw [hd, ← mul_add, add_tsub_cancel_of_le huℓa]
      calc f0 + sa * ℓa + G (v - d)
          = (f0 + sa * u) + (sa * d + G (v - d)) := by rw [hℓa]; ring
        _ = (f0 + sa * u) + (G (v - d) + sa * d) := by rw [add_comm (sa * d)]
        _ ≤ (f0 + sa * u) + G v := by gcongr

/-- **Theorem 4.1 — the convolution on the leading segment** (the short-time half of the peel). On
times `t ≤ ℓa`, before the flattest segment `(sa, ℓa)` of `F` is exhausted, the `(min,plus)`
convolution with a `G` growing at rate `≥ sa` everywhere is the affine `F(0)+G(0)+sa·t`:
`(F ∗ G) t = f0 + G 0 + sa·t`. -/
theorem minConv_leadSeg_le (f0 sf sa ℓa : ℝ≥0) (as : List (ℝ≥0 × ℝ≥0))
    (G : ℝ≥0 → ℝ≥0) (hGrate : ∀ x d : ℝ≥0, G x + sa * d ≤ G (x + d)) {t : ℝ≥0} (ht : t ≤ ℓa) :
    minConv (fun u => (((convexSegEval f0 sf ((sa, ℓa) :: as) u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((G v : ℝ≥0) : ℝ) : EReal)) t
      = (((f0 + G 0 + sa * t : ℝ≥0) : ℝ) : EReal) := by
  have coeadd : ∀ x y : ℝ≥0,
      (((x : ℝ) : EReal)) + (((y : ℝ) : EReal)) = (((x + y : ℝ≥0) : ℝ) : EReal) := by
    intro x y; rw [← EReal.coe_add, ← NNReal.coe_add]
  have hFu : ∀ u : ℝ≥0, u ≤ ℓa → convexSegEval f0 sf ((sa, ℓa) :: as) u = f0 + sa * u :=
    fun u hu => by rw [convexSegEval_cons, if_pos hu]
  apply le_antisymm
  · refine le_trans (minConv_le_add _ _ (add_zero t)) (le_of_eq ?_)
    rw [hFu t ht, coeadd]; norm_cast; ring
  · refine le_minConv (fun u v huv => ?_)
    have hut : u ≤ t := huv ▸ le_self_add
    have hu : u ≤ ℓa := le_trans hut ht
    rw [hFu u hu, coeadd, EReal.coe_le_coe_iff, NNReal.coe_le_coe]
    have hGlow : G 0 + sa * v ≤ G v := by
      have := hGrate 0 v; rwa [zero_add] at this
    calc f0 + G 0 + sa * t = (f0 + sa * u) + (G 0 + sa * v) := by rw [← huv]; ring
      _ ≤ (f0 + sa * u) + G v := by gcongr

/-- From a slope-sorted list `l` and `sa ≤ l.head.1`, every slope of `l` dominates `sa`. -/
theorem sorted_head_le_all {sa : ℝ≥0} {l : List (ℝ≥0 × ℝ≥0)}
    (hsort : List.Pairwise (fun a b => a.1 ≤ b.1) l) {hd : ℝ≥0 × ℝ≥0} {tl : List (ℝ≥0 × ℝ≥0)}
    (hl : l = hd :: tl) (hsa : sa ≤ hd.1) : ∀ seg ∈ l, sa ≤ seg.1 := by
  subst hl
  rw [List.pairwise_cons] at hsort
  intro seg hseg
  rw [List.mem_cons] at hseg
  rcases hseg with rfl | hseg
  · exact hsa
  · exact le_trans hsa (hsort.1 seg hseg)

/-- The growth-rate hypothesis `convexSegEval_rate` packages for `minConv_peel_leadSeg`: a convex
PWL with all slopes `≥ sa` (and asymptotic `≥ sa`) grows at rate `≥ sa` from any point. -/
theorem convexSegEval_rate_of_le {s sa g0 : ℝ≥0} {l : List (ℝ≥0 × ℝ≥0)}
    (hall : ∀ seg ∈ l, sa ≤ seg.1) (hsas : sa ≤ s) :
    ∀ x d : ℝ≥0, convexSegEval g0 s l x + sa * d ≤ convexSegEval g0 s l (x + d) :=
  fun x d => convexSegEval_rate s sa l hall hsas g0 x d

/-- **Theorem 4.1, the balanced case.** When two convex PWLs share the same asymptotic slope `s`
(every finite segment slope is `≤ s`, and the segment lists are slope-sorted), the full
`mergeBySlope` is *exactly* the `(min,plus)` convolution — no truncation needed, because the merged
list keeps slope `< s` throughout:
`(convexSegEval f0 s fsegs) ∗ (convexSegEval g0 s gsegs) = convexSegEval (f0+g0) s (mergeBySlope …)`.
Proved by peeling the globally flattest leading segment (`minConv_peel_leadSeg`) until both lists
are empty, where it is the affine base case `minConv_affine`. -/
theorem minConv_convexSegEval_balanced (s : ℝ≥0) :
    ∀ (n : ℕ) (fsegs gsegs : List (ℝ≥0 × ℝ≥0)), fsegs.length + gsegs.length = n →
      ∀ (f0 g0 t : ℝ≥0),
      List.Pairwise (fun a b => a.1 ≤ b.1) fsegs →
      List.Pairwise (fun a b => a.1 ≤ b.1) gsegs →
      (∀ seg ∈ fsegs, seg.1 ≤ s) → (∀ seg ∈ gsegs, seg.1 ≤ s) →
      (((convexSegEval (f0 + g0) s (mergeBySlope fsegs gsegs) t : ℝ≥0) : ℝ) : EReal)
        = minConv (fun u => (((convexSegEval f0 s fsegs u : ℝ≥0) : ℝ) : EReal))
                  (fun v => (((convexSegEval g0 s gsegs v : ℝ≥0) : ℝ) : EReal)) t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro fsegs gsegs hn f0 g0 t hfsort hgsort hfs hgs
    match fsegs, gsegs, hn with
    | [], [], _ =>
        rw [mergeBySlope_nil_left, convexSegEval_nil]
        simp only [convexSegEval_nil]
        rw [minConv_affine f0 s g0 s t, min_self]
    | [], (sb, ℓb) :: gbs, hn =>
        -- f affine slope `s`; peel g's leading segment, recurse on `([], gbs)`
        have hsbs : sb ≤ s := hgs (sb, ℓb) List.mem_cons_self
        have hgbs_sort : List.Pairwise (fun a b => a.1 ≤ b.1) gbs :=
          (List.pairwise_cons.mp hgsort).2
        have hgbs_le : ∀ seg ∈ gbs, seg.1 ≤ s :=
          fun seg h => hgs seg (List.mem_cons_of_mem _ h)
        -- `F_f` is affine slope `s`; it grows at rate `≥ sb` since `sb ≤ s`
        have hGrate : ∀ x d : ℝ≥0,
            convexSegEval f0 s [] x + sb * d ≤ convexSegEval f0 s [] (x + d) :=
          convexSegEval_rate_of_le (by simp) hsbs
        rw [mergeBySlope_nil_left]
        by_cases ht : t ≤ ℓb
        · -- short region: convolution is affine on `g`'s leading segment
          rw [convexSegEval_cons, if_pos ht, minConv_comm,
            minConv_leadSeg_le g0 s sb ℓb gbs _ hGrate ht, convexSegEval_zero]
          norm_cast; ring
        · -- past `ℓb`: peel `g`'s lead and apply the IH on `([], gbs)`
          have hℓbt : ℓb ≤ t := (not_le.mp ht).le
          rw [convexSegEval_cons, if_neg ht, minConv_comm,
            minConv_peel_leadSeg g0 s sb ℓb gbs _ hGrate hℓbt, minConv_comm]
          have hlen : ([] : List (ℝ≥0 × ℝ≥0)).length + gbs.length < n := by
            simp only [List.length_nil, List.length_cons] at hn ⊢; omega
          have := ih _ hlen [] gbs rfl f0 (g0 + sb * ℓb) (t - ℓb)
            List.Pairwise.nil hgbs_sort (by simp) hgbs_le
          rw [mergeBySlope_nil_left] at this
          rw [show f0 + g0 + sb * ℓb = f0 + (g0 + sb * ℓb) from by ring]
          exact this
    | (sa, ℓa) :: fas, [], hn =>
        -- symmetric to the previous case: peel `f`'s leading segment, recurse on `(fas, [])`
        have hsas : sa ≤ s := hfs (sa, ℓa) List.mem_cons_self
        have hfas_sort : List.Pairwise (fun a b => a.1 ≤ b.1) fas :=
          (List.pairwise_cons.mp hfsort).2
        have hfas_le : ∀ seg ∈ fas, seg.1 ≤ s :=
          fun seg h => hfs seg (List.mem_cons_of_mem _ h)
        have hGrate : ∀ x d : ℝ≥0,
            convexSegEval g0 s [] x + sa * d ≤ convexSegEval g0 s [] (x + d) :=
          convexSegEval_rate_of_le (by simp) hsas
        rw [mergeBySlope_nil_right]
        by_cases ht : t ≤ ℓa
        · rw [convexSegEval_cons, if_pos ht,
            minConv_leadSeg_le f0 s sa ℓa fas _ hGrate ht, convexSegEval_zero]
        · have hℓat : ℓa ≤ t := (not_le.mp ht).le
          rw [convexSegEval_cons, if_neg ht,
            minConv_peel_leadSeg f0 s sa ℓa fas _ hGrate hℓat]
          have hlen : fas.length + ([] : List (ℝ≥0 × ℝ≥0)).length < n := by
            simp only [List.length_nil, List.length_cons] at hn ⊢; omega
          have := ih _ hlen fas [] rfl (f0 + sa * ℓa) g0 (t - ℓa)
            hfas_sort List.Pairwise.nil hfas_le (by simp)
          rw [mergeBySlope_nil_right] at this
          rw [show f0 + g0 + sa * ℓa = f0 + sa * ℓa + g0 from by ring]
          exact this
    | (sa, ℓa) :: fas, (sb, ℓb) :: gbs, hn =>
        have hsas : sa ≤ s := hfs (sa, ℓa) List.mem_cons_self
        have hsbs : sb ≤ s := hgs (sb, ℓb) List.mem_cons_self
        have hfas_sort : List.Pairwise (fun a b => a.1 ≤ b.1) fas :=
          (List.pairwise_cons.mp hfsort).2
        have hgbs_sort : List.Pairwise (fun a b => a.1 ≤ b.1) gbs :=
          (List.pairwise_cons.mp hgsort).2
        have hfas_le : ∀ seg ∈ fas, seg.1 ≤ s :=
          fun seg h => hfs seg (List.mem_cons_of_mem _ h)
        have hgbs_le : ∀ seg ∈ gbs, seg.1 ≤ s :=
          fun seg h => hgs seg (List.mem_cons_of_mem _ h)
        by_cases hab : sa ≤ sb
        · -- `f`'s lead is the global min: peel it, recurse on `(fas, (sb,ℓb)::gbs)`
          have hgall : ∀ seg ∈ (sb, ℓb) :: gbs, sa ≤ seg.1 :=
            sorted_head_le_all hgsort rfl hab
          have hGrate : ∀ x d : ℝ≥0,
              convexSegEval g0 s ((sb, ℓb) :: gbs) x + sa * d
                ≤ convexSegEval g0 s ((sb, ℓb) :: gbs) (x + d) :=
            convexSegEval_rate_of_le hgall hsas
          rw [mergeBySlope_cons_le (show (sa, ℓa).1 ≤ (sb, ℓb).1 from hab)]
          by_cases ht : t ≤ ℓa
          · rw [convexSegEval_cons, if_pos ht,
              minConv_leadSeg_le f0 s sa ℓa fas _ hGrate ht, convexSegEval_zero]
          · have hℓat : ℓa ≤ t := (not_le.mp ht).le
            rw [convexSegEval_cons, if_neg ht,
              minConv_peel_leadSeg f0 s sa ℓa fas _ hGrate hℓat]
            have hlen : fas.length + ((sb, ℓb) :: gbs).length < n := by
              simp only [List.length_cons] at hn ⊢; omega
            have := ih _ hlen fas ((sb, ℓb) :: gbs) rfl (f0 + sa * ℓa) g0 (t - ℓa)
              hfas_sort hgsort hfas_le hgs
            rw [show f0 + g0 + sa * ℓa = f0 + sa * ℓa + g0 from by ring]
            exact this
        · -- `g`'s lead is the global min: peel it (via `minConv_comm`), recurse on `((sa,ℓa)::fas, gbs)`
          have hba : sb ≤ sa := (not_le.mp hab).le
          have hfall : ∀ seg ∈ (sa, ℓa) :: fas, sb ≤ seg.1 :=
            sorted_head_le_all hfsort rfl hba
          have hGrate : ∀ x d : ℝ≥0,
              convexSegEval f0 s ((sa, ℓa) :: fas) x + sb * d
                ≤ convexSegEval f0 s ((sa, ℓa) :: fas) (x + d) :=
            convexSegEval_rate_of_le hfall hsbs
          rw [mergeBySlope_cons_gt (show ¬ (sa, ℓa).1 ≤ (sb, ℓb).1 from hab)]
          by_cases ht : t ≤ ℓb
          · rw [convexSegEval_cons, if_pos ht, minConv_comm,
              minConv_leadSeg_le g0 s sb ℓb gbs _ hGrate ht, convexSegEval_zero]
            norm_cast; ring
          · have hℓbt : ℓb ≤ t := (not_le.mp ht).le
            rw [convexSegEval_cons, if_neg ht, minConv_comm,
              minConv_peel_leadSeg g0 s sb ℓb gbs _ hGrate hℓbt, minConv_comm]
            have hlen : ((sa, ℓa) :: fas).length + gbs.length < n := by
              simp only [List.length_cons] at hn ⊢; omega
            have := ih _ hlen ((sa, ℓa) :: fas) gbs rfl f0 (g0 + sb * ℓb) (t - ℓb)
              hfsort hgbs_sort hfs hgbs_le
            rw [show f0 + g0 + sb * ℓb = f0 + (g0 + sb * ℓb) from by ring]
            exact this

/-- **Theorem 4.1, balanced case (usable form).** Drops the recursion-fuel argument of
`minConv_convexSegEval_balanced`: for slope-sorted segment lists with all finite slopes `≤` the
shared asymptotic slope `s`, the `(min,plus)` convolution equals the `mergeBySlope` evaluation from
`f(0)+g(0)`. -/
theorem minConv_convexSegEval_eq_merge (s f0 g0 : ℝ≥0) (fsegs gsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs)
    (hgsort : List.Pairwise (fun a b => a.1 ≤ b.1) gsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ s) (hgs : ∀ seg ∈ gsegs, seg.1 ≤ s) (t : ℝ≥0) :
    minConv (fun u => (((convexSegEval f0 s fsegs u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval g0 s gsegs v : ℝ≥0) : ℝ) : EReal)) t
      = (((convexSegEval (f0 + g0) s (mergeBySlope fsegs gsegs) t : ℝ≥0) : ℝ) : EReal) :=
  (minConv_convexSegEval_balanced s _ fsegs gsegs rfl f0 g0 t hfsort hgsort hfs hgs).symm

/-- The balanced `mergeBySlope` is *untruncated*: it returns the whole slope-sorted concatenation,
length `fsegs.length + gsegs.length`, so every finite segment of both inputs survives into the
convolution result (no segments are dropped). -/
theorem mergeBySlope_length :
    ∀ fsegs gsegs : List (ℝ≥0 × ℝ≥0),
      (mergeBySlope fsegs gsegs).length = fsegs.length + gsegs.length
  | [], l => by simp
  | a :: as, [] => by simp
  | a :: as, b :: bs => by
      by_cases h : a.1 ≤ b.1
      · rw [mergeBySlope_cons_le h, List.length_cons,
          mergeBySlope_length as (b :: bs), List.length_cons, List.length_cons]
        ring
      · rw [mergeBySlope_cons_gt h, List.length_cons,
          mergeBySlope_length (a :: as) bs, List.length_cons, List.length_cons]
        ring
  termination_by l1 l2 => l1.length + l2.length
  decreasing_by all_goals (simp_wf; try omega)

end DeepWiki
