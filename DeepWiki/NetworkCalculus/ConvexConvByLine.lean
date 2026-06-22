import DeepWiki.NetworkCalculus.ConvexSegmentMergeTrunc

/-! # Lemma 4.1 core — convolution of a convex PWL by a single line
The engine of the book's Lemma 4.1 (§4.2.2): the `(min,plus)` convolution of a convex PWL
`f = convexSegEval f0 fs fsegs` by a single line `ℓ(u) = c + q·u` (= `convexSegEval c q []`,
no finite segments, asymptote `q`). Two regimes around the breakpoint `u*` (the cumulative
length of `f`'s segments of slope `< q`):
  • `t ≤ u*`:  `(f ∗ ℓ) t = f(t) + c`   (the line is steeper than `f` so far — `f` is kept);
  • `t ≥ u*`:  `(f ∗ ℓ) t = f(u*) + c + q·(t − u*)` (beyond `u*` the line's slope `q` wins).
The concave function's `j`-th piece in Lemma 4.1 is exactly such a line, so this is the
building block of the full concave/convex convolution. -/

namespace DeepWiki

open scoped NNReal

/-- `coeadd`: the `ℝ≥0 → ℝ → EReal` cast turns dioid `+` into addition, matching the idiom of
`minConv_affine`. -/
private theorem coeadd_byLine (x y : ℝ≥0) :
    (((x : ℝ) : EReal)) + (((y : ℝ) : EReal)) = (((x + y : ℝ≥0) : ℝ) : EReal) := by
  rw [← EReal.coe_add, ← NNReal.coe_add]

/-- **Steep line absorbed: `(f ∗ ℓ) t = f(t) + c`.** When the line `ℓ(u) = c + q·u` is at least as
steep as `f`'s asymptote (`fs ≤ q`, hence steeper than every finite slope of `f`), the `(min,plus)`
convolution keeps `f` and merely shifts it by the line's burst `c`: `(f ∗ ℓ) t = f(t) + c` for all
`t`. (The line never wins, so there is no breakpoint — `u* = ∞`.) -/
theorem minConv_convexSegEval_steepLine (f0 fs c q : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hfq : fs ≤ q) (t : ℝ≥0) :
    minConv (fun u => (((convexSegEval f0 fs fsegs u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval c q [] v : ℝ≥0) : ℝ) : EReal)) t
      = (((convexSegEval f0 fs fsegs t + c : ℝ≥0) : ℝ) : EReal) := by
  have hfsq : ∀ seg ∈ fsegs, seg.1 ≤ q := fun seg h => le_trans (hfs seg h) hfq
  apply le_antisymm
  · -- (≤) split `(t, 0)`: `f t + ℓ 0 = f t + c`
    refine le_trans (minConv_le_add _ _ (add_zero t)) (le_of_eq ?_)
    rw [convexSegEval_zero, coeadd_byLine]
  · -- (≥) any split `u + v = t`: `f t + c ≤ f u + (c + q·v)` by `f`'s upper-rate bound
    refine le_minConv (fun u v huv => ?_)
    rw [coeadd_byLine, convexSegEval_nil, EReal.coe_le_coe_iff, NNReal.coe_le_coe]
    have hup : convexSegEval f0 fs fsegs (u + v) ≤ convexSegEval f0 fs fsegs u + q * v :=
      convexSegEval_upper_rate fs q fsegs hfsq hfq f0 u v
    calc convexSegEval f0 fs fsegs t + c
        = convexSegEval f0 fs fsegs (u + v) + c := by rw [huv]
      _ ≤ (convexSegEval f0 fs fsegs u + q * v) + c := by gcongr
      _ = convexSegEval f0 fs fsegs u + (c + q * v) := by ring

/-- **Convolution by a line, merged form.** When the line `ℓ(u) = c + q·u` is no steeper than `f`'s
asymptote (`q ≤ fs`), the `(min,plus)` convolution `ℓ ∗ f` is the convex PWL based at `c + f(0)` with
asymptote `q` whose finite segments are exactly `f`'s segments of slope `≤ q` (truncation at `q`); the
steeper segments of `f` are absorbed into the line's slope `q`. -/
theorem minConv_line_convexSegEval (f0 fs c q : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hqf : q ≤ fs) (t : ℝ≥0) :
    minConv (fun u => (((convexSegEval c q [] u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) t
      = (((convexSegEval (c + f0) q (truncSegs q fsegs) t : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_convexSegEval_unbalanced q fs c f0 [] fsegs hqf List.Pairwise.nil hfsort
    (by simp) hfs t, mergeBySlope_nil_left]

/-- Shifting the base value by `c` shifts the whole convex PWL by `c`:
`convexSegEval (c + f0) fs l t = c + convexSegEval f0 fs l t`. -/
theorem convexSegEval_base_shift (c fs : ℝ≥0) (l : List (ℝ≥0 × ℝ≥0)) (f0 t : ℝ≥0) :
    convexSegEval (c + f0) fs l t = c + convexSegEval f0 fs l t := by
  induction l generalizing f0 t with
  | nil => rw [convexSegEval_nil, convexSegEval_nil]; ring
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      rw [convexSegEval_cons, convexSegEval_cons]
      split
      · ring
      · rw [show c + f0 + s * ℓ = c + (f0 + s * ℓ) from by ring, ih]

/-- Cumulative length of a `(slope, length)` segment list (the breakpoint coordinate). -/
noncomputable def segLenSum : List (ℝ≥0 × ℝ≥0) → ℝ≥0
  | [] => 0
  | (_, ℓ) :: rest => ℓ + segLenSum rest

@[simp] theorem segLenSum_nil : segLenSum [] = 0 := rfl

@[simp] theorem segLenSum_cons (s ℓ : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) :
    segLenSum ((s, ℓ) :: rest) = ℓ + segLenSum rest := rfl

/-- Below its last breakpoint, a convex PWL and any extension agreeing on its segments coincide: if
`t ≤ segLenSum l`, the asymptote is never reached, so `convexSegEval f0 fs l t = convexSegEval f0 fs' l t`
for any two asymptotes `fs`, `fs'`. (The finite segments alone determine the value on `[0, u*]`.) -/
theorem convexSegEval_asymp_irrel (fs fs' : ℝ≥0) :
    ∀ (l : List (ℝ≥0 × ℝ≥0)) (f0 t : ℝ≥0), t ≤ segLenSum l →
      convexSegEval f0 fs l t = convexSegEval f0 fs' l t := by
  intro l
  induction l with
  | nil =>
      intro f0 t ht
      rw [segLenSum_nil, nonpos_iff_eq_zero] at ht
      subst ht
      rw [convexSegEval_zero, convexSegEval_zero]
  | cons hd tl ih =>
      intro f0 t ht
      obtain ⟨s, ℓ⟩ := hd
      rw [convexSegEval_cons, convexSegEval_cons]
      split
      · rfl
      · rename_i hnt
        have hℓt : ℓ ≤ t := (not_le.mp hnt).le
        rw [segLenSum_cons] at ht
        apply ih
        rw [tsub_le_iff_left]
        exact ht

/-- Below the truncation cut the truncated and untruncated curves coincide: if
`t ≤ segLenSum (truncSegs q l)` then `convexSegEval f0 fs (truncSegs q l) t = convexSegEval f0 fs l t`.
(Truncating only drops the segments past the cut; on the kept prefix nothing changes.) -/
theorem convexSegEval_truncSegs_eq_below (q fs : ℝ≥0) :
    ∀ (l : List (ℝ≥0 × ℝ≥0)) (f0 t : ℝ≥0), t ≤ segLenSum (truncSegs q l) →
      convexSegEval f0 fs (truncSegs q l) t = convexSegEval f0 fs l t := by
  intro l
  induction l with
  | nil => intro f0 t _; rfl
  | cons hd tl ih =>
      intro f0 t ht
      obtain ⟨s, ℓ⟩ := hd
      by_cases hsq : s ≤ q
      · rw [truncSegs_cons_le hsq] at ht ⊢
        rw [convexSegEval_cons, convexSegEval_cons]
        split
        · rfl
        · rename_i hnt
          rw [segLenSum_cons] at ht
          apply ih
          rw [tsub_le_iff_left]
          exact ht
      · -- the whole leading segment is dropped, so `truncSegs q (...) = []` and `u* = 0`
        rw [truncSegs_cons_gt hsq] at ht ⊢
        rw [segLenSum_nil, nonpos_iff_eq_zero] at ht
        subst ht
        rw [convexSegEval_zero, convexSegEval_zero]

/-- Truncation can only shorten the cumulative length: `segLenSum (truncSegs q l) ≤ segLenSum l`. -/
theorem segLenSum_truncSegs_le (q : ℝ≥0) :
    ∀ l : List (ℝ≥0 × ℝ≥0), segLenSum (truncSegs q l) ≤ segLenSum l
  | [] => by simp
  | (s, ℓ) :: rest => by
      by_cases hsq : s ≤ q
      · rw [truncSegs_cons_le hsq, segLenSum_cons, segLenSum_cons]
        gcongr
        exact segLenSum_truncSegs_le q rest
      · rw [truncSegs_cons_gt hsq, segLenSum_nil]
        positivity

/-- **Convolution by a line — the short-time regime `t ≤ u*`.** With `u* = segLenSum (truncSegs q fsegs)`
the breakpoint where `f`'s slope first reaches `q`, for `t ≤ u*` the line is steeper than `f` so far,
so the convolution keeps `f`: `(ℓ ∗ f) t = f(t) + c`. -/
theorem minConv_line_convexSegEval_below (f0 fs c q : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hqf : q ≤ fs)
    {t : ℝ≥0} (ht : t ≤ segLenSum (truncSegs q fsegs)) :
    minConv (fun u => (((convexSegEval c q [] u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) t
      = (((convexSegEval f0 fs fsegs t + c : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_line_convexSegEval f0 fs c q fsegs hfsort hfs hqf t, convexSegEval_base_shift,
    convexSegEval_truncSegs_eq_below q q fsegs f0 t ht,
    convexSegEval_asymp_irrel q fs fsegs f0 t (le_trans ht (segLenSum_truncSegs_le q fsegs))]
  rw [add_comm]

/-- **Past the last breakpoint a convex PWL is its asymptote line.** For `t ≥ segLenSum l` the finite
segments are exhausted, so `convexSegEval f0 fs l t = convexSegEval f0 fs l (segLenSum l) + fs·(t − segLenSum l)`
— the value continues from the corner `f(u*)` at slope `fs`. -/
theorem convexSegEval_past_segs (fs : ℝ≥0) :
    ∀ (l : List (ℝ≥0 × ℝ≥0)) (f0 t : ℝ≥0), segLenSum l ≤ t →
      convexSegEval f0 fs l t
        = convexSegEval f0 fs l (segLenSum l) + fs * (t - segLenSum l) := by
  intro l
  induction l with
  | nil =>
      intro f0 t _
      rw [segLenSum_nil, convexSegEval_zero, tsub_zero, convexSegEval_nil]
  | cons hd tl ih =>
      intro f0 t ht
      obtain ⟨s, ℓ⟩ := hd
      rw [segLenSum_cons] at ht ⊢
      have hℓt : ℓ ≤ t := le_trans le_self_add ht
      have htst : segLenSum tl ≤ t - ℓ := by
        rw [le_tsub_iff_left hℓt]; exact ht
      -- peel the leading segment on both sides, then apply IH to the tail at `t - ℓ`
      have hpeelt : convexSegEval f0 fs ((s, ℓ) :: tl) t
          = convexSegEval (f0 + s * ℓ) fs tl (t - ℓ) := by
        rw [← convexSegEval_cons_peel f0 fs s ℓ (t - ℓ) tl, add_tsub_cancel_of_le hℓt]
      have hpeelc : convexSegEval f0 fs ((s, ℓ) :: tl) (ℓ + segLenSum tl)
          = convexSegEval (f0 + s * ℓ) fs tl (segLenSum tl) :=
        convexSegEval_cons_peel f0 fs s ℓ (segLenSum tl) tl
      rw [hpeelt, hpeelc, ih (f0 + s * ℓ) (t - ℓ) htst]
      congr 2
      rw [tsub_add_eq_tsub_tsub]

/-- **Convolution by a line — the long-time regime `t ≥ u*`.** With `u* = segLenSum (truncSegs q fsegs)`
the breakpoint where `f`'s slope first reaches `q`, for `t ≥ u*` the line's slope `q` has taken over:
`(ℓ ∗ f) t = f(u*) + c + q·(t − u*)` — the convolution runs at the line's slope `q` from the corner
`f(u*) + c`. -/
theorem minConv_line_convexSegEval_above (f0 fs c q : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hqf : q ≤ fs)
    {t : ℝ≥0} (ht : segLenSum (truncSegs q fsegs) ≤ t) :
    minConv (fun u => (((convexSegEval c q [] u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) t
      = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs q fsegs)) + c
            + q * (t - segLenSum (truncSegs q fsegs)) : ℝ≥0) : ℝ) : EReal) := by
  set us := segLenSum (truncSegs q fsegs) with hus
  -- evaluate the corner value `f(u*)` of the convolution result
  have hcorner : convexSegEval (c + f0) q (truncSegs q fsegs) us
      = convexSegEval f0 fs fsegs us + c := by
    rw [convexSegEval_base_shift, convexSegEval_truncSegs_eq_below q q fsegs f0 us le_rfl,
      convexSegEval_asymp_irrel q fs fsegs f0 us (segLenSum_truncSegs_le q fsegs), add_comm]
  rw [minConv_line_convexSegEval f0 fs c q fsegs hfsort hfs hqf t,
    convexSegEval_past_segs q (truncSegs q fsegs) (c + f0) t ht, ← hus, hcorner]

/-- Faithfulness check: at the breakpoint `t = u*` the two regimes agree (the `q·(t−u*)` term
vanishes), so `(ℓ ∗ f) u* = f(u*) + c` consistently. -/
example (f0 fs c q : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hqf : q ≤ fs) :
    minConv (fun u => (((convexSegEval c q [] u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal))
            (segLenSum (truncSegs q fsegs))
      = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs q fsegs)) + c : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_line_convexSegEval_below f0 fs c q fsegs hfsort hfs hqf le_rfl]

/-- Faithfulness check: the long-time regime at `t = u*` reduces to the corner value
`f(u*) + c` (the `q·(u*−u*) = 0` term drops). -/
example (f0 fs c q : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hqf : q ≤ fs) :
    minConv (fun u => (((convexSegEval c q [] u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal))
            (segLenSum (truncSegs q fsegs))
      = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs q fsegs)) + c : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_line_convexSegEval_above f0 fs c q fsegs hfsort hfs hqf le_rfl, tsub_self,
    mul_zero, add_zero]

/-- Faithfulness check: the steep-line and below-line theorems agree (via `minConv_comm`) — both say
that when the line is steeper (`fs ≤ q`, so `truncSegs q fsegs = fsegs` and `u* = segLenSum fsegs`)
the result is `f(t) + c` for every `t ≤ u*`. -/
example (f0 fs c q : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hfq : fs ≤ q) (t : ℝ≥0) :
    minConv (fun u => (((convexSegEval f0 fs fsegs u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval c q [] v : ℝ≥0) : ℝ) : EReal)) t
      = (((convexSegEval f0 fs fsegs t + c : ℝ≥0) : ℝ) : EReal) :=
  minConv_convexSegEval_steepLine f0 fs c q fsegs hfs hfq t

/-- Faithfulness check: a pure line `∗` a pure line recovers the affine base case — the breakpoint is
`u* = 0` (no segments below `q`), so the long-time regime gives `c + b + q·t` for the flatter slope. -/
example (c q b r t : ℝ≥0) (hqr : q ≤ r) :
    minConv (fun u => (((convexSegEval c q [] u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval b r [] v : ℝ≥0) : ℝ) : EReal)) t
      = (((b + c + q * t : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_line_convexSegEval_above b r c q [] List.Pairwise.nil (by simp) hqr (by simp)]
  simp

end DeepWiki
