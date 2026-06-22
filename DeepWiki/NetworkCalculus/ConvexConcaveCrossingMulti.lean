import DeepWiki.NetworkCalculus.ConvexConcaveCrossingCoord

/-! # The full multi-segment tail of the Theorem 4.2 crossing coordinate (§4.2.2)
`ConvexConcaveCrossingCoord` pins the crossing offset `d*` (first `d` with the excess `E(d) = b`)
only for a **single** steep tail-segment `dropSegs r fsegs = [(s, ℓ)]`. This file generalizes to the
**full** steep tail `dropSegs r fsegs = [(s₁, ℓ₁), (s₂, ℓ₂), …]` (every `sₖ > r`), where the excess
`E` is piecewise-linear: on the k-th tail segment it has slope `(sₖ − r) > 0`, so by the time the
prefix of length `segLenSum (take k tail)` is traversed it has accumulated
`Σⱼ≤ₖ (sⱼ − r)·ℓⱼ`.

It delivers:
* **(1)** the per-segment **ramp values** at tail-segment boundaries: a fold `tailExcess r tail`
  (`= Σ (sⱼ − r)·ℓⱼ`) with `excess_eq_tailExcess_at_boundary`
  (`E(segLenSum (take k tail)) = tailExcess r (take k tail)`) — the structural heart.
* **(2)** **reachability**: `E(segLenSum tail) = tailExcess r tail` (total finite-tail excess) and,
  beyond the whole tail, growth at the asymptotic rate `(fs − r)`.
* **(3)** the recursive **multi-segment crossing offset** `crossingOffset r tail b` walking the tail,
  subtracting each `(sₖ − r)·ℓₖ` from `b` until a segment saturates, then `b_remaining/(sₖ − r)`
  inside it; `excess_crossingOffset` (`E(crossingOffset) = b` for reachable `b`) and the piecewise
  value of `f ∗ γ_{r,b}` below/above it. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## (1) The tail-excess fold and the ramp values at segment boundaries -/

/-- **Tail-excess fold.** Over a `(slope, length)` tail list (each slope `> r`), the cumulative
excess `Σ (sⱼ − r)·ℓⱼ` accrued by traversing the whole list at rate `r`: each segment of slope `s`
and length `ℓ` contributes `(s − r)·ℓ` above the rate-`r` line. -/
noncomputable def tailExcess (r : ℝ≥0) : List (ℝ≥0 × ℝ≥0) → ℝ≥0
  | [] => 0
  | (s, ℓ) :: rest => (s - r) * ℓ + tailExcess r rest

@[simp] theorem tailExcess_nil (r : ℝ≥0) : tailExcess r [] = 0 := rfl

@[simp] theorem tailExcess_cons (r s ℓ : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) :
    tailExcess r ((s, ℓ) :: rest) = (s - r) * ℓ + tailExcess r rest := rfl

/-- **Corner values of a slope-`≥ r` PWL, written as a rate-`r` ramp plus `tailExcess`.** For a
list `dt` whose every slope is `≥ r`, evaluating it at the cumulative length of any prefix
`take k dt` gives `g0 + r·(prefix length) + tailExcess r (take k dt)` — the rate-`r` line plus the
accumulated excess of the traversed segments. (Generic in the base `g0` and asymptote `fs`; the
asymptote is irrelevant on the kept prefix.) This is the structural identity behind every ramp
value. -/
theorem convexSegEval_eq_rate_add_tailExcess (fs r : ℝ≥0) :
    ∀ (dt : List (ℝ≥0 × ℝ≥0)), (∀ seg ∈ dt, r ≤ seg.1) → ∀ (g0 : ℝ≥0) (k : ℕ),
      convexSegEval g0 fs dt (segLenSum (dt.take k))
        = g0 + r * segLenSum (dt.take k) + tailExcess r (dt.take k) := by
  intro dt
  induction dt with
  | nil =>
      intro _ g0 k
      simp
  | cons hd tl ih =>
      intro hslopes g0 k
      obtain ⟨s, ℓ⟩ := hd
      have hs : r ≤ s := hslopes (s, ℓ) List.mem_cons_self
      have htl : ∀ seg ∈ tl, r ≤ seg.1 := fun seg h => hslopes seg (List.mem_cons_of_mem _ h)
      cases k with
      | zero => simp
      | succ k =>
          -- `take (k+1) ((s,ℓ)::tl) = (s,ℓ) :: take k tl`; peel the leading segment
          rw [List.take_succ_cons, segLenSum_cons, tailExcess_cons,
            convexSegEval_cons_peel, ih htl (g0 + s * ℓ) k]
          -- `g0 + s·ℓ + r·L + E = g0 + r·(ℓ + L) + ((s−r)·ℓ + E)`, using `s·ℓ = r·ℓ + (s−r)·ℓ`
          have hsℓ : s * ℓ = r * ℓ + (s - r) * ℓ := by
            rw [← add_mul, add_tsub_cancel_of_le hs]
          rw [hsℓ]; ring

/-- **The excess at a tail-segment boundary is the ramp value.** With `tail = dropSegs r fsegs`, at
the cumulative length of any prefix `take k tail` the excess equals the prefix's tail-excess:
`E(segLenSum (take k tail)) = tailExcess r (take k tail) = Σⱼ≤ₖ (sⱼ − r)·ℓⱼ`. This is the
piecewise-linear ramp of `E` read off at its breakpoints — the multi-segment generalization of
`excess_singleTail_at_end`. -/
theorem excess_eq_tailExcess_at_boundary (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs) (k : ℕ) :
    excess f0 fs r fsegs (segLenSum ((dropSegs r fsegs).take k))
      = tailExcess r ((dropSegs r fsegs).take k) := by
  set us := segLenSum (truncSegs r fsegs) with hus
  set fu := convexSegEval f0 fs fsegs us with hfu
  set dt := dropSegs r fsegs with hdt
  set d := segLenSum (dt.take k) with hd
  -- every tail segment has slope `≥ r`
  have hslopes : ∀ seg ∈ dt, r ≤ seg.1 := dropSegs_slope_ge (s := r) fsegs hfsort
  -- evaluate `f(u*+d)` via the split, then via the ramp form
  have hsplit := convexSegEval_split_truncSegs fs r fsegs f0 (t := us + d) (by rw [← hus]; exact le_self_add)
  rw [← hus, ← hfu, ← hdt, add_tsub_cancel_left] at hsplit
  have hramp := convexSegEval_eq_rate_add_tailExcess fs r dt hslopes fu k
  rw [← hd] at hramp
  -- `E(d) + (fu + r·d) = f(u*+d) = fu + r·d + tailExcess`, cancel `(fu + r·d)`
  have e := excess_add_eq f0 fs r fsegs hfsort hrf d
  rw [← hus, ← hfu, hsplit, hramp] at e
  have hcancel : excess f0 fs r fsegs d + (fu + r * d)
      = tailExcess r (dt.take k) + (fu + r * d) := by
    rw [e]; ring
  exact add_right_cancel hcancel

/-! ## (2) Reachability: the total finite-tail excess -/

/-- **Total finite-tail excess (reachability).** With `tail = dropSegs r fsegs`, the excess at the
end of the whole tail is `E(segLenSum tail) = tailExcess r tail = Σⱼ (sⱼ − r)·ℓⱼ` — the largest excess
the finite steep segments contribute. A burst `b` is reachable inside the finite tail iff
`b ≤ tailExcess r tail`. (The `k → length` case of `excess_eq_tailExcess_at_boundary`.) -/
theorem excess_segLenSum_tail (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs) :
    excess f0 fs r fsegs (segLenSum (dropSegs r fsegs)) = tailExcess r (dropSegs r fsegs) := by
  have h := excess_eq_tailExcess_at_boundary f0 fs r fsegs hfsort hrf (dropSegs r fsegs).length
  rwa [List.take_length] at h

/-- **Asymptotic growth beyond the whole tail.** Past the end of the steep tail
`U := u* + segLenSum (dropSegs r fsegs)` the convex PWL runs at its asymptote `fs`, so the excess
grows at the residual rate `(fs − r)`: `E(segLenSum tail + e) = tailExcess r tail + (fs − r)·e` for
every further offset `e`. (Past the finite segments `convexSegEval_past_segs` gives slope `fs`; the
rate-`r` line is subtracted off, leaving `(fs − r)`.) -/
theorem excess_past_tail (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs) (e : ℝ≥0) :
    excess f0 fs r fsegs (segLenSum (dropSegs r fsegs) + e)
      = tailExcess r (dropSegs r fsegs) + (fs - r) * e := by
  set us := segLenSum (truncSegs r fsegs) with hus
  set fu := convexSegEval f0 fs fsegs us with hfu
  set dt := dropSegs r fsegs with hdt
  set L := segLenSum dt with hL
  have hslopes : ∀ seg ∈ dt, r ≤ seg.1 := dropSegs_slope_ge (s := r) fsegs hfsort
  -- `f(u* + (L + e))` via the split, then `convexSegEval_past_segs` on the tail
  have hsplit := convexSegEval_split_truncSegs fs r fsegs f0
    (t := us + (L + e)) (by rw [← hus]; exact le_self_add)
  rw [← hus, ← hfu, ← hdt, add_tsub_cancel_left] at hsplit
  -- corner value of the tail at its full length is `fu + r·L + tailExcess r dt`
  have hcorner := convexSegEval_eq_rate_add_tailExcess fs r dt hslopes fu dt.length
  rw [List.take_length, ← hL] at hcorner
  have hpast := convexSegEval_past_segs fs dt fu (L + e) (by rw [← hL]; exact le_self_add)
  rw [← hL, add_tsub_cancel_left, hcorner] at hpast
  -- so `f(u* + (L + e)) = fu + r·L + tailExcess + fs·e`
  rw [hpast] at hsplit
  -- `E(L+e) + (fu + r·(L+e)) = f(u*+(L+e))`; cancel and read off
  have e0 := excess_add_eq f0 fs r fsegs hfsort hrf (L + e)
  rw [← hus, ← hfu, hsplit] at e0
  have hfsr : fs * e = r * e + (fs - r) * e := by
    rw [← add_mul, add_tsub_cancel_of_le hrf]
  have hcancel : excess f0 fs r fsegs (L + e) + (fu + r * (L + e))
      = (tailExcess r dt + (fs - r) * e) + (fu + r * (L + e)) := by
    rw [e0, hfsr]; ring
  exact add_right_cancel hcancel

end DeepWiki
