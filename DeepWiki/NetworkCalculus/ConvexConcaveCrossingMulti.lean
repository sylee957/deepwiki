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

/-! ## (3) The recursive multi-segment crossing offset -/

/-- **The multi-segment crossing offset.** Walking the steep tail `tail = dropSegs r fsegs`, subtract
each segment's excess `(sₖ − r)·ℓₖ` from the remaining burst until a segment saturates it, then add
`b_remaining / (sₖ − r)` inside that segment: the first offset `d*` with `E(d*) = b`. The single-tail
case is `crossingOffset r [(s, ℓ)] b = b / (s − r)`. -/
noncomputable def crossingOffset (r : ℝ≥0) : List (ℝ≥0 × ℝ≥0) → ℝ≥0 → ℝ≥0
  | [], _ => 0
  | (s, ℓ) :: rest, b =>
      if b ≤ (s - r) * ℓ then b / (s - r) else ℓ + crossingOffset r rest (b - (s - r) * ℓ)

@[simp] theorem crossingOffset_nil (r b : ℝ≥0) : crossingOffset r [] b = 0 := rfl

theorem crossingOffset_cons (r s ℓ b : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) :
    crossingOffset r ((s, ℓ) :: rest) b
      = if b ≤ (s - r) * ℓ then b / (s - r)
        else ℓ + crossingOffset r rest (b - (s - r) * ℓ) := rfl

/-- **The crossing offset solves `f` for the burst, generically on a steep tail.** For a tail `dt`
whose every slope is `> r` (strict, so each `sₖ − r ≠ 0`), with `r ≤ fs` and a reachable burst
`b ≤ tailExcess r dt`, evaluating `dt` at the recursive crossing offset gives exactly the rate-`r`
line plus the full burst: `convexSegEval g0 fs dt (crossingOffset r dt b) = g0 + r·(offset) + b`.
(The structural core of `excess_crossingOffset`; the `excess` form follows by the split + cancel.) -/
theorem convexSegEval_crossingOffset (fs r : ℝ≥0) :
    ∀ (dt : List (ℝ≥0 × ℝ≥0)), (∀ seg ∈ dt, r < seg.1) → r ≤ fs →
      ∀ (g0 b : ℝ≥0), b ≤ tailExcess r dt →
        convexSegEval g0 fs dt (crossingOffset r dt b)
          = g0 + r * crossingOffset r dt b + b := by
  intro dt
  induction dt with
  | nil =>
      intro _ _ g0 b hb
      rw [tailExcess_nil, nonpos_iff_eq_zero] at hb
      subst hb
      simp
  | cons hd tl ih =>
      intro hslopes hrf g0 b hb
      obtain ⟨s, ℓ⟩ := hd
      have hrs : r < s := hslopes (s, ℓ) List.mem_cons_self
      have htl : ∀ seg ∈ tl, r < seg.1 := fun seg h => hslopes seg (List.mem_cons_of_mem _ h)
      rw [crossingOffset_cons]
      by_cases hbseg : b ≤ (s - r) * ℓ
      · -- crossing inside the leading segment: offset `δ = b/(s−r) ≤ ℓ`
        rw [if_pos hbseg]
        have hsr0 : (0 : ℝ≥0) < s - r := tsub_pos_of_lt hrs
        have hδℓ : b / (s - r) ≤ ℓ := by
          rw [div_le_iff₀ hsr0, mul_comm]; exact hbseg
        rw [convexSegEval_cons, if_pos hδℓ]
        -- `g0 + s·δ = g0 + r·δ + (s−r)·δ = g0 + r·δ + b`
        have hbval : (s - r) * (b / (s - r)) = b := by
          rw [mul_div_cancel₀]; exact hsr0.ne'
        have hsδ : s * (b / (s - r)) = r * (b / (s - r)) + (s - r) * (b / (s - r)) := by
          rw [← add_mul, add_tsub_cancel_of_le hrs.le]
        rw [hsδ, hbval]; ring
      · -- consume the leading segment, recurse on the tail with `b' = b − (s−r)·ℓ`
        rw [if_neg hbseg]
        set b' := b - (s - r) * ℓ with hb'
        have hb'le : b' ≤ tailExcess r tl := by
          rw [hb', tsub_le_iff_left]
          rw [tailExcess_cons] at hb; exact hb
        -- peel the leading segment, then IH on the tail at `b'`
        rw [convexSegEval_cons_peel, ih htl hrf (g0 + s * ℓ) b' hb'le]
        -- `g0 + s·ℓ + r·δ' + b' = g0 + r·(ℓ + δ') + b`, using `s·ℓ = r·ℓ + (s−r)·ℓ` and `b' + (s−r)·ℓ = b`
        have hbseg' : (s - r) * ℓ ≤ b := (not_le.mp hbseg).le
        have hb'add : b' + (s - r) * ℓ = b := by rw [hb', tsub_add_cancel_of_le hbseg']
        have hsℓ : s * ℓ = r * ℓ + (s - r) * ℓ := by
          rw [← add_mul, add_tsub_cancel_of_le hrs.le]
        rw [hsℓ, mul_add, ← hb'add]; ring

/-- **The multi-segment crossing hits the burst: `E(d*) = b`.** With `tail = dropSegs r fsegs` (all
slopes `> r` since they survived `dropSegs`), `r ≤ fs`, and a reachable `b ≤ tailExcess r tail`, the
recursive offset `d* = crossingOffset r tail b` satisfies `excess f0 fs r fsegs d* = b`. The
multi-segment generalization of `excess_singleTail_crossingOffset`. -/
theorem excess_crossingOffset (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    (hb : b ≤ tailExcess r (dropSegs r fsegs)) :
    excess f0 fs r fsegs (crossingOffset r (dropSegs r fsegs) b) = b := by
  set us := segLenSum (truncSegs r fsegs) with hus
  set fu := convexSegEval f0 fs fsegs us with hfu
  set dt := dropSegs r fsegs with hdt
  set d := crossingOffset r dt b with hd
  -- every tail segment has slope `> r`
  have hslopes : ∀ seg ∈ dt, r < seg.1 :=
    fun seg hseg => not_le.mp (dropSegs_slope_gt (s := r) fsegs hfsort seg hseg)
  -- evaluate `f(u*+d)` via the split, then the generic crossing identity
  have hsplit := convexSegEval_split_truncSegs fs r fsegs f0
    (t := us + d) (by rw [← hus]; exact le_self_add)
  rw [← hus, ← hfu, ← hdt, add_tsub_cancel_left] at hsplit
  have hcross := convexSegEval_crossingOffset fs r dt hslopes hrf fu b hb
  rw [← hd] at hcross
  -- `E(d) + (fu + r·d) = f(u*+d) = fu + r·d + b`, cancel
  have e := excess_add_eq f0 fs r fsegs hfsort hrf d
  rw [← hus, ← hfu, hsplit, hcross] at e
  have hcancel : excess f0 fs r fsegs d + (fu + r * d) = b + (fu + r * d) := by
    rw [e]; ring
  exact add_right_cancel hcancel

/-- **The crossing offset lands within the finite tail.** For a reachable burst
`b ≤ tailExcess r (dropSegs r fsegs)` (all tail slopes `> r`), the recursive offset
`d* = crossingOffset r tail b` satisfies `d* ≤ segLenSum tail`: the crossing is reached before the
finite segments run out (so `u** = u* + d*` is still inside the steep tail). -/
theorem crossingOffset_le_segLenSum (r : ℝ≥0) :
    ∀ (dt : List (ℝ≥0 × ℝ≥0)), (∀ seg ∈ dt, r < seg.1) →
      ∀ b : ℝ≥0, b ≤ tailExcess r dt → crossingOffset r dt b ≤ segLenSum dt := by
  intro dt
  induction dt with
  | nil => intro _ b _; simp
  | cons hd tl ih =>
      intro hslopes b hb
      obtain ⟨s, ℓ⟩ := hd
      have hrs : r < s := hslopes (s, ℓ) List.mem_cons_self
      have htl : ∀ seg ∈ tl, r < seg.1 := fun seg h => hslopes seg (List.mem_cons_of_mem _ h)
      rw [crossingOffset_cons, segLenSum_cons]
      by_cases hbseg : b ≤ (s - r) * ℓ
      · -- inside the leading segment: `b/(s−r) ≤ ℓ ≤ ℓ + segLenSum tl`
        rw [if_pos hbseg]
        refine le_trans ?_ le_self_add
        rw [div_le_iff₀ (tsub_pos_of_lt hrs), mul_comm]; exact hbseg
      · -- consume the leading segment, recurse
        rw [if_neg hbseg]
        have hb'le : b - (s - r) * ℓ ≤ tailExcess r tl := by
          rw [tsub_le_iff_left]; rw [tailExcess_cons] at hb; exact hb
        exact add_le_add le_rfl (ih htl (b - (s - r) * ℓ) hb'le)

/-! ## The explicit piecewise value at the multi-segment crossing `u** = u* + d*` -/

/-- **The explicit crossing value, slack side (full tail).** With `u** = u* + crossingOffset r tail b`
for the full steep tail `tail = dropSegs r fsegs` and reachable `b ≤ tailExcess r tail`: for
`u* ≤ t ≤ u**` the bucket is slack and `f ∗ γ_{r,b} t = f t`. The threshold `u**` is explicit — its
offset is the recursive `crossingOffset`. -/
theorem minConv_tbEReal_eq_f_below_crossing_multi (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    (hb : b ≤ tailExcess r (dropSegs r fsegs))
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t)
    (htu : t ≤ segLenSum (truncSegs r fsegs) + crossingOffset r (dropSegs r fsegs) b) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal) := by
  apply minConv_tbEReal_eq_f_of_excess_le f0 fs r b fsegs hfsort hfs hrf ht
  set us := segLenSum (truncSegs r fsegs) with hus
  -- `t − u* ≤ d*`, so `E(t − u*) ≤ E(d*) = b` by monotonicity
  have hle : t - us ≤ crossingOffset r (dropSegs r fsegs) b := by
    rw [hus] at htu ⊢; exact tsub_le_iff_left.mpr htu
  calc excess f0 fs r fsegs (t - us)
      ≤ excess f0 fs r fsegs (crossingOffset r (dropSegs r fsegs) b) :=
        excess_mono f0 fs r fsegs hfsort hrf hle
    _ = b := excess_crossingOffset f0 fs r b fsegs hfsort hrf hb

/-- **The explicit crossing value, binding side (full tail).** With `u** = u* + crossingOffset r tail b`
and reachable `b ≤ tailExcess r tail`: for `t ≥ u**` the bucket binds and
`f ∗ γ_{r,b} t = f(u*) + b + r·(t − u*)`. Together with `minConv_tbEReal_eq_f_below_crossing` this is
Theorem 4.2 for the full multi-segment tail, with the switch coordinate `u**` written out. -/
theorem minConv_tbEReal_eq_line_above_crossing_multi (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    (hb : b ≤ tailExcess r (dropSegs r fsegs))
    {t : ℝ≥0}
    (htu : segLenSum (truncSegs r fsegs) + crossingOffset r (dropSegs r fsegs) b ≤ t) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * (t - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal) := by
  set us := segLenSum (truncSegs r fsegs) with hus
  have ht : us ≤ t := le_trans le_self_add htu
  apply minConv_tbEReal_eq_line_of_le_excess f0 fs r b fsegs hfsort hfs hrf ht
  -- `b = E(d*) ≤ E(t − u*)` by monotonicity, since `d* ≤ t − u*`
  have hle : crossingOffset r (dropSegs r fsegs) b ≤ t - us := by
    rw [le_tsub_iff_left ht, hus]; exact htu
  calc b = excess f0 fs r fsegs (crossingOffset r (dropSegs r fsegs) b) :=
        (excess_crossingOffset f0 fs r b fsegs hfsort hrf hb).symm
    _ ≤ excess f0 fs r fsegs (t - us) := excess_mono f0 fs r fsegs hfsort hrf hle

/-! ## Faithfulness checks -/

/-- Faithfulness: the excess ramp value at a tail-segment boundary is the partial tail-excess sum. -/
example (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs) (k : ℕ) :
    excess f0 fs r fsegs (segLenSum ((dropSegs r fsegs).take k))
      = tailExcess r ((dropSegs r fsegs).take k) :=
  excess_eq_tailExcess_at_boundary f0 fs r fsegs hfsort hrf k

/-- Faithfulness: the total finite-tail excess is `tailExcess r tail`, and `E` then grows at the
residual rate `(fs − r)` on the asymptote. -/
example (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs) (e : ℝ≥0) :
    excess f0 fs r fsegs (segLenSum (dropSegs r fsegs)) = tailExcess r (dropSegs r fsegs)
      ∧ excess f0 fs r fsegs (segLenSum (dropSegs r fsegs) + e)
          = tailExcess r (dropSegs r fsegs) + (fs - r) * e :=
  ⟨excess_segLenSum_tail f0 fs r fsegs hfsort hrf,
    excess_past_tail f0 fs r fsegs hfsort hrf e⟩

/-- Faithfulness: the recursive multi-segment crossing offset hits the burst exactly, `E(d*) = b`. -/
example (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    (hb : b ≤ tailExcess r (dropSegs r fsegs)) :
    excess f0 fs r fsegs (crossingOffset r (dropSegs r fsegs) b) = b :=
  excess_crossingOffset f0 fs r b fsegs hfsort hrf hb

/-- Faithfulness: the single-tail special case agrees with `ConvexConcaveCrossingCoord`. The
multi-segment `crossingOffset r [(s, ℓ)] b` reduces to `b / (s − r)` when `b ≤ (s − r)·ℓ`, matching
`crossingOffset_singleTail r s b`. -/
example (r s ℓ b : ℝ≥0) (hb : b ≤ (s - r) * ℓ) :
    crossingOffset r [(s, ℓ)] b = crossingOffset_singleTail r s b := by
  rw [crossingOffset_cons, if_pos hb, crossingOffset_singleTail]

/-- Faithfulness: at the explicit crossing `t = u** = u* + d*` the two regimes agree — the slack
form `f t` and the binding form `f(u*) + b + r·(t − u*)` give the same value (the meet is
single-valued at the crossing) for the full multi-segment tail. -/
example (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    (hb : b ≤ tailExcess r (dropSegs r fsegs)) :
    (((convexSegEval f0 fs fsegs
          (segLenSum (truncSegs r fsegs) + crossingOffset r (dropSegs r fsegs) b) : ℝ≥0) : ℝ)
        : EReal)
      = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * ((segLenSum (truncSegs r fsegs) + crossingOffset r (dropSegs r fsegs) b)
                - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal) := by
  have hf := minConv_tbEReal_eq_f_below_crossing_multi f0 fs r b fsegs hfsort hfs hrf hb
    (t := segLenSum (truncSegs r fsegs) + crossingOffset r (dropSegs r fsegs) b)
    le_self_add le_rfl
  have hline := minConv_tbEReal_eq_line_above_crossing_multi f0 fs r b fsegs hfsort hfs hrf hb
    (t := segLenSum (truncSegs r fsegs) + crossingOffset r (dropSegs r fsegs) b) le_rfl
  rw [hf] at hline
  exact hline

end DeepWiki
