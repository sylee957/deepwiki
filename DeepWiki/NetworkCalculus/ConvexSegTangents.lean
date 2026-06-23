import DeepWiki.NetworkCalculus.PwlThetaDecomp
import DeepWiki.NetworkCalculus.PwlBreakpoints
import DeepWiki.NetworkCalculus.ConvexPWLNormalForm
import DeepWiki.NetworkCalculus.ConvexSegmentMerge

/-! # Prop 4.4 [4.13], convex companion — `f̲ = ⨆ᵢ β_{sᵢ, Tᵢ}` from segment tangents
The convex side of [4.13]: a slope-sorted convex PWL `f̲ = convexSegEval f0 fs segs` is the
pointwise *supremum of its segment tangent rate-latencies*, `f̲ = ⨆ᵢ β_{sᵢ, Tᵢ}` ("a convex
function is the sup of its tangent lines"). The `≤` inclusion and the asymptotic-region equality
live in `PwlThetaDecomp` (`convexNFEval_le_convexSegEval`, `convexNFEval_eq_past_rank_of_mem_tangent`);
this file adds the **per-segment `≥`**.

* **Segment-affine value.** On its `i`-th finite segment `[τᵢ, τᵢ+ℓᵢ]` (slope `sᵢ`) the curve is
  exactly the affine piece `f̲(t) = f̲(τᵢ) + sᵢ·(t − τᵢ)` (`convexSegEval_affine_on_seg`).
* **Per-segment tangent latency** `segTangentLatency`: `Tᵢ = τᵢ − f̲(τᵢ)/sᵢ`, the x-intercept of
  segment `i`'s affine extension. On segment `i` (with `sᵢ > 0`) the tangent reaches the curve,
  `β_{sᵢ, Tᵢ}(t) = f̲(t)` (`rateLatencyEReal_segTangent_eq_on_seg`).
* **The `≥` direction and full equality.** Combined with `PwlThetaDecomp`'s `≤`, the tangent
  generators (segment tangents + the asymptotic tangent) realise `f̲` exactly on all of `[0,∞)`
  when every slope is positive (`convexNFEval_eq_convexSegEval`). -/

namespace DeepWiki

open scoped Classical NNReal

/-- The `ℝ≥0` truncated subtraction, read in `ℝ`, is the relu `max (x − T) 0`. (Local copy of the
private helper in `ConvexPWLNormalForm`.) -/
private theorem coe_tsub_eq_max' (x T : ℝ≥0) : ((x - T : ℝ≥0) : ℝ) = max ((x : ℝ) - T) 0 := by
  rcases le_total T x with h | h
  · rw [NNReal.coe_sub h, max_eq_left (by have := NNReal.coe_le_coe.mpr h; linarith)]
  · rw [tsub_eq_zero_of_le h, NNReal.coe_zero,
      max_eq_right (by have := NNReal.coe_le_coe.mpr h; linarith)]

/-! ## Segment-affine value: the curve is its affine piece on each segment

A convex PWL split as `segs = pre ++ (s, ℓ) :: post` is affine of slope `s` on the `pre`-anchored
segment `[segLenSum pre, segLenSum pre + ℓ]`. -/

/-- **The curve is affine on each finite segment.** Splitting `segs = pre ++ (s, ℓ) :: post`, the
segment after the cumulative length `τ = segLenSum pre` has slope `s`; for `τ ≤ t ≤ τ + ℓ` the curve
is the affine piece `f̲(t) = f̲(τ) + s·(t − τ)`. -/
theorem convexSegEval_affine_on_seg (f0 fs s ℓ : ℝ≥0) (pre post : List (ℝ≥0 × ℝ≥0)) {t : ℝ≥0}
    (hlo : segLenSum pre ≤ t) (hhi : t ≤ segLenSum pre + ℓ) :
    convexSegEval f0 fs (pre ++ (s, ℓ) :: post) t
      = convexSegEval f0 fs (pre ++ (s, ℓ) :: post) (segLenSum pre) + s * (t - segLenSum pre) := by
  induction pre generalizing f0 t with
  | nil =>
      -- `τ = 0`, the leading segment is `(s, ℓ)`; for `t ≤ ℓ` the value is `f0 + s·t`
      simp only [List.nil_append, segLenSum_nil, tsub_zero, convexSegEval_zero] at *
      rw [zero_add] at hhi
      rw [convexSegEval_cons, if_pos hhi]
  | cons hd tl ih =>
      obtain ⟨sa, ℓa⟩ := hd
      rw [List.cons_append, segLenSum_cons]
      rw [segLenSum_cons] at hlo hhi
      have hℓat : ℓa ≤ t := le_trans le_self_add hlo
      -- peel the leading `(sa, ℓa)` segment, apply IH to the tail at `t - ℓa`
      have hpeel : convexSegEval f0 fs ((sa, ℓa) :: (tl ++ (s, ℓ) :: post)) t
          = convexSegEval (f0 + sa * ℓa) fs (tl ++ (s, ℓ) :: post) (t - ℓa) := by
        rw [← convexSegEval_cons_peel f0 fs sa ℓa (t - ℓa) (tl ++ (s, ℓ) :: post),
          add_tsub_cancel_of_le hℓat]
      have hpeelτ : convexSegEval f0 fs ((sa, ℓa) :: (tl ++ (s, ℓ) :: post)) (ℓa + segLenSum tl)
          = convexSegEval (f0 + sa * ℓa) fs (tl ++ (s, ℓ) :: post) (segLenSum tl) :=
        convexSegEval_cons_peel f0 fs sa ℓa (segLenSum tl) (tl ++ (s, ℓ) :: post)
      have hlo' : segLenSum tl ≤ t - ℓa := by rw [le_tsub_iff_left hℓat]; exact hlo
      have hhi' : t - ℓa ≤ segLenSum tl + ℓ := by
        rw [tsub_le_iff_left]
        refine le_trans hhi (le_of_eq ?_); ring
      rw [hpeel, hpeelτ, ih (f0 + sa * ℓa) hlo' hhi']
      -- `t - ℓa - segLenSum tl = t - (ℓa + segLenSum tl)`
      rw [tsub_tsub]

/-- **The curve value at the start of a segment depends only on the prefix.** Splitting
`segs = pre ++ rest`, the value at the cumulative length `τ = segLenSum pre` is the value of the
prefix curve there: `f̲(τ) = convexSegEval f0 fs pre τ = f0 + cornerSum pre`. (The suffix segments
start after `τ`, so they do not affect the value at `τ`.) -/
theorem convexSegEval_append_at_segLenSum (f0 fs : ℝ≥0) (pre rest : List (ℝ≥0 × ℝ≥0)) :
    convexSegEval f0 fs (pre ++ rest) (segLenSum pre) = f0 + cornerSum pre := by
  induction pre generalizing f0 with
  | nil => simp
  | cons hd tl ih =>
      obtain ⟨sa, ℓa⟩ := hd
      rw [segLenSum_cons, cornerSum_cons, List.cons_append,
        convexSegEval_cons_peel, ih]
      ring

/-- **Peel the whole prefix.** For `t ≥ τ = segLenSum pre`, the curve restarts from the corner value
`v = f̲(τ) = f0 + cornerSum pre` on the suffix: `f̲(t) = convexSegEval v fs suf (t − τ)`. (Iterated
`convexSegEval_cons_peel`; local copy avoiding the `ConvexSegEvalSplit` import.) -/
theorem convexSegEval_append_peel_at (f0 fs : ℝ≥0) (pre suf : List (ℝ≥0 × ℝ≥0)) {t : ℝ≥0}
    (ht : segLenSum pre ≤ t) :
    convexSegEval f0 fs (pre ++ suf) t
      = convexSegEval (f0 + cornerSum pre) fs suf (t - segLenSum pre) := by
  induction pre generalizing f0 t with
  | nil => simp
  | cons hd tl ih =>
      obtain ⟨sa, ℓa⟩ := hd
      rw [segLenSum_cons] at ht ⊢
      have hℓat : ℓa ≤ t := le_trans le_self_add ht
      have htl : segLenSum tl ≤ t - ℓa := by rw [le_tsub_iff_left hℓat]; exact ht
      rw [List.cons_append, cornerSum_cons,
        show t = ℓa + (t - ℓa) from (add_tsub_cancel_of_le hℓat).symm,
        convexSegEval_cons_peel f0 fs sa ℓa (t - ℓa) (tl ++ suf),
        ih (f0 + sa * ℓa) htl, tsub_tsub,
        show f0 + sa * ℓa + cornerSum tl = f0 + (sa * ℓa + cornerSum tl) from by ring]
      congr 2
      rw [add_tsub_cancel_of_le hℓat]

/-- **Below the prefix length the suffix is irrelevant.** For `t ≤ τ = segLenSum pre`, the value of
`convexSegEval f0 fs (pre ++ suf)` is determined by the prefix alone:
`f̲(t) = convexSegEval f0 fs pre t`. (The suffix segments start only after `τ`.) -/
theorem convexSegEval_append_below (f0 fs : ℝ≥0) (pre suf : List (ℝ≥0 × ℝ≥0)) {t : ℝ≥0}
    (ht : t ≤ segLenSum pre) :
    convexSegEval f0 fs (pre ++ suf) t = convexSegEval f0 fs pre t := by
  induction pre generalizing f0 t with
  | nil =>
      rw [segLenSum_nil, nonpos_iff_eq_zero] at ht
      subst ht; simp
  | cons hd tl ih =>
      obtain ⟨sa, ℓa⟩ := hd
      rw [segLenSum_cons] at ht
      rw [List.cons_append, convexSegEval_cons, convexSegEval_cons]
      split
      · rfl
      · rename_i hnt
        have hℓat : ℓa ≤ t := (not_le.mp hnt).le
        exact ih (f0 + sa * ℓa) (by rw [tsub_le_iff_left]; exact ht)

/-! ## Per-segment tangent latency and own-segment exactness -/

/-- The **per-segment tangent latency** of segment `i` (split `segs = pre ++ (s, ℓ) :: post`, with
`τ = segLenSum pre`, `v = f̲(τ) = f0 + cornerSum pre`): `Tᵢ = τ − v/s`, the abscissa where segment
`i`'s affine extension (slope `s` through `(τ, v)`) crosses zero. Depends only on the prefix `pre`
(and `f0`), not on the segment or what follows. -/
noncomputable def segTangentLatency (f0 : ℝ≥0) (pre : List (ℝ≥0 × ℝ≥0)) (s : ℝ≥0) : ℝ≥0 :=
  segLenSum pre - (f0 + cornerSum pre) / s

/-- **The prefix corner sum is dominated by `s·τ` when every prefix slope is `≤ s`.**
`cornerSum pre = Σⱼ sⱼ·ℓⱼ ≤ s · Σⱼ ℓⱼ = s · segLenSum pre`: with `pre`'s slopes all `≤` segment
`i`'s slope `s` (slope-sorting), the prefix never rises faster than slope `s`. -/
theorem cornerSum_le_mul_segLenSum (s : ℝ≥0) (pre : List (ℝ≥0 × ℝ≥0))
    (hpre : ∀ seg ∈ pre, seg.1 ≤ s) : cornerSum pre ≤ s * segLenSum pre := by
  induction pre with
  | nil => simp
  | cons hd tl ih =>
      obtain ⟨sj, ℓj⟩ := hd
      have hsj : sj ≤ s := hpre (sj, ℓj) List.mem_cons_self
      have htl : ∀ seg ∈ tl, seg.1 ≤ s := fun seg h => hpre seg (List.mem_cons_of_mem _ h)
      rw [cornerSum_cons, segLenSum_cons, mul_add]
      gcongr
      exact ih htl

/-- **The segment-`i` tangent has a nonnegative latency when `f0 = 0` and `pre`'s slopes are `≤ s`.**
`v/s = cornerSum pre / s ≤ segLenSum pre = τ`, so `Tᵢ = τ − v/s` is the genuine (uncapped)
x-intercept of segment `i`'s affine extension. -/
theorem div_corner_le_segLenSum (s : ℝ≥0) (pre : List (ℝ≥0 × ℝ≥0))
    (hpre : ∀ seg ∈ pre, seg.1 ≤ s) (hs : 0 < s) :
    (0 + cornerSum pre) / s ≤ segLenSum pre := by
  rw [zero_add, div_le_iff₀ hs, mul_comm]
  exact cornerSum_le_mul_segLenSum s pre hpre

/-- **Own-segment exactness — the segment-`i` tangent equals the curve on segment `i`.** Splitting
`segs = pre ++ (s, ℓ) :: post` with `s > 0` and the well-formedness bound `v/s ≤ τ`
(`v = f0 + cornerSum pre`, `τ = segLenSum pre`), the tangent rate-latency `β_{s, Tᵢ}` anchored at
`Tᵢ = segTangentLatency f0 pre s` reproduces the curve for `t` in segment `i` (`τ ≤ t ≤ τ + ℓ`):
`β_{s, Tᵢ}(t) = s·(t − Tᵢ) = v + s·(t − τ) = f̲(t)`. The single sloped generator that *is* the affine
piece on its own segment. -/
theorem rateLatencyEReal_segTangent_eq_on_seg (f0 fs s ℓ : ℝ≥0) (pre post : List (ℝ≥0 × ℝ≥0))
    (hs : 0 < s) (hdiv : (f0 + cornerSum pre) / s ≤ segLenSum pre)
    {t : ℝ≥0} (hlo : segLenSum pre ≤ t) (hhi : t ≤ segLenSum pre + ℓ) :
    rateLatencyEReal s (segTangentLatency f0 pre s) t
      = (((convexSegEval f0 fs (pre ++ (s, ℓ) :: post) t : ℝ≥0) : ℝ) : EReal) := by
  set τ := segLenSum pre with hτ
  set v := f0 + cornerSum pre with hv
  rw [rateLatencyEReal_apply]
  congr 1
  rw [NNReal.coe_inj]
  -- the curve is the affine piece `v + s·(t − τ)` on this segment
  rw [convexSegEval_affine_on_seg f0 fs s ℓ pre post hlo hhi,
    convexSegEval_append_at_segLenSum, ← hv, ← hτ]
  -- `t − Tᵢ = (t − τ) + v/s` since `v/s ≤ τ ≤ t`
  rw [segTangentLatency, ← hτ, ← hv]
  have hsub : t - (τ - v / s) = (t - τ) + v / s := by
    rw [tsub_tsub_assoc hlo hdiv, add_comm]
  rw [hsub, mul_add, mul_div_cancel₀ v (ne_of_gt hs)]
  ring

/-! ## The segment tangent lies below the curve everywhere (the convex `≤`)

A tangent to a convex function lies below it: the segment-`i` tangent `β_{s, Tᵢ}` is `≤ f̲`
everywhere, not just on segment `i`. With `pre`'s slopes `≤ s` (slope-sorting), the curve rises at
rate `≤ s` before `τ`; with the suffix slopes `≥ s` (and `s ≤ fs`), it rises at rate `≥ s` after.
Both bounds pinch the tangent below the curve. -/

/-- **A segment tangent lies below the curve everywhere.** For `s > 0`, with the prefix slopes `≤ s`
(`hpre`), the suffix slopes `≥ s` (`hsuf`), `s ≤ fs`, and the well-formedness bound `v/s ≤ τ`, the
tangent rate-latency `β_{s, Tᵢ}` is `≤ ↑f̲` everywhere: `β_{s,Tᵢ}(t) = s·(t − Tᵢ) ≤ f̲(t)` for all
`t`. (A tangent to a convex function never crosses above it.) -/
theorem rateLatencyEReal_segTangent_le (f0 fs s ℓ : ℝ≥0) (pre post : List (ℝ≥0 × ℝ≥0))
    (hs : 0 < s) (hpre : ∀ seg ∈ pre, seg.1 ≤ s) (hsuf : ∀ seg ∈ (s, ℓ) :: post, s ≤ seg.1)
    (hsfs : s ≤ fs) (hdiv : (f0 + cornerSum pre) / s ≤ segLenSum pre) (t : ℝ≥0) :
    rateLatencyEReal s (segTangentLatency f0 pre s) t
      ≤ (((convexSegEval f0 fs (pre ++ (s, ℓ) :: post) t : ℝ≥0) : ℝ) : EReal) := by
  set τ := segLenSum pre with hτ
  set v := f0 + cornerSum pre with hv
  rw [rateLatencyEReal_apply, EReal.coe_le_coe_iff, segTangentLatency, ← hτ, ← hv]
  -- the latency `T = τ − v/s`; reduce to `(s : ℝ)·max(t − T, 0) ≤ (f̲ t : ℝ)`
  rw [NNReal.coe_mul, coe_tsub_eq_max']
  set fval : ℝ := (convexSegEval f0 fs (pre ++ (s, ℓ) :: post) t : ℝ) with hfval
  have hfnn : (0 : ℝ) ≤ fval := (convexSegEval f0 fs (pre ++ (s, ℓ) :: post) t).coe_nonneg
  rcases le_total t τ with htle | htge
  · -- below `τ`: upper-rate caps the curve, so the tangent stays below
    -- `f̲ t = convexSegEval f0 s pre t` (suffix irrelevant; asymptote irrelevant)
    have hfeq : fval = (convexSegEval f0 s pre t : ℝ) := by
      rw [hfval, convexSegEval_append_below f0 fs pre _ htle,
        convexSegEval_asymp_irrel fs s pre f0 t htle]
    -- upper-rate from `t` to `τ`: `v ≤ f̲ t + s·(τ − t)`
    have hupper : convexSegEval f0 s pre τ ≤ convexSegEval f0 s pre t + s * (τ - t) := by
      have := (@convexSegEval_upper_rate_of_le s f0 pre hpre) t (τ - t)
      rwa [add_tsub_cancel_of_le htle] at this
    have hvτ : convexSegEval f0 s pre τ = v := by
      rw [hv, ← convexSegEval_pwlRank f0 s pre]; rfl
    rw [hvτ] at hupper
    -- now in `ℝ`: `v ≤ f̲ t + s·(τ − t)`
    have hupperR : (v : ℝ) ≤ (convexSegEval f0 s pre t : ℝ) + (s : ℝ) * ((τ : ℝ) - (t : ℝ)) := by
      have := NNReal.coe_le_coe.mpr hupper
      push_cast [NNReal.coe_sub htle] at this ⊢
      linarith
    have hTr : ((τ - v / s : ℝ≥0) : ℝ) = (τ : ℝ) - (v : ℝ) / (s : ℝ) := by
      rw [NNReal.coe_sub hdiv, NNReal.coe_div]
    rw [hfeq, hTr, mul_max_of_nonneg _ _ s.coe_nonneg, mul_zero]
    apply max_le
    · -- `s·(t − T) = s·(t − τ) + v ≤ f̲ t` (the negative `t − τ` cancels `s·(τ − t)`)
      have hsvs : (s : ℝ) * ((v : ℝ) / (s : ℝ)) = (v : ℝ) := by field_simp
      have hexp : (s : ℝ) * ((t : ℝ) - ((τ : ℝ) - (v : ℝ) / (s : ℝ)))
          = (s : ℝ) * ((t : ℝ) - (τ : ℝ)) + (v : ℝ) := by
        rw [mul_sub, mul_sub, hsvs]; ring
      rw [hexp]; nlinarith [hupperR]
    · exact (convexSegEval f0 s pre t).coe_nonneg
  · -- past `τ`: lower-rate (suffix slopes `≥ s`) makes the curve rise at least at rate `s`
    -- `f̲ t = convexSegEval v fs ((s,ℓ)::post) (t − τ)`
    have hfeq : fval = (convexSegEval v fs ((s, ℓ) :: post) (t - τ) : ℝ) := by
      rw [hfval, convexSegEval_append_peel_at f0 fs pre _ htge, ← hv, ← hτ]
    -- lower-rate from `0` to `t − τ`: `v + s·(t − τ) ≤ f̲ t`
    have hlower : convexSegEval v fs ((s, ℓ) :: post) 0 + s * (t - τ)
        ≤ convexSegEval v fs ((s, ℓ) :: post) (0 + (t - τ)) :=
      convexSegEval_rate fs s ((s, ℓ) :: post) hsuf hsfs v 0 (t - τ)
    rw [zero_add, convexSegEval_zero] at hlower
    have hlowerR : (v : ℝ) + (s : ℝ) * ((t : ℝ) - (τ : ℝ))
        ≤ (convexSegEval v fs ((s, ℓ) :: post) (t - τ) : ℝ) := by
      have := NNReal.coe_le_coe.mpr hlower
      push_cast [NNReal.coe_sub htge] at this ⊢
      linarith
    have hTr : ((τ - v / s : ℝ≥0) : ℝ) = (τ : ℝ) - (v : ℝ) / (s : ℝ) := by
      rw [NNReal.coe_sub hdiv, NNReal.coe_div]
    rw [hfeq, hTr, mul_max_of_nonneg _ _ s.coe_nonneg, mul_zero]
    apply max_le
    · -- `s·(t − T) = s·(t − τ) + v` (genuine since `T ≤ τ ≤ t`)
      have hsvs : (s : ℝ) * ((v : ℝ) / (s : ℝ)) = (v : ℝ) := by field_simp
      have hexp : (s : ℝ) * ((t : ℝ) - ((τ : ℝ) - (v : ℝ) / (s : ℝ)))
          = (s : ℝ) * ((t : ℝ) - (τ : ℝ)) + (v : ℝ) := by
        rw [mul_sub, mul_sub, hsvs]; ring
      rw [hexp]; linarith [hlowerR]
    · exact (convexSegEval v fs ((s, ℓ) :: post) (t - τ)).coe_nonneg

/-! ## Assembling the full equality `f̲ = ⨆ᵢ β_{sᵢ, Tᵢ}`

Combining the two directions: if every generator lies below the curve (`≤`) and at each point some
generator reaches it (`≥`), the convex sup-of-tangents `convexNFEval gens` equals `↑f̲` everywhere.
The concrete tangent generators (segment tangents + the asymptotic tangent) satisfy both. -/

/-- **The convex sup is below the curve when every generator is.** If each `g ∈ gens` lies below
`↑f̲` at `t`, so does their supremum `convexNFEval gens t`. (The `≤` half of the assembly.) -/
theorem convexNFEval_le_of_forall_le (f0 fs : ℝ≥0) (segs gens : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0)
    (hle : ∀ g ∈ gens,
      rateLatencyEReal g.1 g.2 t ≤ (((convexSegEval f0 fs segs t : ℝ≥0) : ℝ) : EReal)) :
    convexNFEval gens t ≤ (((convexSegEval f0 fs segs t : ℝ≥0) : ℝ) : EReal) := by
  induction gens with
  | nil => rw [convexNFEval_nil]; exact bot_le
  | cons g gs ih =>
      rw [convexNFEval_cons]
      exact sup_le (hle g List.mem_cons_self) (ih (fun g' hg' => hle g' (List.mem_cons_of_mem _ hg')))

/-- **Generic assembly of the convex tangent decomposition.** If every generator `g ∈ gens` lies
below the curve (`β_g ≤ ↑f̲` everywhere) and at each point `t` *some* generator reaches it
(`β_g(t) = ↑f̲(t)`), then `convexNFEval gens = ↑f̲` pointwise. (The `≤` is `convexNFEval_le_of_forall_le`;
the `≥` is `le_convexNFEval_of_mem` at the reaching generator.) -/
theorem convexNFEval_eq_of_le_of_reaches (f0 fs : ℝ≥0) (segs gens : List (ℝ≥0 × ℝ≥0))
    (hle : ∀ g ∈ gens, ∀ t : ℝ≥0,
      rateLatencyEReal g.1 g.2 t ≤ (((convexSegEval f0 fs segs t : ℝ≥0) : ℝ) : EReal))
    (hreach : ∀ t : ℝ≥0, ∃ g ∈ gens,
      rateLatencyEReal g.1 g.2 t = (((convexSegEval f0 fs segs t : ℝ≥0) : ℝ) : EReal))
    (t : ℝ≥0) :
    convexNFEval gens t = (((convexSegEval f0 fs segs t : ℝ≥0) : ℝ) : EReal) := by
  refine le_antisymm
    (convexNFEval_le_of_forall_le f0 fs segs gens t (fun g hg => hle g hg t)) ?_
  obtain ⟨g, hg, hgt⟩ := hreach t
  rw [← hgt]
  exact le_convexNFEval_of_mem gens hg t

end DeepWiki
