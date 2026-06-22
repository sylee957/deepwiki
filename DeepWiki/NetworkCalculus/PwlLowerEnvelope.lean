import DeepWiki.NetworkCalculus.ConvexSegmentMerge
import DeepWiki.NetworkCalculus.ConvexConvByLine

/-! # Pointwise minimum (lower envelope) of piecewise-linear curves over `ℝ≥0`

The pointwise *minimum* (lower envelope) of two PWL curves is itself PWL. This is the
algorithmic core of network-calculus min-plus arithmetic that is **not** a convolution:
`min(f, g)` rather than `f ∗ g`. Unlike convex convolution (slope merge), the lower
envelope of two PWLs can cross many times, so the merged representation may interleave
pieces of both inputs.

This file builds the construction bottom-up against the general evaluator
`convexSegEval f0 fs segs t` (base value, asymptotic slope, `(slope, length)` list — any
`ℝ≥0` slopes, no sorting assumed):

* **(a) `affineMin`** — the minimum of two affine curves `a + p·t` and `b + q·t`, a 1- or
  2-piece PWL, with the exact closed form `affineMin a p b q t = min (a + p·t) (b + q·t)`.
  The crossing offset is computed with `ℝ≥0` truncated subtraction / division; the
  correctness proof keeps comparisons as products to dodge division algebra.
* **(b) `affineMinSeg`** — the minimum of a general `convexSegEval f0 fs segs` and an affine
  `b + q·t`, in the total-domination regimes (the affine lies entirely below, or entirely
  above, the PWL on `[0,∞)`), where the answer is one of the two inputs verbatim.

The fully general multi-crossing lower envelope (c) is left to a later layer; the affine
base case (a) is the reusable building block. -/

namespace DeepWiki

open scoped NNReal

/-! ## (a) Minimum of two affine curves

For affine `f t = a + p·t` and `g t = b + q·t` over `ℝ≥0`, `min (f t) (g t)` is piecewise
linear with at most one breakpoint (the crossing). Four regimes by `a ≤ b` / `b ≤ a` and
`p ≤ q` / `q ≤ p`:

* the lower-base line is also flatter ⇒ it dominates (1 piece, no crossing);
* the lower-base line is steeper ⇒ they cross once at `t* = (b−a)/(p−q)` (2 pieces): below
  `t*` the lower-base line wins, above `t*` the flatter line wins.

`affineMin` packs this as a single `convexSegEval`. -/

/-- A crossing offset for two affine curves: the `t` at which `a + p·t = b + q·t`, oriented so
`a ≤ b` and `q ≤ p` (lower-base meets higher-base-but-flatter). With `ℝ≥0` truncated subtraction
this is `(b − a) / (p − q)`; it is `0` when `p = q`. -/
noncomputable def affineCross (a p b q : ℝ≥0) : ℝ≥0 := (b - a) / (p - q)

/-- The minimum of two affine curves `a + p·t` and `b + q·t`, as a single `convexSegEval`.

The construction orients the two lines so the one with the lower base value `f(0)` leads. If the
leading line is also the flatter (smaller-slope) one it dominates everywhere (one semi-infinite
piece). Otherwise the lines cross once: the leading (steeper) line is used up to the crossing
offset `affineCross`, then the trailing (flatter) line continues, so the asymptotic slope is the
*smaller* of the two slopes. -/
noncomputable def affineMin (a p b q : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  if a ≤ b then
    if p ≤ q then convexSegEval a p []                  -- leader flatter ⇒ dominates
    else convexSegEval a q [(p, affineCross a p b q)]   -- cross once, asymptote `q`
  else
    if q ≤ p then convexSegEval b q []
    else convexSegEval b p [(q, affineCross b q a p)]

/-- **Key affine-comparison lemma.** Over `ℝ≥0`, with `a ≤ b` and `q < p`, the affine curve
`a + p·t` is `≤ b + q·t` exactly on `t ≤ (b − a)/(p − q)`. Kept as a product comparison so the
truncated subtraction is never "un-divided". -/
theorem affine_le_affine_iff_le_cross {a p b q : ℝ≥0} (hab : a ≤ b) (hqp : q < p) (t : ℝ≥0) :
    a + p * t ≤ b + q * t ↔ t ≤ affineCross a p b q := by
  unfold affineCross
  rw [le_div_iff₀ (tsub_pos_of_lt hqp)]
  -- goal: `a + p·t ≤ b + q·t ↔ t·(p - q) ≤ b - a`; push to `ℝ` to compare linearly
  rw [← NNReal.coe_le_coe, ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub hab, NNReal.coe_sub hqp.le]
  constructor <;> intro h <;> nlinarith [h]

/-- **The two affines agree at the crossing.** With `a ≤ b` and `q < p`, at `t* = affineCross`
the lines `a + p·t` and `b + q·t` take the same value. -/
theorem affine_eq_at_cross {a p b q : ℝ≥0} (hab : a ≤ b) (hqp : q < p) :
    a + p * affineCross a p b q = b + q * affineCross a p b q := by
  unfold affineCross
  rw [← NNReal.coe_inj]
  have hsub : ((p - q : ℝ≥0) : ℝ) = (p : ℝ) - q := NNReal.coe_sub hqp.le
  have hpq : (0 : ℝ) < (p : ℝ) - q := sub_pos.mpr (NNReal.coe_lt_coe.mpr hqp)
  push_cast [NNReal.coe_sub hab]
  rw [hsub]
  field_simp
  ring

/-- The two-piece crossing form: with `a ≤ b` and `q < p`, the single-segment evaluator
`convexSegEval a q [(p, t*)]` (steeper line `p` up to the crossing `t*`, then flatter asymptote
`q`) is exactly the pointwise minimum of the two affines. -/
theorem convexSegEval_cross_eq_min {a p b q : ℝ≥0} (hab : a ≤ b) (hqp : q < p) (t : ℝ≥0) :
    convexSegEval a q [(p, affineCross a p b q)] t = min (a + p * t) (b + q * t) := by
  rw [convexSegEval_cons]
  split
  · rename_i ht
    rw [min_eq_left ((affine_le_affine_iff_le_cross hab hqp t).mpr ht)]
  · rename_i ht
    rw [convexSegEval_nil]
    have ht' : affineCross a p b q ≤ t := (not_le.mp ht).le
    -- the trailing piece, expanded at the corner value
    have hcorner : a + p * affineCross a p b q = b + q * affineCross a p b q :=
      affine_eq_at_cross hab hqp
    have hval : a + p * affineCross a p b q + q * (t - affineCross a p b q) = b + q * t := by
      rw [hcorner, add_assoc, ← mul_add, add_tsub_cancel_of_le ht']
    rw [hval, min_eq_right]
    exact le_of_not_ge (fun h => ht ((affine_le_affine_iff_le_cross hab hqp t).mp h))

/-- **(a) Minimum of two affine curves, closed form.** `affineMin a p b q t = min (a + p·t)
(b + q·t)` for all `t`: the pointwise minimum of two affine curves over `ℝ≥0` is the single
`convexSegEval` produced by `affineMin`. -/
theorem affineMin_eq_min (a p b q : ℝ≥0) (t : ℝ≥0) :
    affineMin a p b q t = min (a + p * t) (b + q * t) := by
  unfold affineMin
  split
  · rename_i hab
    split
    · rename_i hpq
      rw [convexSegEval_nil, min_eq_left]; gcongr
    · rename_i hpq
      exact convexSegEval_cross_eq_min hab (not_le.mp hpq) t
  · rename_i hab
    have hba : b ≤ a := (not_le.mp hab).le
    split
    · rename_i hqp
      rw [convexSegEval_nil, min_eq_right]; gcongr
    · rename_i hqp
      rw [convexSegEval_cross_eq_min hba (not_le.mp hqp) t, min_comm]

/-! ## (b) Minimum of a general convex PWL and an affine line: total-domination regimes

The full multi-crossing min of `convexSegEval f0 fs segs` against `b + q·t` is deferred to
later; here are the regimes where one input dominates the other on all of `[0,∞)`, so the
minimum *is* that input verbatim. The reusable trigger is `convexSegEval_le_affine_of_slopes`:
a PWL whose base and every slope are bounded by the line stays below it everywhere. -/

/-- **Total-domination upper bound (sufficient condition).** If the base `f0 ≤ b` and every
slope of the PWL (each segment slope and the asymptote `fs`) is `≤ q`, then the PWL lies below
the affine line `b + q·t` for all `t` — the PWL never starts above the line nor grows faster. -/
theorem convexSegEval_le_affine_of_slopes {f0 fs b q : ℝ≥0} {segs : List (ℝ≥0 × ℝ≥0)}
    (hbase : f0 ≤ b) (hfs : fs ≤ q) (hsegs : ∀ seg ∈ segs, seg.1 ≤ q) (t : ℝ≥0) :
    convexSegEval f0 fs segs t ≤ b + q * t := by
  have h := convexSegEval_upper_rate fs q segs hsegs hfs f0 0 t
  rw [zero_add, convexSegEval_zero] at h
  calc convexSegEval f0 fs segs t ≤ f0 + q * t := h
    _ ≤ b + q * t := by gcongr

/-- **The line dominates from above ⇒ min is the PWL.** If `b + q·t` is everywhere `≥` the PWL,
the lower envelope is the PWL itself. -/
theorem min_eq_convexSegEval_of_le {f0 fs b q : ℝ≥0} {segs : List (ℝ≥0 × ℝ≥0)}
    (h : ∀ t, convexSegEval f0 fs segs t ≤ b + q * t) (t : ℝ≥0) :
    min (convexSegEval f0 fs segs t) (b + q * t) = convexSegEval f0 fs segs t :=
  min_eq_left (h t)

/-- **The PWL dominates from above ⇒ min is the line.** If the PWL is everywhere `≥ b + q·t`,
the lower envelope is the affine line itself. -/
theorem min_eq_affine_of_le {f0 fs b q : ℝ≥0} {segs : List (ℝ≥0 × ℝ≥0)}
    (h : ∀ t, b + q * t ≤ convexSegEval f0 fs segs t) (t : ℝ≥0) :
    min (convexSegEval f0 fs segs t) (b + q * t) = b + q * t :=
  min_eq_right (h t)

/-- **Total-domination corollary.** Under the slope/base bound, the lower envelope of a PWL and
the affine line `b + q·t` is exactly the PWL. -/
theorem min_eq_convexSegEval_of_slopes {f0 fs b q : ℝ≥0} {segs : List (ℝ≥0 × ℝ≥0)}
    (hbase : f0 ≤ b) (hfs : fs ≤ q) (hsegs : ∀ seg ∈ segs, seg.1 ≤ q) (t : ℝ≥0) :
    min (convexSegEval f0 fs segs t) (b + q * t) = convexSegEval f0 fs segs t :=
  min_eq_convexSegEval_of_le (convexSegEval_le_affine_of_slopes hbase hfs hsegs) t

/-! ## (c) Lower envelope of two general convex PWLs: the recursion building blocks

The full multi-crossing lower-envelope merge interleaves pieces of both curves at every
crossing; its correctness is an induction over a *shared* segment grid. Here are the two
invariants that recursion rests on, each fully proved:

* `lowerEnv_peel_shared` — when both curves share a leading breakpoint at length `L`, the
  lower envelope splits cleanly: it is `affineMin` of the two leading pieces on `[0, L]`, and
  the lower envelope of the two *peeled tails* on `[L, ∞)`.
* `min_convexSegEval_dominated` — the no-crossing case: if one PWL lies below the other on all
  of `[0, ∞)`, the lower envelope is that lower PWL verbatim.

A full `(c)` would first refine the two segment lists onto a common grid (so every step meets
the shared-breakpoint hypothesis of `lowerEnv_peel_shared`), then induct. That grid-refinement
layer is left for later; the pieces below are its load-bearing core. -/

/-- **No-crossing lower envelope.** If `convexSegEval f0 fs fsegs ≤ convexSegEval g0 gs gsegs`
pointwise, their lower envelope is the first (lower) curve. -/
theorem min_convexSegEval_dominated {f0 fs g0 gs : ℝ≥0} {fsegs gsegs : List (ℝ≥0 × ℝ≥0)}
    (h : ∀ t, convexSegEval f0 fs fsegs t ≤ convexSegEval g0 gs gsegs t) (t : ℝ≥0) :
    min (convexSegEval f0 fs fsegs t) (convexSegEval g0 gs gsegs t)
      = convexSegEval f0 fs fsegs t :=
  min_eq_left (h t)

/-- A zero-length leading segment is inert: `convexSegEval f0 fs ((s, 0) :: rest) = convexSegEval
f0 fs rest`. -/
theorem convexSegEval_zero_head (f0 fs s : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    convexSegEval f0 fs ((s, 0) :: rest) t = convexSegEval f0 fs rest t := by
  rw [convexSegEval_cons]
  by_cases ht : t ≤ 0
  · rw [if_pos ht, le_antisymm ht zero_le, mul_zero, add_zero, convexSegEval_zero]
  · rw [if_neg ht, mul_zero, add_zero, tsub_zero]

/-- **Splitting a leading segment at an interior length preserves the curve.** For `L ≤ ℓ`,
inserting a breakpoint at `L` inside the leading segment `(s, ℓ)` — i.e. replacing it by
`(s, L) :: (s, ℓ − L)` — leaves the evaluation unchanged (it is still slope `s` on `[0, ℓ]`). -/
theorem convexSegEval_splitLeadSeg (f0 fs s ℓ L : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0))
    (hLℓ : L ≤ ℓ) (t : ℝ≥0) :
    convexSegEval f0 fs ((s, L) :: (s, ℓ - L) :: rest) t
      = convexSegEval f0 fs ((s, ℓ) :: rest) t := by
  rw [convexSegEval_cons (s := s) (ℓ := L), convexSegEval_cons (s := s) (ℓ := ℓ)]
  by_cases htL : t ≤ L
  · rw [if_pos htL, if_pos (le_trans htL hLℓ)]
  · rw [if_neg htL, convexSegEval_cons (s := s) (ℓ := ℓ - L)]
    have hLt : L ≤ t := (not_le.mp htL).le
    by_cases htℓ : t ≤ ℓ
    · -- still on the leading slope: both sides equal `f0 + s·t`
      rw [if_pos htℓ, if_pos (tsub_le_tsub_right htℓ L)]
      rw [add_assoc, ← mul_add, add_tsub_cancel_of_le hLt]
    · -- past the leading slope: both peel into `rest` from corner `f0 + s·ℓ`
      have hℓt : ℓ ≤ t := (not_le.mp htℓ).le
      have htLℓ : ¬ t - L ≤ ℓ - L := by
        rw [not_le] at htℓ ⊢; exact tsub_lt_tsub_right_of_le hLℓ htℓ
      rw [if_neg htℓ, if_neg htLℓ]
      congr 1
      · rw [add_assoc, ← mul_add, add_tsub_cancel_of_le hLℓ]
      · rw [tsub_tsub_tsub_cancel_right hLℓ]

/-- **Shared-breakpoint peel step (the lower-envelope recursion invariant).** When both PWLs
have a leading segment of the *same* length `L`, their lower envelope is `affineMin` of the two
leading affine pieces below `L`, and the lower envelope of the peeled tails above `L`. This is
the step a full grid-aligned lower-envelope merge induces on. -/
theorem lowerEnv_peel_shared (f0 fs sf g0 gs sg L : ℝ≥0)
    (fr gr : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    min (convexSegEval f0 fs ((sf, L) :: fr) t) (convexSegEval g0 gs ((sg, L) :: gr) t)
      = if t ≤ L then affineMin f0 sf g0 sg t
        else min (convexSegEval (f0 + sf * L) fs fr (t - L))
                 (convexSegEval (g0 + sg * L) gs gr (t - L)) := by
  rw [convexSegEval_cons, convexSegEval_cons]
  split
  · exact (affineMin_eq_min f0 sf g0 sg t).symm
  · rfl

/-- **General peel step (different leading breakpoints).** With leading segments of lengths
`Lf`, `Lg`, peel up to the nearer breakpoint `L = min Lf Lg`: below `L` the envelope is
`affineMin` of the leading pieces, above `L` it is the lower envelope of the tails with the
longer leading segment split at `L` (`(s, ℓ − L)` kept; the equal-length one gets a harmless
zero-length head). Reduces to `lowerEnv_peel_shared` after splitting both leads to length `L`. -/
theorem lowerEnv_peel (f0 fs sf Lf g0 gs sg Lg : ℝ≥0) (fr gr : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    min (convexSegEval f0 fs ((sf, Lf) :: fr) t) (convexSegEval g0 gs ((sg, Lg) :: gr) t)
      = if t ≤ min Lf Lg then affineMin f0 sf g0 sg t
        else min (convexSegEval (f0 + sf * min Lf Lg) fs ((sf, Lf - min Lf Lg) :: fr)
                    (t - min Lf Lg))
                 (convexSegEval (g0 + sg * min Lf Lg) gs ((sg, Lg - min Lf Lg) :: gr)
                    (t - min Lf Lg)) := by
  rw [← convexSegEval_splitLeadSeg f0 fs sf Lf (min Lf Lg) fr (min_le_left _ _) t,
      ← convexSegEval_splitLeadSeg g0 gs sg Lg (min Lf Lg) gr (min_le_right _ _) t,
      lowerEnv_peel_shared f0 fs sf g0 gs sg (min Lf Lg)]

/-- **(c) The lower envelope of two general convex PWLs.** Recurses over the two segment lists,
consuming the nearer breakpoint at each step: below it the value is `affineMin` of the two
current leading affine pieces; above it, the recursion continues on the peeled tails (the curve
whose lead was fully consumed loses a segment; the other keeps a shortened lead). The nil/nil
base is `affineMin` of the two asymptotic lines. Correctness is `lowerEnvEval_eq_min`. -/
noncomputable def lowerEnvEval (f0 fs g0 gs : ℝ≥0) :
    List (ℝ≥0 × ℝ≥0) → List (ℝ≥0 × ℝ≥0) → ℝ≥0 → ℝ≥0
  | [], [], t => affineMin f0 fs g0 gs t
  | (sf, Lf) :: fr, [], t =>
      if t ≤ Lf then affineMin f0 sf g0 gs t
      else lowerEnvEval (f0 + sf * Lf) fs (g0 + gs * Lf) gs fr [] (t - Lf)
  | [], (sg, Lg) :: gr, t =>
      if t ≤ Lg then affineMin f0 fs g0 sg t
      else lowerEnvEval (f0 + fs * Lg) fs (g0 + sg * Lg) gs [] gr (t - Lg)
  | (sf, Lf) :: fr, (sg, Lg) :: gr, t =>
      if t ≤ min Lf Lg then affineMin f0 sf g0 sg t
      else if Lf ≤ Lg then
        lowerEnvEval (f0 + sf * Lf) fs (g0 + sg * Lf) gs fr ((sg, Lg - Lf) :: gr) (t - Lf)
      else
        lowerEnvEval (f0 + sf * Lg) fs (g0 + sg * Lg) gs ((sf, Lf - Lg) :: fr) gr (t - Lg)
  termination_by l1 l2 => l1.length + l2.length
  decreasing_by all_goals (simp_wf; try omega)

/-- **(c) Correctness of the lower-envelope merge.** `lowerEnvEval` computes the pointwise
minimum of the two PWLs: `lowerEnvEval f0 fs g0 gs fsegs gsegs t
= min (convexSegEval f0 fs fsegs t) (convexSegEval g0 gs gsegs t)`. -/
theorem lowerEnvEval_eq_min :
    ∀ (n : ℕ) (f0 fs g0 gs : ℝ≥0) (fsegs gsegs : List (ℝ≥0 × ℝ≥0)),
      fsegs.length + gsegs.length = n → ∀ t : ℝ≥0,
      lowerEnvEval f0 fs g0 gs fsegs gsegs t
        = min (convexSegEval f0 fs fsegs t) (convexSegEval g0 gs gsegs t) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f0 fs g0 gs fsegs gsegs hn t
    match fsegs, gsegs with
    | [], [] =>
        rw [lowerEnvEval, convexSegEval_nil, convexSegEval_nil, affineMin_eq_min]
    | (sf, Lf) :: fr, [] =>
        rw [lowerEnvEval]
        by_cases ht : t ≤ Lf
        · rw [if_pos ht, convexSegEval_cons, if_pos ht, convexSegEval_nil, affineMin_eq_min]
        · rw [if_neg ht, ih (fr.length + ([] : List (ℝ≥0 × ℝ≥0)).length) (by simp at hn ⊢; omega)
            _ _ _ _ _ _ rfl, convexSegEval_cons, if_neg ht, convexSegEval_nil, convexSegEval_nil]
          have hLt : Lf ≤ t := (not_le.mp ht).le
          congr 1
          rw [add_assoc, ← mul_add, add_tsub_cancel_of_le hLt]
    | [], (sg, Lg) :: gr =>
        rw [lowerEnvEval]
        by_cases ht : t ≤ Lg
        · rw [if_pos ht, convexSegEval_cons, if_pos ht, convexSegEval_nil, affineMin_eq_min]
        · rw [if_neg ht, ih (([] : List (ℝ≥0 × ℝ≥0)).length + gr.length) (by simp at hn ⊢; omega)
            _ _ _ _ _ _ rfl, convexSegEval_cons, if_neg ht, convexSegEval_nil, convexSegEval_nil]
          have hLt : Lg ≤ t := (not_le.mp ht).le
          congr 1
          rw [add_assoc, ← mul_add, add_tsub_cancel_of_le hLt]
    | (sf, Lf) :: fr, (sg, Lg) :: gr =>
        rw [lowerEnvEval]
        by_cases ht : t ≤ min Lf Lg
        · rw [if_pos ht, affineMin_eq_min, convexSegEval_cons, convexSegEval_cons,
            if_pos (le_trans ht (min_le_left _ _)), if_pos (le_trans ht (min_le_right _ _))]
        · rw [if_neg ht]
          have hpeel := lowerEnv_peel f0 fs sf Lf g0 gs sg Lg fr gr t
          by_cases hfg : Lf ≤ Lg
          · rw [if_pos hfg, ih (fr.length + ((sg, Lg - Lf) :: gr).length)
              (by simp at hn ⊢; omega) _ _ _ _ _ _ rfl]
            rw [show min Lf Lg = Lf from min_eq_left hfg] at hpeel ht
            rw [hpeel, if_neg ht, tsub_self, convexSegEval_zero_head]
          · rw [if_neg hfg, ih (((sf, Lf - Lg) :: fr).length + gr.length)
              (by simp at hn ⊢; omega) _ _ _ _ _ _ rfl]
            have hgf : Lg ≤ Lf := (not_le.mp hfg).le
            rw [show min Lf Lg = Lg from min_eq_right hgf] at hpeel ht
            rw [hpeel, if_neg ht, tsub_self, convexSegEval_zero_head]

/-- **(c) Lower-envelope correctness, user form.** Drops the recursion-measure index from
`lowerEnvEval_eq_min`: `lowerEnvEval` is the pointwise minimum of the two PWLs. -/
theorem lowerEnvEval_eq_min' (f0 fs g0 gs : ℝ≥0) (fsegs gsegs : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    lowerEnvEval f0 fs g0 gs fsegs gsegs t
      = min (convexSegEval f0 fs fsegs t) (convexSegEval g0 gs gsegs t) :=
  lowerEnvEval_eq_min _ f0 fs g0 gs fsegs gsegs rfl t

/-! ## Restatements against the intended wording -/

/-- (a) `affineMin` computes the pointwise minimum of two affine curves. -/
example (a p b q t : ℝ≥0) : affineMin a p b q t = min (a + p * t) (b + q * t) :=
  affineMin_eq_min a p b q t

/-- (a) The two affines cross at `affineCross` (equal values there, oriented `a ≤ b`, `q < p`). -/
example {a p b q : ℝ≥0} (hab : a ≤ b) (hqp : q < p) :
    a + p * affineCross a p b q = b + q * affineCross a p b q :=
  affine_eq_at_cross hab hqp

/-- (b) A slope-and-base-dominated PWL lies under the affine line everywhere. -/
example {f0 fs b q : ℝ≥0} {segs : List (ℝ≥0 × ℝ≥0)}
    (hbase : f0 ≤ b) (hfs : fs ≤ q) (hsegs : ∀ seg ∈ segs, seg.1 ≤ q) (t : ℝ≥0) :
    convexSegEval f0 fs segs t ≤ b + q * t :=
  convexSegEval_le_affine_of_slopes hbase hfs hsegs t

/-- (c) The lower-envelope merge of two general convex PWLs computes their pointwise minimum. -/
example (f0 fs g0 gs : ℝ≥0) (fsegs gsegs : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    lowerEnvEval f0 fs g0 gs fsegs gsegs t
      = min (convexSegEval f0 fs fsegs t) (convexSegEval g0 gs gsegs t) :=
  lowerEnvEval_eq_min' f0 fs g0 gs fsegs gsegs t

end DeepWiki
