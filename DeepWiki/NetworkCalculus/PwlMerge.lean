import DeepWiki.NetworkCalculus.PwlLowerEnvelope
import DeepWiki.NetworkCalculus.GeneralPwl

/-! # List-producing lower-envelope merge of `Pwl` curves

`lowerEnvEval` (in `PwlLowerEnvelope`) computes the pointwise *minimum* of two PWL curves
but returns only the merged **value**, so it cannot be folded to collapse `k` curves into a
single `Pwl`. This file lifts that recursion to a **segment-list-producing** merge:

* **`affineMinPwl a p b q : Pwl`** — the minimum of two affine curves as an explicit 1- or
  2-segment `Pwl`, reading off `affineMin`'s `convexSegEval` shape; eval equals
  `min (a + p·t) (b + q·t)`.
* **`segsTrunc segs L`** — cap a segment list's total length to `L`, used to emit the
  consumed leading piece at each merge step (eval below `L` unchanged; corner value at `L`).
* **`lowerEnvMerge p q : Pwl`** — mirrors `lowerEnvEval`'s well-founded recursion but EMITS
  segments: the leaf is `affineMinPwl`; each cons step prepends the consumed `affineMin`
  prefix `segsTrunc` then continues. Correctness `lowerEnvMerge_eval` reuses
  `lowerEnvEval_eq_min'`: `(lowerEnvMerge p q).eval t = min (p.eval t) (q.eval t)`.
* **`mergeAll p0 ps`** — the `foldl` of `lowerEnvMerge` collapsing finitely many `Pwl` into
  ONE, with `mergeAll_eval` the running pointwise min. -/

namespace DeepWiki

open scoped NNReal

/-! ## (1) Minimum of two affine curves as an explicit `Pwl` -/

/-- **The minimum of two affine curves as an explicit `Pwl`.** Reads off `affineMin`'s
`convexSegEval` shape (a 1- or 2-segment representation): in the dominated regimes the answer
is a single affine `⟨base, [], slope⟩`; in the crossing regimes it is one segment
`⟨base, [(slope, affineCross …)], asymptote⟩`. -/
noncomputable def affineMinPwl (a p b q : ℝ≥0) : Pwl :=
  if a ≤ b then
    if p ≤ q then ⟨a, [], p⟩
    else ⟨a, [(p, affineCross a p b q)], q⟩
  else
    if q ≤ p then ⟨b, [], q⟩
    else ⟨b, [(q, affineCross b q a p)], p⟩

/-- `(affineMinPwl a p b q).eval = affineMin a p b q`: the `Pwl` form evaluates to the affine
minimum (hence to `min (a + p·t) (b + q·t)`). -/
theorem affineMinPwl_eval (a p b q t : ℝ≥0) :
    (affineMinPwl a p b q).eval t = affineMin a p b q t := by
  unfold affineMinPwl affineMin
  split
  · split <;> rw [Pwl.eval_def]
  · split <;> rw [Pwl.eval_def]

/-- `(affineMinPwl a p b q).eval t = min (a + p·t) (b + q·t)`: the explicit-`Pwl` minimum of
two affine curves is their pointwise minimum. -/
theorem affineMinPwl_eval_min (a p b q t : ℝ≥0) :
    (affineMinPwl a p b q).eval t = min (a + p * t) (b + q * t) := by
  rw [affineMinPwl_eval, affineMin_eq_min]

/-- `(affineMinPwl a p b q).base = min a b`: the base of the affine-min `Pwl` is the smaller of
the two affine values at `0`. -/
theorem affineMinPwl_base (a p b q : ℝ≥0) : (affineMinPwl a p b q).base = min a b := by
  have h := affineMinPwl_eval_min a p b q 0
  rw [Pwl.eval_zero] at h
  simpa using h

/-! ## (2a) Truncating a curve to a leading length

To emit the consumed leading piece of one merge step we cap a curve `convexSegEval f0 fs segs`
to the breakpoint `L`, producing a segment list that (i) ends exactly at length `L` and (ii)
agrees with the original on `[0, L]`. The asymptote `fs` is folded in as the slope of the final
emitted segment, so the truncated piece carries the curve's slope all the way to `L` and the
caller can hand off to the next step from the exact corner value. -/

/-- **Cap a curve (with asymptote `fs`) to total length `L`.** Keeps leading segments whole while
their cumulative length stays `≤ L`, shortens the straddling segment to end at `L`, and — once the
finite segments are exhausted within `[0, L]` — emits the asymptote slope `fs` as the final
segment up to `L`. The result is a single segment list reaching exactly length `L`. -/
noncomputable def segsTrunc (fs : ℝ≥0) : List (ℝ≥0 × ℝ≥0) → ℝ≥0 → List (ℝ≥0 × ℝ≥0)
  | [], L => [(fs, L)]
  | (s, ℓ) :: rest, L =>
      if L ≤ ℓ then [(s, L)]
      else (s, ℓ) :: segsTrunc fs rest (L - ℓ)

/-- `segsTrunc fs [] L = [(fs, L)]`: a semi-infinite affine truncates to one segment of its
asymptote slope. -/
@[simp] theorem segsTrunc_nil (fs L : ℝ≥0) : segsTrunc fs [] L = [(fs, L)] := rfl

/-- Cons reading of `segsTrunc`: the straddling segment is shortened to `L`; otherwise the
leading segment is kept and the budget reduced by `ℓ`. -/
theorem segsTrunc_cons (fs s ℓ L : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) :
    segsTrunc fs ((s, ℓ) :: rest) L
      = if L ≤ ℓ then [(s, L)] else (s, ℓ) :: segsTrunc fs rest (L - ℓ) := rfl

/-- **`segsTrunc` agrees below `L`.** For `t ≤ L`, evaluating the truncated piece (with ANY
asymptote `fs'`) equals evaluating the original curve `convexSegEval f0 fs segs t`: both stay
on the shared leading pieces, which the truncation preserves. -/
theorem convexSegEval_segsTrunc_le (f0 fs fs' : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) (L t : ℝ≥0)
    (htL : t ≤ L) :
    convexSegEval f0 fs' (segsTrunc fs segs L) t = convexSegEval f0 fs segs t := by
  induction segs generalizing f0 L t with
  | nil =>
      rw [segsTrunc_nil, convexSegEval_cons, if_pos htL, convexSegEval_nil]
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      rw [segsTrunc_cons]
      by_cases hLℓ : L ≤ ℓ
      · rw [if_pos hLℓ, convexSegEval_cons, convexSegEval_cons,
          if_pos htL, if_pos (le_trans htL hLℓ)]
      · rw [if_neg hLℓ, convexSegEval_cons, convexSegEval_cons]
        by_cases htℓ : t ≤ ℓ
        · rw [if_pos htℓ, if_pos htℓ]
        · rw [if_neg htℓ, if_neg htℓ]
          exact ih (f0 + s * ℓ) (L - ℓ) (t - ℓ) (tsub_le_tsub_right htL ℓ)

/-- **`segsTrunc` agrees below `L`, even with a tail appended.** For `t ≤ L`, evaluating
`segsTrunc fs segs L ++ rest` equals the original curve `convexSegEval f0 fs segs t`: below `L`
the appended `rest` is never reached, so the truncated prefix governs. -/
theorem convexSegEval_segsTrunc_append_le (f0 fs fs' : ℝ≥0) (segs rest : List (ℝ≥0 × ℝ≥0))
    (L t : ℝ≥0) (htL : t ≤ L) :
    convexSegEval f0 fs' (segsTrunc fs segs L ++ rest) t = convexSegEval f0 fs segs t := by
  induction segs generalizing f0 L t with
  | nil =>
      rw [segsTrunc_nil, List.cons_append, List.nil_append, convexSegEval_cons, if_pos htL,
        convexSegEval_nil]
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      rw [segsTrunc_cons]
      by_cases hLℓ : L ≤ ℓ
      · rw [if_pos hLℓ, List.cons_append, List.nil_append, convexSegEval_cons, convexSegEval_cons,
          if_pos htL, if_pos (le_trans htL hLℓ)]
      · rw [if_neg hLℓ, List.cons_append, convexSegEval_cons, convexSegEval_cons]
        by_cases htℓ : t ≤ ℓ
        · rw [if_pos htℓ, if_pos htℓ]
        · rw [if_neg htℓ, if_neg htℓ]
          exact ih (f0 + s * ℓ) (L - ℓ) (t - ℓ) (tsub_le_tsub_right htL ℓ)

/-- **`segsTrunc` reaches the corner at `L`.** Evaluating the truncated piece at `t = L` gives the
original curve's value `convexSegEval f0 fs segs L` — the corner from which the next merge step
continues. -/
theorem convexSegEval_segsTrunc_at (f0 fs fs' : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) (L : ℝ≥0) :
    convexSegEval f0 fs' (segsTrunc fs segs L) L = convexSegEval f0 fs segs L :=
  convexSegEval_segsTrunc_le f0 fs fs' segs L L le_rfl

/-- **Peel a truncated leading piece.** For `L ≤ t`, evaluating `segsTrunc fs segs L ++ rest`
peels the whole truncated prefix and continues into `rest` from the corner
`convexSegEval f0 fs segs L`, evaluated at `t - L`. (At `t = L` both sides are the corner.) -/
theorem convexSegEval_segsTrunc_append_ge (f0 fs fs' : ℝ≥0) (segs rest : List (ℝ≥0 × ℝ≥0))
    (L t : ℝ≥0) (hLt : L ≤ t) :
    convexSegEval f0 fs' (segsTrunc fs segs L ++ rest) t
      = convexSegEval (convexSegEval f0 fs segs L) fs' rest (t - L) := by
  induction segs generalizing f0 L t with
  | nil =>
      rw [segsTrunc_nil, List.cons_append, List.nil_append, convexSegEval_cons, convexSegEval_nil]
      by_cases htL : t ≤ L
      · have heq : t = L := le_antisymm htL hLt
        subst heq
        rw [if_pos le_rfl, tsub_self, convexSegEval_zero]
      · rw [if_neg htL]
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      rw [segsTrunc_cons]
      by_cases hLℓ : L ≤ ℓ
      · rw [if_pos hLℓ, List.cons_append, List.nil_append, convexSegEval_cons,
          convexSegEval_cons, if_pos hLℓ]
        by_cases htL : t ≤ L
        · have heq : t = L := le_antisymm htL hLt
          subst heq
          rw [if_pos le_rfl, tsub_self, convexSegEval_zero]
        · rw [if_neg htL]
      · rw [if_neg hLℓ, List.cons_append, convexSegEval_cons, convexSegEval_cons]
        have hℓL : ℓ ≤ L := (not_le.mp hLℓ).le
        have hℓt : ℓ ≤ t := le_trans hℓL hLt
        rw [if_neg (not_le.mpr (lt_of_lt_of_le (lt_of_not_ge hLℓ) hLt)),
          if_neg (not_le.mpr (lt_of_not_ge hLℓ))]
        rw [ih (f0 + s * ℓ) (L - ℓ) (t - ℓ) (tsub_le_tsub_right hLt ℓ)]
        rw [tsub_tsub_tsub_cancel_right hℓL]

/-! ## (2b) The list-producing lower-envelope merge -/

/-- **One merge step as a `Pwl`.** Prepend the consumed `affineMin` leading piece on `[0, L]`
(the segments of `affineMinPwl f0 sf g0 sg` capped to `L` via `segsTrunc`) to a remaining curve
`rest`. Base and prefix slopes come from `affineMinPwl`; the asymptote is `rest`'s. -/
noncomputable def consAffineMin (f0 sf g0 sg L : ℝ≥0) (rest : Pwl) : Pwl :=
  ⟨(affineMinPwl f0 sf g0 sg).base,
    segsTrunc (affineMinPwl f0 sf g0 sg).tail (affineMinPwl f0 sf g0 sg).segs L ++ rest.segs,
    rest.tail⟩

/-- **Peel a merge step.** Provided `rest.base = affineMin f0 sf g0 sg L` (the corner where the
two halves meet), `consAffineMin` evaluates to the affine minimum below `L` and to `rest`
above it: `if t ≤ L then affineMin f0 sf g0 sg t else rest.eval (t - L)`. -/
theorem consAffineMin_eval (f0 sf g0 sg L : ℝ≥0) (rest : Pwl)
    (hcorner : rest.base = affineMin f0 sf g0 sg L) (t : ℝ≥0) :
    (consAffineMin f0 sf g0 sg L rest).eval t
      = if t ≤ L then affineMin f0 sf g0 sg t else rest.eval (t - L) := by
  simp only [consAffineMin, Pwl.eval_def]
  by_cases htL : t ≤ L
  · rw [if_pos htL, convexSegEval_segsTrunc_append_le _ _ _ _ _ _ _ htL]
    exact affineMinPwl_eval f0 sf g0 sg t
  · rw [if_neg htL]
    have hLt : L ≤ t := (not_le.mp htL).le
    rw [convexSegEval_segsTrunc_append_ge _ _ _ _ _ _ _ hLt]
    have hc : convexSegEval (affineMinPwl f0 sf g0 sg).base (affineMinPwl f0 sf g0 sg).tail
        (affineMinPwl f0 sf g0 sg).segs L = rest.base := by
      rw [← Pwl.eval_def, affineMinPwl_eval, hcorner]
    rw [hc]

/-- **The list-producing lower-envelope merge of two `Pwl`s.** Mirrors `lowerEnvEval`'s
well-founded recursion over the two segment lists, but EMITS segments: the nil/nil leaf is
`affineMinPwl` of the two asymptotic lines; each cons step prepends the consumed `affineMin`
prefix (via `consAffineMin`, splitting at the nearer breakpoint exactly as `lowerEnvEval` does)
then continues on the peeled tails. Correctness is `lowerEnvMerge_eval`. -/
noncomputable def lowerEnvMergeAux (f0 fs g0 gs : ℝ≥0) :
    List (ℝ≥0 × ℝ≥0) → List (ℝ≥0 × ℝ≥0) → Pwl
  | [], [] => affineMinPwl f0 fs g0 gs
  | (sf, Lf) :: fr, [] =>
      consAffineMin f0 sf g0 gs Lf
        (lowerEnvMergeAux (f0 + sf * Lf) fs (g0 + gs * Lf) gs fr [])
  | [], (sg, Lg) :: gr =>
      consAffineMin f0 fs g0 sg Lg
        (lowerEnvMergeAux (f0 + fs * Lg) fs (g0 + sg * Lg) gs [] gr)
  | (sf, Lf) :: fr, (sg, Lg) :: gr =>
      if Lf ≤ Lg then
        consAffineMin f0 sf g0 sg Lf
          (lowerEnvMergeAux (f0 + sf * Lf) fs (g0 + sg * Lf) gs fr ((sg, Lg - Lf) :: gr))
      else
        consAffineMin f0 sf g0 sg Lg
          (lowerEnvMergeAux (f0 + sf * Lg) fs (g0 + sg * Lg) gs ((sf, Lf - Lg) :: fr) gr)
  termination_by l1 l2 => l1.length + l2.length
  decreasing_by all_goals (simp_wf; try omega)

/-- The merge of two `Pwl` curves: applies `lowerEnvMergeAux` to their fields. -/
noncomputable def lowerEnvMerge (p q : Pwl) : Pwl :=
  lowerEnvMergeAux p.base p.tail q.base q.tail p.segs q.segs

/-- **The merge starts at the lower base.** `(lowerEnvMergeAux f0 fs g0 gs fsegs gsegs).base
= min f0 g0`: every branch (leaf and cons) opens with the `affineMin` base of the two leading
values, which is `min f0 g0`. Supplies the corner-matching hypothesis of `consAffineMin_eval`. -/
theorem lowerEnvMergeAux_base :
    ∀ (n : ℕ) (f0 fs g0 gs : ℝ≥0) (fsegs gsegs : List (ℝ≥0 × ℝ≥0)),
      fsegs.length + gsegs.length = n →
      (lowerEnvMergeAux f0 fs g0 gs fsegs gsegs).base = min f0 g0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f0 fs g0 gs fsegs gsegs hn
    match fsegs, gsegs with
    | [], [] => rw [lowerEnvMergeAux, affineMinPwl_base]
    | (sf, Lf) :: fr, [] => rw [lowerEnvMergeAux, consAffineMin, affineMinPwl_base]
    | [], (sg, Lg) :: gr => rw [lowerEnvMergeAux, consAffineMin, affineMinPwl_base]
    | (sf, Lf) :: fr, (sg, Lg) :: gr =>
        rw [lowerEnvMergeAux]
        split <;> rw [consAffineMin, affineMinPwl_base]

/-- **`lowerEnvMergeAux` matches `lowerEnvEval`.** Both follow the identical branch structure;
this proves the list-producing merge agrees pointwise with the value-only `lowerEnvEval`. -/
theorem lowerEnvMergeAux_eval :
    ∀ (n : ℕ) (f0 fs g0 gs : ℝ≥0) (fsegs gsegs : List (ℝ≥0 × ℝ≥0)),
      fsegs.length + gsegs.length = n → ∀ t : ℝ≥0,
      (lowerEnvMergeAux f0 fs g0 gs fsegs gsegs).eval t
        = lowerEnvEval f0 fs g0 gs fsegs gsegs t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f0 fs g0 gs fsegs gsegs hn t
    match fsegs, gsegs with
    | [], [] =>
        rw [lowerEnvMergeAux, lowerEnvEval, affineMinPwl_eval]
    | (sf, Lf) :: fr, [] =>
        rw [lowerEnvMergeAux, lowerEnvEval,
          consAffineMin_eval _ _ _ _ _ _
            (by rw [lowerEnvMergeAux_base _ _ _ _ _ _ _ rfl, affineMin_eq_min])]
        by_cases ht : t ≤ Lf
        · rw [if_pos ht, if_pos ht]
        · rw [if_neg ht, if_neg ht,
            ih (fr.length + ([] : List (ℝ≥0 × ℝ≥0)).length) (by simp at hn ⊢; omega)
              _ _ _ _ _ _ rfl]
    | [], (sg, Lg) :: gr =>
        rw [lowerEnvMergeAux, lowerEnvEval,
          consAffineMin_eval _ _ _ _ _ _
            (by rw [lowerEnvMergeAux_base _ _ _ _ _ _ _ rfl, affineMin_eq_min])]
        by_cases ht : t ≤ Lg
        · rw [if_pos ht, if_pos ht]
        · rw [if_neg ht, if_neg ht,
            ih (([] : List (ℝ≥0 × ℝ≥0)).length + gr.length) (by simp at hn ⊢; omega)
              _ _ _ _ _ _ rfl]
    | (sf, Lf) :: fr, (sg, Lg) :: gr =>
        rw [lowerEnvMergeAux, lowerEnvEval]
        by_cases hfg : Lf ≤ Lg
        · rw [if_pos hfg, if_pos hfg,
            consAffineMin_eval _ _ _ _ _ _
              (by rw [lowerEnvMergeAux_base _ _ _ _ _ _ _ rfl, affineMin_eq_min])]
          rw [show min Lf Lg = Lf from min_eq_left hfg]
          by_cases ht : t ≤ Lf
          · rw [if_pos ht, if_pos ht]
          · rw [if_neg ht, if_neg ht,
              ih (fr.length + ((sg, Lg - Lf) :: gr).length) (by simp at hn ⊢; omega)
                _ _ _ _ _ _ rfl]
        · rw [if_neg hfg, if_neg hfg,
            consAffineMin_eval _ _ _ _ _ _
              (by rw [lowerEnvMergeAux_base _ _ _ _ _ _ _ rfl, affineMin_eq_min])]
          rw [show min Lf Lg = Lg from min_eq_right (not_le.mp hfg).le]
          by_cases ht : t ≤ Lg
          · rw [if_pos ht, if_pos ht]
          · rw [if_neg ht, if_neg ht,
              ih (((sf, Lf - Lg) :: fr).length + gr.length) (by simp at hn ⊢; omega)
                _ _ _ _ _ _ rfl]

/-- **Correctness of the list-producing merge.** `(lowerEnvMerge p q).eval t = min (p.eval t)
(q.eval t)`: the explicit segment-list merge of two `Pwl`s is their pointwise minimum. This is
the key deliverable — "the min of two PWLs IS one explicit `Pwl` segment list". -/
theorem lowerEnvMerge_eval (p q : Pwl) (t : ℝ≥0) :
    (lowerEnvMerge p q).eval t = min (p.eval t) (q.eval t) := by
  rw [lowerEnvMerge, lowerEnvMergeAux_eval _ _ _ _ _ _ _ rfl, lowerEnvEval_eq_min',
    Pwl.eval_def, Pwl.eval_def]

/-! ## (3) The k-ary fold -/

/-- **Collapse finitely many `Pwl`s into one** by folding `lowerEnvMerge` from a starting curve
`p0` across the list `ps`. The result is a single `Pwl` whose value is the running pointwise
minimum of `p0` and all of `ps`. -/
noncomputable def mergeAll (p0 : Pwl) (ps : List Pwl) : Pwl :=
  ps.foldl lowerEnvMerge p0

/-- **Correctness of the `k`-ary fold.** `(mergeAll p0 ps).eval t` is the running pointwise
minimum: `ps.foldl (fun acc q => min acc (q.eval t)) (p0.eval t)`. So one `Pwl` represents the
lower envelope of `p0` together with every curve in `ps`. -/
theorem mergeAll_eval (p0 : Pwl) (ps : List Pwl) (t : ℝ≥0) :
    (mergeAll p0 ps).eval t
      = ps.foldl (fun acc q => min acc (q.eval t)) (p0.eval t) := by
  unfold mergeAll
  induction ps generalizing p0 with
  | nil => rfl
  | cons q qs ih =>
      rw [List.foldl_cons, List.foldl_cons, ih (lowerEnvMerge p0 q), lowerEnvMerge_eval]

/-! ## Restatements against the intended wording -/

/-- (1) The affine-min `Pwl` evaluates to the pointwise minimum of two affine curves. -/
example (a p b q t : ℝ≥0) : (affineMinPwl a p b q).eval t = min (a + p * t) (b + q * t) :=
  affineMinPwl_eval_min a p b q t

/-- (2) The list-producing merge of two `Pwl`s is their pointwise minimum. -/
example (p q : Pwl) (t : ℝ≥0) :
    (lowerEnvMerge p q).eval t = min (p.eval t) (q.eval t) :=
  lowerEnvMerge_eval p q t

/-- (3) The fold collapses many `Pwl`s into one whose value is the running pointwise min. -/
example (p0 : Pwl) (ps : List Pwl) (t : ℝ≥0) :
    (mergeAll p0 ps).eval t = ps.foldl (fun acc q => min acc (q.eval t)) (p0.eval t) :=
  mergeAll_eval p0 ps t

end DeepWiki
