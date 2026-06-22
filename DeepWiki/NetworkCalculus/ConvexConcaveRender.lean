import DeepWiki.NetworkCalculus.ConvexConcaveCollapse

/-! # Rendering the convex-by-concave convolution as explicit PWL pieces (Theorem 4.2 output)
The collapse `minConv_concaveNFEval_eq_lineMeet_inf` writes `f ∗ concave = lineMeet f l ⊓ f` as a
bucket-line lower envelope capped by `f`. Each line-convolution `f ∗ lineⱼ` is, by
`minConv_line_convexSegEval`, the *explicit* convex PWL `convexSegEval (bⱼ + f0) rⱼ (truncSegs rⱼ
fsegs)` (`f`'s segments truncated at the bucket rate `rⱼ`, lifted by the burst `bⱼ`). So for a convex
`f = convexSegEval f0 fs fsegs` whose bucket rates are all `≤ fs`, the whole convex-by-concave
convolution renders as a **finite meet of concrete `convexSegEval` curves** — Theorem 4.2's output. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- One line-convolution rendered as an explicit convex PWL: for `r ≤ fs`,
`f ∗ lineᵣᵦ = convexSegEval (b + f0) r (truncSegs r fsegs)` (the curve `f` with its segments steeper
than `r` truncated to the asymptote `r`, lifted by `b`). Bridges the token-bucket line
`rateEReal r + b` to `convexSegEval b r []` then applies `minConv_line_convexSegEval`. -/
theorem minConv_line_render (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal))
            (rateEReal r + Function.const ℝ≥0 ((b : ℝ) : EReal))
      = fun t => (((convexSegEval (b + f0) r (truncSegs r fsegs) t : ℝ≥0) : ℝ) : EReal) := by
  funext t
  rw [rateEReal_add_const_eq_convexSegEval, minConv_comm]
  exact minConv_line_convexSegEval f0 fs b r fsegs hfsort hfs hrf t

/-- The rendered bucket-line envelope: the foldr-meet of the explicit per-bucket convex curves
`convexSegEval (bⱼ + f0) rⱼ (truncSegs rⱼ fsegs)` (each bucket `(rⱼ, bⱼ)` of `l`). -/
noncomputable def renderedLineMeet (f0 : ℝ≥0) (fsegs l : List (ℝ≥0 × ℝ≥0)) : ℝ≥0 → EReal :=
  l.foldr (fun rb acc =>
      (fun t => (((convexSegEval (rb.2 + f0) rb.1 (truncSegs rb.1 fsegs) t : ℝ≥0) : ℝ) : EReal))
        ⊓ acc)
    topCurve

/-- `renderedLineMeet` on the empty list is `topCurve` (the meet identity). -/
@[simp] theorem renderedLineMeet_nil (f0 : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0)) :
    renderedLineMeet f0 fsegs [] = topCurve := rfl

/-- `renderedLineMeet` peels one bucket: its rendered convex curve met with the rest. -/
@[simp] theorem renderedLineMeet_cons (f0 : ℝ≥0) (rb : ℝ≥0 × ℝ≥0)
    (fsegs l : List (ℝ≥0 × ℝ≥0)) :
    renderedLineMeet f0 fsegs (rb :: l)
      = (fun t => (((convexSegEval (rb.2 + f0) rb.1 (truncSegs rb.1 fsegs) t : ℝ≥0) : ℝ) : EReal))
          ⊓ renderedLineMeet f0 fsegs l := rfl

/-- `lineMeet` over a convex `f` renders termwise to the explicit per-bucket convex PWL curves,
provided every bucket rate is `≤ fs`: `lineMeet f l = renderedLineMeet f0 fsegs l`. -/
theorem lineMeet_eq_renderedLineMeet (f0 fs : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) :
    ∀ (l : List (ℝ≥0 × ℝ≥0)), (∀ rb ∈ l, rb.1 ≤ fs) →
      lineMeet (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) l
        = renderedLineMeet f0 fsegs l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons rb l ih =>
      intro hl
      have hrb : rb.1 ≤ fs := hl rb List.mem_cons_self
      have hl' : ∀ x ∈ l, x.1 ≤ fs := fun x hx => hl x (List.mem_cons_of_mem _ hx)
      rw [lineMeet_cons, minConv_line_render f0 fs rb.1 rb.2 fsegs hfsort hfs hrb, ih hl',
        renderedLineMeet_cons]

/-- **Theorem 4.2, rendered output.** For a convex PWL `f = convexSegEval f0 fs fsegs` and a
non-empty token-bucket list `l` whose every rate is `≤ fs`, the convex-by-concave convolution is an
explicit **finite meet of concrete convex PWL curves**:
`f ∗ concaveNFEval l = renderedLineMeet f0 fsegs l ⊓ f`, i.e.
`(⊓ⱼ convexSegEval (bⱼ + f0) rⱼ (truncSegs rⱼ fsegs)) ⊓ convexSegEval f0 fs fsegs`. Each meet
component is a computable `convexSegEval`; this is Theorem 4.2's output curve as a lower envelope of
explicit pieces (a single segment-list would require the lower-envelope merge of these pieces). -/
theorem minConv_concaveNFEval_render (f0 fs : ℝ≥0) (fsegs l : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs)
    (hl : ∀ rb ∈ l, rb.1 ≤ fs) (hne : l ≠ []) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (concaveNFEval l)
      = renderedLineMeet f0 fsegs l
          ⊓ (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) := by
  rw [minConv_concaveNFEval_eq_lineMeet_inf (isNeverBot_coe_nnreal _) hne,
    lineMeet_eq_renderedLineMeet f0 fs fsegs hfsort hfs l hl]

/-! ## Well-formedness of the rendered output
The convex-by-concave output is generally *convex-then-concave* (a convex head `f`, then
decreasing-rate bucket lines), so collapsing it to a single `convexSegEval`/`concaveNFEval` segment
list needs a general arbitrary-slope PWL datatype not present in this layer. What holds with the
current representation: the rendered meet is a genuine **monotone** curve. -/

/-- The `EReal` coe of a `convexSegEval` curve is monotone (it is `f`'s monotonicity lifted). -/
theorem monotone_coe_convexSegEval (a b : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) :
    Monotone (fun t => (((convexSegEval a b segs t : ℝ≥0) : ℝ) : EReal)) :=
  fun _ _ h =>
    EReal.coe_le_coe_iff.mpr (NNReal.coe_le_coe.mpr (monotone_convexSegEval b segs a h))

/-- The rendered bucket-line envelope is monotone (a finite meet of monotone convex curves; the
`topCurve` base is constant). -/
theorem monotone_renderedLineMeet (f0 : ℝ≥0) (fsegs l : List (ℝ≥0 × ℝ≥0)) :
    Monotone (renderedLineMeet f0 fsegs l) := by
  induction l with
  | nil => rw [renderedLineMeet_nil]; exact monotone_const
  | cons rb l ih =>
      rw [renderedLineMeet_cons]
      exact Monotone.inf (monotone_coe_convexSegEval (rb.2 + f0) rb.1 (truncSegs rb.1 fsegs)) ih

/-- **The rendered Theorem 4.2 output is a monotone curve** (well-formedness): for bucket rates
`≤ fs`, `f ∗ concaveNFEval l` is non-decreasing — it is the meet of the monotone rendered envelope
and the monotone `f`. (Collapsing it to one PWL segment list is the remaining `[infra]` step, needing
a general arbitrary-slope PWL datatype since the output is convex-then-concave.) -/
theorem monotone_minConv_concaveNFEval_render (f0 fs : ℝ≥0) (fsegs l : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs)
    (hl : ∀ rb ∈ l, rb.1 ≤ fs) (hne : l ≠ []) :
    Monotone (minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal))
      (concaveNFEval l)) := by
  rw [minConv_concaveNFEval_render f0 fs fsegs l hfsort hfs hl hne]
  exact Monotone.inf (monotone_renderedLineMeet f0 fsegs l)
    (monotone_coe_convexSegEval f0 fs fsegs)

end DeepWiki
