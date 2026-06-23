import DeepWiki.NetworkCalculus.ConvexConcaveRender
import DeepWiki.NetworkCalculus.PwlMerge

/-! # Theorem 4.2 output as a single explicit `Pwl`
The render (`minConv_concaveNFEval_render`) writes `f ∗ concave` as a meet of explicit `convexSegEval`
pieces; the list-producing merge (`mergeAll`) collapses finitely many `Pwl`s into one. This file is
the connector: folding `mergeAll` over the rendered pieces reads the convex-by-concave convolution as
the `EReal` coe of **one** named `Pwl`'s evaluation — `f ∗ concaveNFEval l = ⇑(mergeAll fPwl pieces)`.
-/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The `EReal` coe of an `ℝ≥0` minimum is the meet of the coes. -/
private theorem coeNN_min (a b : ℝ≥0) :
    (((min a b : ℝ≥0) : ℝ) : EReal) = (((a : ℝ≥0) : ℝ) : EReal) ⊓ (((b : ℝ≥0) : ℝ) : EReal) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, inf_eq_left.mpr (by exact_mod_cast h)]
  · rw [min_eq_right h, inf_eq_right.mpr (by exact_mod_cast h)]

/-- Bridge: the `coe` of a `foldl`-min running minimum equals the `foldr`-meet of the coes capped by
the coe of the base. (`min` is commutative/associative, so fold direction is immaterial.) -/
private theorem coe_foldl_min_eq_foldr_meet (t : ℝ≥0) :
    ∀ (ps : List Pwl) (c : ℝ≥0),
      (((ps.foldl (fun acc q => min acc (q.eval t)) c : ℝ≥0) : ℝ) : EReal)
        = (ps.foldr (fun q acc => (((q.eval t : ℝ≥0) : ℝ) : EReal) ⊓ acc) ⊤)
            ⊓ (((c : ℝ≥0) : ℝ) : EReal) := by
  intro ps
  induction ps with
  | nil => intro c; simp
  | cons q ps ih =>
      intro c
      rw [List.foldl_cons, List.foldr_cons, ih (min c (q.eval t)), coeNN_min c (q.eval t)]
      ac_rfl

/-- Pointwise reading of `renderedLineMeet`: the function-level foldr-meet evaluated at `t` is the
`EReal` foldr-meet of the per-bucket curve values at `t`. -/
private theorem renderedLineMeet_apply (f0 : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    ∀ l : List (ℝ≥0 × ℝ≥0),
      renderedLineMeet f0 fsegs l t
        = l.foldr (fun rb acc =>
            (((convexSegEval (rb.2 + f0) rb.1 (truncSegs rb.1 fsegs) t : ℝ≥0) : ℝ) : EReal) ⊓ acc)
          ⊤ := by
  intro l
  induction l with
  | nil => simp [renderedLineMeet_nil, topCurve]
  | cons rb l ih => rw [renderedLineMeet_cons, Pi.inf_apply, ih, List.foldr_cons]

/-- **Theorem 4.2, single-`Pwl` output.** For a convex PWL `f = convexSegEval f0 fs fsegs` and a
non-empty token-bucket list `l` with every rate `≤ fs`, the convex-by-concave convolution is the
`EReal` coe of **one** explicit `Pwl`'s evaluation: `f ∗ concaveNFEval l = ⇑(mergeAll fPwl pieces)`,
where `fPwl = ⟨f0, fsegs, fs⟩` and `pieces = l.map (fun (r,b) => ⟨b+f0, truncSegs r fsegs, r⟩)`. The
rendered meet (`minConv_concaveNFEval_render`) folds, via the list-producing `mergeAll`, into a single
arbitrary-slope PWL segment list — closing Theorem 4.2's output as one explicit curve. -/
theorem minConv_concaveNFEval_eq_mergeAll (f0 fs : ℝ≥0) (fsegs l : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs)
    (hl : ∀ rb ∈ l, rb.1 ≤ fs) (hne : l ≠ []) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (concaveNFEval l)
      = fun t => ((((mergeAll ⟨f0, fsegs, fs⟩
            (l.map (fun rb => (⟨rb.2 + f0, truncSegs rb.1 fsegs, rb.1⟩ : Pwl)))).eval t : ℝ≥0)
            : ℝ) : EReal) := by
  funext t
  rw [minConv_concaveNFEval_render f0 fs fsegs l hfsort hfs hl hne, Pi.inf_apply,
    mergeAll_eval, coe_foldl_min_eq_foldr_meet t, List.foldr_map, renderedLineMeet_apply f0 fsegs t l]
  rfl

end DeepWiki
