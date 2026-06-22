import DeepWiki.NetworkCalculus.ConcavePWLNormalForm
import DeepWiki.NetworkCalculus.ConcaveDioid
import DeepWiki.NetworkCalculus.FunctionDioids

/-! # Concave (min,+) convolution is list concatenation (Theorem 4.1, concave case)
The concave analog of the convex segment-merge theorem. For concave piecewise-linear
curves — the pointwise infima of token-bucket lists `concaveNFEval l` — the (min,+)
convolution is just their pointwise **minimum** (since both are concave and null at the
origin, the inf-convolution collapses to the meet). In the token-bucket-list
representation that minimum is exactly **list concatenation**:
`minConv (concaveNFEval l₁) (concaveNFEval l₂) = concaveNFEval (l₁ ++ l₂)`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## Concatenation is the pointwise infimum -/

/-- The concave PWL evaluation of a concatenation is the pointwise infimum of the two
evaluations: `concaveNFEval (l₁ ++ l₂) = concaveNFEval l₁ ⊓ concaveNFEval l₂` (an
`inf`-over-`++` fold with `topCurve = ⊤` as the identity). -/
@[simp] theorem concaveNFEval_append (l₁ l₂ : List (ℝ≥0 × ℝ≥0)) :
    concaveNFEval (l₁ ++ l₂) = concaveNFEval l₁ ⊓ concaveNFEval l₂ := by
  induction l₁ with
  | nil =>
      rw [List.nil_append, concaveNFEval_nil]
      funext t
      show concaveNFEval l₂ t = topCurve t ⊓ concaveNFEval l₂ t
      rw [topCurve, top_inf_eq]
  | cons rb l ih =>
      rw [List.cons_append, concaveNFEval_cons, concaveNFEval_cons, ih, inf_assoc]

/-! ## The origin value of a non-empty concave PWL function is `0` -/

/-- A non-empty concave PWL function vanishes at the origin: every token-bucket is `0`
at `t = 0`, so their infimum is `0`. -/
theorem concaveNFEval_zero_of_ne_nil {l : List (ℝ≥0 × ℝ≥0)} (hne : l ≠ []) :
    concaveNFEval l 0 = 0 := by
  cases l with
  | nil => exact absurd rfl hne
  | cons rb l =>
      rw [concaveNFEval_cons, Pi.inf_apply, tbEReal_zero, inf_eq_left]
      exact concaveNFEval_nonneg l 0

/-! ## Concave convolution is the pointwise minimum, i.e. list concatenation -/

/-- **Theorem 4.1 (concave case), meet form.** The (min,+) convolution of two
non-empty concave PWL functions is their pointwise minimum: both are concave and null
at the origin, so the inf-convolution collapses to the meet (`minConv_eq_inf_of_null`). -/
theorem minConv_concaveNFEval_eq_inf {l₁ l₂ : List (ℝ≥0 × ℝ≥0)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    minConv (concaveNFEval l₁) (concaveNFEval l₂) = concaveNFEval l₁ ⊓ concaveNFEval l₂ :=
  minConv_eq_inf_of_null _ _ (isConcaveEReal_concaveNFEval l₁) (isConcaveEReal_concaveNFEval l₂)
    (concaveNFEval_zero_of_ne_nil h₁) (concaveNFEval_zero_of_ne_nil h₂)

/-- **Theorem 4.1 (concave case), concatenation form.** The (min,+) convolution of two
non-empty concave PWL functions is the concave PWL function of the *concatenated*
token-bucket lists: `(⋀ᵢ γ_{r¹ᵢ,b¹ᵢ}) ∗ (⋀ⱼ γ_{r²ⱼ,b²ⱼ}) = ⋀ over the merged list`. -/
theorem minConv_concaveNFEval_eq_concaveNFEval_append
    {l₁ l₂ : List (ℝ≥0 × ℝ≥0)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    minConv (concaveNFEval l₁) (concaveNFEval l₂) = concaveNFEval (l₁ ++ l₂) := by
  rw [minConv_concaveNFEval_eq_inf h₁ h₂, concaveNFEval_append]

-- Book wording check (Theorem 4.1, concave case): for concave PWL functions the (min,+)
-- convolution is the pointwise minimum, realized on token-bucket lists as concatenation.
example {l₁ l₂ : List (ℝ≥0 × ℝ≥0)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    minConv (concaveNFEval l₁) (concaveNFEval l₂) = concaveNFEval (l₁ ++ l₂) :=
  minConv_concaveNFEval_eq_concaveNFEval_append h₁ h₂

/-! ## Convolution by a concave PWL distributes over its token-bucket meet (toward Theorem 4.2) -/

/-- **Toward Theorem 4.2 (convex-by-concave).** Convolution by a concave PWL `concaveNFEval l`
(an infimum of token buckets) distributes over the meet: `f ∗ (⊓ⱼ γⱼ) = ⊓ⱼ (f ∗ γⱼ)`. In the
foldr representation `concaveNFEval l = foldr (γ ⊓ ·) ⊤`, convolution pushes inside termwise
(via `minConv_inf_fun`), so `f ∗ concaveNFEval l = foldr ((f ∗ γⱼ) ⊓ ·) (f ∗ ⊤)`. For a *convex*
`f` each piece `f ∗ γⱼ` is then the convex-by-line value (Lemma 4.1), which is what makes the
convex-by-concave convolution computable. -/
theorem minConv_concaveNFEval_foldr (f : ℝ≥0 → EReal) (l : List (ℝ≥0 × ℝ≥0)) :
    minConv f (concaveNFEval l)
      = l.foldr (fun rb acc => minConv f (tbEReal rb.1 rb.2) ⊓ acc) (minConv f topCurve) := by
  induction l with
  | nil => rfl
  | cons rb l ih => rw [concaveNFEval_cons, minConv_inf_fun, ih, List.foldr_cons]

end DeepWiki
