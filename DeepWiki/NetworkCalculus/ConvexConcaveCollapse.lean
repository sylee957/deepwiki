import DeepWiki.NetworkCalculus.ConcaveSegmentMerge
import DeepWiki.NetworkCalculus.ConvexConcaveReadback
import DeepWiki.NetworkCalculus.SegmentDeconvCurve

/-! # The Theorem 4.2 collapse, and the Lemma 4.6 dividend-side non-distribution
Two independent structural facts about convolution / deconvolution by concave PWL curves.

**Theorem 4.2 collapse.** Convolving `f` (any `IsNeverBot`) by a non-empty concave PWL curve
`concaveNFEval l` is the *line-meet* `lineMeet f l = ⊓ⱼ (f ∗ lineⱼ)` capped by `f` **once**:
`f ∗ concaveNFEval l = lineMeet f l ⊓ f`. The per-bucket readback (`minConv_tbEReal_eq_inf`)
produces a repeated `⊓ f` on every term; this pulls that single `f`-cap out of the meet,
separating the `f`-cap from the bucket-line lower envelope.

**Lemma 4.6 dividend asymmetry.** Deconvolution does *not* distribute over `⊓` in the
dividend: only `minDeconv (g₁ ⊓ g₂) h ≤ minDeconv g₁ h ⊓ minDeconv g₂ h`
(`minDeconv_inf_left_le`) holds. We make the failure a citable `¬∀` with an elementary
constant-curve witness whose two optimal shifts differ. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## GOAL 1 — pull the `f`-cap out of the per-bucket meet (Theorem 4.2 collapse) -/

/-- **The `⊓ f`-pull foldr identity (non-empty list).** Folding the per-term meets
`(g rb ⊓ f) ⊓ ·` from base `⊤` equals folding the bare terms `g rb ⊓ ·` and capping with a
single `⊓ f` at the end: `foldr (fun rb acc => (g rb ⊓ f) ⊓ acc) ⊤ l = (foldr (fun rb acc =>
g rb ⊓ acc) ⊤ l) ⊓ f`, for `l ≠ []`. The non-emptiness is needed: with `l = []` the left side
is `⊤` but the right is `⊤ ⊓ f = f`. Proven by induction, the singleton base discharging
`(g a ⊓ f) ⊓ ⊤ = (g a ⊓ ⊤) ⊓ f` and the cons step using `inf` assoc/comm/idem. -/
theorem foldr_inf_cap_pull {α : Type*} {β : Type*} [CompleteLattice β]
    (g : α → β) (f : β) {l : List α} (hne : l ≠ []) :
    l.foldr (fun rb acc => (g rb ⊓ f) ⊓ acc) ⊤
      = (l.foldr (fun rb acc => g rb ⊓ acc) ⊤) ⊓ f := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    rcases eq_or_ne t [] with rfl | ht
    · simp only [List.foldr_nil, List.foldr_cons]
      rw [inf_top_eq, inf_top_eq]
    · rw [List.foldr_cons, List.foldr_cons, ih ht]
      -- `(g a ⊓ f) ⊓ (acc ⊓ f) = (g a ⊓ acc) ⊓ f`
      generalize g a = x
      generalize t.foldr (fun rb acc => g rb ⊓ acc) ⊤ = y
      rw [inf_assoc, inf_left_comm f y, inf_idem, ← inf_assoc]

/-- The **line-meet** of `f` over a token-bucket list `l`: the pointwise meet of the
per-bucket line convolutions `f ∗ lineⱼ`, where `lineⱼ = rᵢ·t + bᵢ` (`= rateEReal rᵢ +
const bᵢ`), folded with `topCurve = ⊤` as the meet identity. This is the bucket-line lower
envelope, *without* the `f`-cap (`minConv_concaveNFEval_eq_lineMeet_inf` adds the single cap). -/
noncomputable def lineMeet (f : ℝ≥0 → EReal) (l : List (ℝ≥0 × ℝ≥0)) : ℝ≥0 → EReal :=
  l.foldr (fun rb acc =>
      minConv f (rateEReal rb.1 + Function.const ℝ≥0 ((rb.2 : ℝ) : EReal)) ⊓ acc)
    topCurve

/-- `lineMeet f []` is the `topCurve` base (`⊤`), the meet identity. -/
@[simp] theorem lineMeet_nil (f : ℝ≥0 → EReal) : lineMeet f [] = topCurve := rfl

/-- `lineMeet f (rb :: l) = (f ∗ lineᵣᵦ) ⊓ lineMeet f l`: one line-convolution met with the
rest. -/
@[simp] theorem lineMeet_cons (f : ℝ≥0 → EReal) (rb : ℝ≥0 × ℝ≥0) (l : List (ℝ≥0 × ℝ≥0)) :
    lineMeet f (rb :: l)
      = minConv f (rateEReal rb.1 + Function.const ℝ≥0 ((rb.2 : ℝ) : EReal)) ⊓ lineMeet f l :=
  rfl

/-- **Theorem 4.2 collapse.** For a non-empty token-bucket list `l` and any `IsNeverBot f`,
convolving `f` by the concave PWL curve `concaveNFEval l` is the line-meet capped by `f`
**once**: `f ∗ concaveNFEval l = lineMeet f l ⊓ f`, i.e.
`f ∗ (⊓ⱼ γⱼ) = (⊓ⱼ f ∗ lineⱼ) ⊓ f`. The per-bucket readback (`minConv_tbEReal_eq_inf`)
yields a repeated `⊓ f`; this pulls the single `f`-cap out of the meet (`foldr_inf_cap_pull`),
the `f ∗ ⊤ = ⊤` base supplying the meet identity so the non-empty list's first term carries
the surviving `f`. -/
theorem minConv_concaveNFEval_eq_lineMeet_inf {f : ℝ≥0 → EReal} (hf : IsNeverBot f)
    {l : List (ℝ≥0 × ℝ≥0)} (hne : l ≠ []) :
    minConv f (concaveNFEval l) = lineMeet f l ⊓ f := by
  rw [minConv_concaveNFEval_eq_foldr_inf hf, minConv_topCurve_right hf,
    show (topCurve : ℝ≥0 → EReal) = ⊤ from rfl, lineMeet,
    show (topCurve : ℝ≥0 → EReal) = ⊤ from rfl,
    foldr_inf_cap_pull
      (fun rb => minConv f (rateEReal rb.1 + Function.const ℝ≥0 ((rb.2 : ℝ) : EReal))) f hne]

-- Book wording check (Theorem 4.2 collapse): for non-empty `l` the convolution of `f` by the
-- concave PWL `concaveNFEval l` is the meet of the per-bucket line convolutions, capped by `f`
-- exactly once — `f ∗ concave = (⊓ⱼ f ∗ lineⱼ) ⊓ f`.
example {f : ℝ≥0 → EReal} (hf : IsNeverBot f) {l : List (ℝ≥0 × ℝ≥0)} (hne : l ≠ []) :
    minConv f (concaveNFEval l) = lineMeet f l ⊓ f :=
  minConv_concaveNFEval_eq_lineMeet_inf hf hne

/-- Single-bucket specialization: `f ∗ γ_{r,b} = (f ∗ lineᵣᵦ) ⊓ f`. The `lineMeet f [(r,b)]`
unfolds to `(f ∗ lineᵣᵦ) ⊓ ⊤ = f ∗ lineᵣᵦ`, recovering `minConv_tbEReal_eq_inf` through the
collapse. -/
theorem minConv_concaveNFEval_singleton_eq_lineMeet_inf {f : ℝ≥0 → EReal} (hf : IsNeverBot f)
    (r b : ℝ≥0) :
    minConv f (concaveNFEval [(r, b)])
      = minConv f (rateEReal r + Function.const ℝ≥0 ((b : ℝ) : EReal)) ⊓ f := by
  rw [minConv_concaveNFEval_eq_lineMeet_inf hf (by simp), lineMeet_cons, lineMeet_nil]
  show minConv f (rateEReal r + Function.const ℝ≥0 ((b : ℝ) : EReal)) ⊓ topCurve ⊓ f
      = minConv f (rateEReal r + Function.const ℝ≥0 ((b : ℝ) : EReal)) ⊓ f
  rw [show (topCurve : ℝ≥0 → EReal) = ⊤ from rfl, inf_top_eq]

/-! ## GOAL 2 — the Lemma 4.6 dividend asymmetry as a citable `¬∀` -/

/-- A constant `EReal`-valued curve `fun _ => c`. The deconvolution `minDeconv (const c) h t =
⨆ s, c - h s` is independent of `t`. -/
noncomputable def constCurve (c : EReal) : ℝ≥0 → EReal := fun _ => c

@[simp] theorem constCurve_apply (c : EReal) (t : ℝ≥0) : constCurve c t = c := rfl

/-- `minDeconv (constCurve c) h t = ⨆ s, c - h s` (the dividend is `t`-independent). -/
theorem minDeconv_constCurve (c : EReal) (h : ℝ≥0 → EReal) (t : ℝ≥0) :
    minDeconv (constCurve c) h t = ⨆ s : ℝ≥0, c - h s := by
  simp only [minDeconv, constCurve_apply]

/-- A two-value step curve: `b₀` at `0`, `b₁` everywhere positive. The shift dependence of its
deconvolution is what breaks dividend-side distribution (constant curves would tie). -/
noncomputable def stepCurve (b₀ b₁ : EReal) : ℝ≥0 → EReal := fun t => if t = 0 then b₀ else b₁

@[simp] theorem stepCurve_zero (b₀ b₁ : EReal) : stepCurve b₀ b₁ 0 = b₀ := by
  simp [stepCurve]

theorem stepCurve_pos (b₀ b₁ : EReal) {t : ℝ≥0} (ht : t ≠ 0) : stepCurve b₀ b₁ t = b₁ := by
  simp [stepCurve, ht]

/-- The meet of the two opposite steps is the constant `0`: `stepCurve 1 0 ⊓ stepCurve 0 1 =
constCurve 0` (at `0` it is `1 ⊓ 0 = 0`, elsewhere `0 ⊓ 1 = 0`). -/
theorem inf_stepCurve_eq_constCurve_zero :
    (stepCurve (1 : EReal) 0 ⊓ stepCurve 0 1) = constCurve 0 := by
  funext t
  rcases eq_or_ne t 0 with rfl | ht
  · simp [stepCurve, constCurve]
  · simp [stepCurve_pos, ht, constCurve]

/-- The deconvolution of `constCurve 0` by `constCurve 0` at `0` is `0`: every shifted
difference is `0 - 0 = 0`. -/
theorem minDeconv_constCurve_zero_self :
    minDeconv (constCurve (0 : EReal)) (constCurve 0) (0 : ℝ≥0) = 0 := by
  rw [minDeconv_constCurve]; simp [constCurve]

/-- The deconvolution of a `stepCurve b₀ b₁` by `constCurve 0` at `0` is `b₀ ⊔ b₁`: the
shifted differences range over `{b₀ - 0, b₁ - 0}`, whose supremum is the join. -/
theorem minDeconv_stepCurve_constCurve_zero (b₀ b₁ : EReal) :
    minDeconv (stepCurve b₀ b₁) (constCurve 0) (0 : ℝ≥0) = b₀ ⊔ b₁ := by
  apply le_antisymm
  · refine minDeconv_le (fun s => ?_)
    simp only [zero_add, constCurve_apply, sub_zero]
    rcases eq_or_ne s 0 with rfl | hs
    · simp [stepCurve]
    · rw [stepCurve_pos _ _ hs]; exact le_sup_right
  · refine sup_le ?_ ?_
    · calc b₀ = stepCurve b₀ b₁ (0 + 0) - constCurve 0 0 := by simp [stepCurve, constCurve]
        _ ≤ _ := sub_le_minDeconv _ _ 0 0
    · calc b₁ = stepCurve b₀ b₁ (0 + 1) - constCurve 0 1 := by
            rw [zero_add, stepCurve_pos _ _ one_ne_zero]; simp [constCurve]
        _ ≤ _ := sub_le_minDeconv _ _ 0 1

/-- `minDeconv (stepCurve 1 0) (constCurve 0) 0 = 1` (best shift `s = 0`). -/
theorem minDeconv_stepCurve10 :
    minDeconv (stepCurve (1 : EReal) 0) (constCurve 0) (0 : ℝ≥0) = 1 := by
  rw [minDeconv_stepCurve_constCurve_zero]; norm_num

/-- `minDeconv (stepCurve 0 1) (constCurve 0) 0 = 1` (best shift `s ≠ 0`). -/
theorem minDeconv_stepCurve01 :
    minDeconv (stepCurve (0 : EReal) 1) (constCurve 0) (0 : ℝ≥0) = 1 := by
  rw [minDeconv_stepCurve_constCurve_zero]; norm_num

/-- **Lemma 4.6 dividend asymmetry — the strict inequality witness.** The sub-distribution
`minDeconv_inf_left_le` is *strict* at this witness: `minDeconv (g₁ ⊓ g₂) h 0 < minDeconv g₁ h 0
⊓ minDeconv g₂ h 0` for `g₁ = stepCurve 1 0`, `g₂ = stepCurve 0 1`, `h = constCurve 0` — the
LHS is `0`, the RHS is `1`. The optimal shift differs between `g₁` (best at `s = 0`) and `g₂`
(best at `s ≠ 0`), so the meet of suprema strictly exceeds the supremum of the meet. -/
theorem minDeconv_inf_left_lt_witness :
    minDeconv (stepCurve (1 : EReal) 0 ⊓ stepCurve 0 1) (constCurve 0) 0
      < minDeconv (stepCurve (1 : EReal) 0) (constCurve 0) 0
          ⊓ minDeconv (stepCurve 0 1) (constCurve 0) 0 := by
  rw [inf_stepCurve_eq_constCurve_zero, minDeconv_constCurve_zero_self,
    minDeconv_stepCurve10, minDeconv_stepCurve01]
  norm_num

/-- **Lemma 4.6 dividend asymmetry, as a citable `¬∀`.** Deconvolution does *not* in general
distribute over `⊓` in the *dividend*: there exist `g₁, g₂, h : ℝ≥0 → EReal` and `t` with
`minDeconv (g₁ ⊓ g₂) h t ≠ minDeconv g₁ h t ⊓ minDeconv g₂ h t`. Witnesses: `g₁ = stepCurve 1 0`
(value `1` at `0`, `0` elsewhere), `g₂ = stepCurve 0 1` (the reverse), `h = constCurve 0`,
`t = 0`. Then `g₁ ⊓ g₂ = constCurve 0` so the LHS is `0`; but `minDeconv g₁ h 0 = 1` (best shift
`s = 0`) and `minDeconv g₂ h 0 = 1` (best shift `s ≠ 0`), so the RHS is `1 ⊓ 1 = 1 ≠ 0` — the
optimal shifts disagree. Direct consequence of the strict gap `minDeconv_inf_left_lt_witness`. -/
theorem not_forall_minDeconv_inf_left_eq :
    ¬ ∀ (g₁ g₂ h : ℝ≥0 → EReal) (t : ℝ≥0),
        minDeconv (g₁ ⊓ g₂) h t = minDeconv g₁ h t ⊓ minDeconv g₂ h t := by
  intro hcontra
  exact absurd (hcontra (stepCurve 1 0) (stepCurve 0 1) (constCurve 0) 0)
    (ne_of_lt minDeconv_inf_left_lt_witness)

end DeepWiki
