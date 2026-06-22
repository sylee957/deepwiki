import DeepWiki.NetworkCalculus.SegmentDeconvComposite
import Mathlib.Data.EReal.Operations

/-! # (min,plus) deconvolution by a concave piecewise-linear curve (Lemma 4.6, §4.3)
The tail of Lemma 4.6: deconvolution where the **divisor** is a general concave
piecewise-linear curve, presented as a *meet of rate-latency pieces*
`minInfList (divisors.map (fun p => rlE p.1 p.2))`. Distributing the divisor-side meet
through the deconvolution (`minDeconv_inf_list_right`) and reading each single-piece block as
its closed form (`minDeconv_rl_eq_term`) composes the per-piece blocks into one closed form,
a **join over the pieces** `⨆ p ∈ divisors, rlDeconvTerm R₁ T₁ p.1 p.2 t` (the headline
result `minDeconv_rl_minInfList`).

Also recorded here is the honest **dividend-side asymmetry**: deconvolution does *not* in
general distribute over a meet in the *dividend* — only the inequality
`minDeconv (g₁ ⊓ g₂) h ≤ minDeconv g₁ h ⊓ minDeconv g₂ h` holds
(`minDeconv_inf_left_le`), in contrast to the *equality* `minDeconv_inf_right` on the
divisor side. -/

namespace DeepWiki

open scoped NNReal

/-! ## A `⨆`-over-mapped-list helper -/

/-- A bounded supremum over a mapped list collapses the map: `⨆ h ∈ l.map f, F h = ⨆ p ∈ l,
F (f p)`. Proven by induction on `l`, peeling the `head`-term off both joins. -/
theorem biSup_map_list {ι α β : Type*} [CompleteLattice α]
    (l : List ι) (f : ι → β) (F : β → α) :
    (⨆ h ∈ l.map f, F h) = ⨆ p ∈ l, F (f p) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.mem_cons]
    simp only [iSup_or, iSup_sup_eq, iSup_iSup_eq_left]
    rw [ih]

/-! ## (a) Rate-latency deconvolved by a concave curve (min-list of rate-latencies) -/

/-- **Deconvolution of a rate-latency curve by a concave piecewise-linear curve (Lemma 4.6).**
For `divisors : List (ℝ≥0 × ℝ≥0)` read as rate-latency pieces `β_{p.1,p.2}`, the divisor
`minInfList (divisors.map (fun p => rlE p.1 p.2))` is their meet (a concave PWL curve); the
`(min,plus)` deconvolution of `β_{R₁,T₁}` by it is the **join over the pieces** of the
single-piece closed forms `rlDeconvTerm R₁ T₁ p.1 p.2 t` (each `R₁·(t + Tᵢ − T₁)₊` when
`R₁ ≤ Rᵢ`, else `⊤`). The empty list (divisor `⊤`) gives `⊥`. -/
theorem minDeconv_rl_minInfList (R₁ T₁ : ℝ≥0) (divisors : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    minDeconv (rlE R₁ T₁) (minInfList (divisors.map (fun p => rlE p.1 p.2))) t
      = ⨆ p ∈ divisors, rlDeconvTerm R₁ T₁ p.1 p.2 t := by
  rw [minDeconv_inf_list_right, biSup_map_list]
  exact biSup_congr (fun p _ => minDeconv_rl_eq_term R₁ T₁ p.1 p.2 t)

/-! ## (b) The same with token-bucket / affine pieces -/

/-- The closed-form deconvolution term value of one affine (token-bucket / leaky-bucket)
divisor `u ↦ b + q·u`, slow- or fast-divisor case: `↑(↑(a + p·t)) − ↑(↑b)` if `p ≤ q`, else
`⊤` (the divisor-side analog of `rlDeconvTerm`). -/
noncomputable def affineDeconvTerm (a p b q t : ℝ≥0) : EReal :=
  if p ≤ q then (((a + p * t : ℝ≥0) : ℝ) : EReal) - (((b : ℝ≥0) : ℝ) : EReal) else ⊤

/-- `affineDeconvTerm` is exactly `minDeconv (affineE a p) (affineE b q) t` (the slow- and
fast-divisor closed forms merged through the `p ≤ q` test). -/
theorem minDeconv_affine_eq_term (a p b q t : ℝ≥0) :
    minDeconv (affineE a p) (affineE b q) t = affineDeconvTerm a p b q t := by
  unfold affineDeconvTerm
  split_ifs with h
  · exact minDeconv_affine_le a p b q t h
  · exact minDeconv_affine_top a p b q t (lt_of_not_ge h)

/-- **Deconvolution of an affine curve by a concave PWL token-bucket envelope (Lemma 4.6).**
For `divisors : List (ℝ≥0 × ℝ≥0)` read as affine pieces `u ↦ p.1 + p.2·u`, the meet
`minInfList (divisors.map (fun p => affineE p.1 p.2))` is the token-bucket envelope; the
deconvolution of `u ↦ a + p·u` by it is the **join over the pieces** of the single-piece
closed forms `affineDeconvTerm a p p'.1 p'.2 t`. -/
theorem minDeconv_affine_minInfList (a p : ℝ≥0) (divisors : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    minDeconv (affineE a p) (minInfList (divisors.map (fun q => affineE q.1 q.2))) t
      = ⨆ q ∈ divisors, affineDeconvTerm a p q.1 q.2 t := by
  rw [minDeconv_inf_list_right, biSup_map_list]
  exact biSup_congr (fun q _ => minDeconv_affine_eq_term a p q.1 q.2 t)

/-! ## (c) Dividend side: only an inequality (no distribution over `⊓` in the dividend) -/

/-- **Deconvolution sub-distributes over `⊓` in the dividend (honest direction only):**
`minDeconv (g₁ ⊓ g₂) h t ≤ minDeconv g₁ h t ⊓ minDeconv g₂ h t`. Each term
`(g₁ ⊓ g₂)(t+s) − h s ≤ gᵢ(t+s) − h s`, so the supremum is below each `minDeconv gᵢ h t`.
Equality fails in general: the left side is a single `⨆_s` of a *meet* of shifted differences,
not the meet of the two separate suprema (the optimal shift `s` may differ between `g₁` and
`g₂`), so the divisor-side equality `minDeconv_inf_right` has no dividend-side mirror. -/
theorem minDeconv_inf_left_le {D : Type*} [Add D] (g₁ g₂ h : D → EReal) (t : D) :
    minDeconv (g₁ ⊓ g₂) h t ≤ minDeconv g₁ h t ⊓ minDeconv g₂ h t := by
  refine le_inf ?_ ?_
  · refine iSup_le (fun s => le_trans ?_ (sub_le_minDeconv g₁ h t s))
    rw [Pi.inf_apply]
    exact EReal.sub_le_sub inf_le_left le_rfl
  · refine iSup_le (fun s => le_trans ?_ (sub_le_minDeconv g₂ h t s))
    rw [Pi.inf_apply]
    exact EReal.sub_le_sub inf_le_right le_rfl

/-! ## Restatements (faithfulness checks against the book's wording) -/

/-- Empty divisor list (`minInfList` of the empty map = the `⊤` curve): the deconvolution is
`⊥`, matching the empty join `⨆ p ∈ []`. -/
example (R₁ T₁ t : ℝ≥0) :
    minDeconv (rlE R₁ T₁) (minInfList (([] : List (ℝ≥0 × ℝ≥0)).map (fun p => rlE p.1 p.2))) t
      = ⊥ := by
  rw [minDeconv_rl_minInfList]; simp

/-- Single-piece divisor list `[(R₂, T₂)]`: the concave-curve deconvolution collapses to the
single rate-latency closed form `rlDeconvTerm R₁ T₁ R₂ T₂ t`. -/
example (R₁ T₁ R₂ T₂ t : ℝ≥0) :
    minDeconv (rlE R₁ T₁) (minInfList ([(R₂, T₂)].map (fun p => rlE p.1 p.2))) t
      = rlDeconvTerm R₁ T₁ R₂ T₂ t := by
  rw [minDeconv_rl_minInfList]; simp

/-- Two-piece divisor list, both branches slow (`R₁ ≤ R₂`, `R₁ ≤ R₃`): the concave-curve
deconvolution is the join of the two finite rate-latency values `R₁·(t+T₂−T₁)₊ ⊔ R₁·(t+T₃−T₁)₊`
— the explicit Lemma 4.6 two-segment shape. -/
example (R₁ T₁ R₂ T₂ R₃ T₃ t : ℝ≥0) (h₂ : R₁ ≤ R₂) (h₃ : R₁ ≤ R₃) :
    minDeconv (rlE R₁ T₁) (minInfList ([(R₂, T₂), (R₃, T₃)].map (fun p => rlE p.1 p.2))) t
      = (((R₁ * (t + T₂ - T₁) : ℝ≥0) : ℝ) : EReal)
          ⊔ (((R₁ * (t + T₃ - T₁) : ℝ≥0) : ℝ) : EReal) := by
  rw [minDeconv_rl_minInfList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  unfold rlDeconvTerm
  simp [iSup_or, iSup_sup_eq, if_pos h₂, if_pos h₃]

/-- Two-piece divisor list with one fast branch (`R₂ < R₁`): that piece contributes `⊤`, so the
whole concave-curve deconvolution is `⊤` (the envelope is "too slow" on the `R₂` piece). -/
example (R₁ T₁ R₂ T₂ R₃ T₃ t : ℝ≥0) (h₂ : R₂ < R₁) :
    minDeconv (rlE R₁ T₁) (minInfList ([(R₂, T₂), (R₃, T₃)].map (fun p => rlE p.1 p.2))) t
      = ⊤ := by
  rw [minDeconv_rl_minInfList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  unfold rlDeconvTerm
  simp [iSup_or, iSup_sup_eq, if_neg (not_le_of_gt h₂)]

/-- Affine (token-bucket) single-piece divisor `[(b, q)]` with the slow-divisor case `p ≤ q`:
the deconvolution is the finite value `(a + p·t) − b`. -/
example (a p b q t : ℝ≥0) (hpq : p ≤ q) :
    minDeconv (affineE a p) (minInfList ([(b, q)].map (fun r => affineE r.1 r.2))) t
      = (((a + p * t : ℝ≥0) : ℝ) : EReal) - (((b : ℝ≥0) : ℝ) : EReal) := by
  rw [minDeconv_affine_minInfList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  unfold affineDeconvTerm
  simp [if_pos hpq]

/-- Dividend-side sub-distribution applied to two rate-latency dividends and one rate-latency
divisor: `minDeconv (β_{R₁,T₁} ⊓ β_{R₂,T₂}) β_{R₃,T₃} t ≤ (the two single deconvolutions met)`. -/
example (R₁ T₁ R₂ T₂ R₃ T₃ t : ℝ≥0) :
    minDeconv (rlE R₁ T₁ ⊓ rlE R₂ T₂) (rlE R₃ T₃) t
      ≤ minDeconv (rlE R₁ T₁) (rlE R₃ T₃) t ⊓ minDeconv (rlE R₂ T₂) (rlE R₃ T₃) t :=
  minDeconv_inf_left_le (rlE R₁ T₁) (rlE R₂ T₂) (rlE R₃ T₃) t

end DeepWiki
