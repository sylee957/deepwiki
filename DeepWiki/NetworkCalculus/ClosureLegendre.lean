import DeepWiki.NetworkCalculus.ContainerQuotient
import DeepWiki.NetworkCalculus.Closures

/-! # The sub-additive closure modulo the Legendre–Fenchel transform (Lemma 4.10 [4.12])
The Legendre–Fenchel transform of an `⨅`-family is the `⨆` of the transforms
(`legendre_iInf`, generalizing `legendre_inf`); applied to the inf-convolution
powers this shows the transform of the (min,+) **sub-additive closure** depends
only on the transform of the input — so the closure descends to the quotient
dioid `ℱ↑/𝓛` (`SameLegendre.legendreClosure`, equation [4.9]/[4.12]). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## The Legendre–Fenchel transform commutes with `⨅` (turning it into `⨆`)

The transform `𝓛` is the pointwise sup of affine slices, so it sends an
infimum of curves to the supremum of their transforms — the unbounded-index
generalization of `legendre_inf` (`𝓛(f ⊓ g) = 𝓛 f ⊔ 𝓛 g`). -/

/-- **`𝓛(⨅ᵢ gᵢ) = ⨆ᵢ 𝓛(gᵢ)`**: the Legendre–Fenchel transform turns a pointwise
infimum of curves into the pointwise supremum of their transforms (the `iInf`
generalization of `legendre_inf`). -/
theorem legendre_iInf {ι : Sort*} (g : ι → ℝ≥0 → EReal) :
    legendre (fun u => ⨅ i, g i u) = fun t => ⨆ i, legendre (g i) t := by
  funext t
  rw [legendre_apply]
  have hslice : ∀ u : ℝ≥0,
      (((t * u : ℝ≥0) : ℝ) : EReal) - (⨅ i, g i u)
        = ⨆ i, ((((t * u : ℝ≥0) : ℝ) : EReal) - g i u) :=
    fun u => coe_sub_iInf _ _
  calc (⨆ u : ℝ≥0, (((t * u : ℝ≥0) : ℝ) : EReal) - (⨅ i, g i u))
      = ⨆ u : ℝ≥0, ⨆ i, ((((t * u : ℝ≥0) : ℝ) : EReal) - g i u) := by
        exact iSup_congr hslice
    _ = ⨆ i, ⨆ u : ℝ≥0, ((((t * u : ℝ≥0) : ℝ) : EReal) - g i u) := iSup_comm
    _ = ⨆ i, legendre (g i) t := by
        exact iSup_congr fun i => (legendre_apply (g i) t).symm

/-- `𝓛(⨅ᵢ gᵢ) t = ⨆ᵢ 𝓛(gᵢ) t` pointwise. -/
theorem legendre_iInf_apply {ι : Sort*} (g : ι → ℝ≥0 → EReal) (t : ℝ≥0) :
    legendre (fun u => ⨅ i, g i u) t = ⨆ i, legendre (g i) t :=
  congrFun (legendre_iInf g) t

/-! ## The inf-convolution closure on `ℝ≥0 → EReal`

The (min,+) sub-additive closure `f⋆ = ⨅ₙ fⁿ` of the inf-convolution
`legendreConv`, with the convolution unit `δ₀` (`0` at the origin, `⊤`
elsewhere) as the zeroth power. -/

/-- The inf-convolution unit `δ₀`: `0` at the origin, `⊤` (= `+∞`) elsewhere —
the neutral element of `legendreConv` and the zeroth convolution power. -/
noncomputable def legendreUnit : ℝ≥0 → EReal := fun u => if u = 0 then 0 else ⊤

/-- `legendreUnit 0 = 0`. -/
@[simp] theorem legendreUnit_zero : legendreUnit 0 = 0 := if_pos rfl

/-- `legendreUnit` is non-negative: it is `0` or `⊤`. -/
theorem legendreUnit_nonneg (u : ℝ≥0) : 0 ≤ legendreUnit u := by
  unfold legendreUnit; split_ifs with h
  · exact le_rfl
  · exact le_top

/-- **`𝓛(δ₀) = 0`**: the transform of the inf-convolution unit is the zero
function (the unit `0` at the origin gives slice `0`; positive `u` give `⊥`). -/
theorem legendre_legendreUnit : legendre legendreUnit = 0 := by
  funext t
  rw [legendre_apply]
  apply le_antisymm
  · refine iSup_le fun u => ?_
    rcases eq_or_ne u 0 with rfl | hu
    · rw [legendreUnit_zero, mul_zero]
      simp
    · rw [show legendreUnit u = ⊤ from if_neg hu, EReal.sub_top]
      exact bot_le
  · refine le_iSup_of_le 0 ?_
    rw [legendreUnit_zero, mul_zero]
    simp

/-- `n`-fold inf-convolution power `fⁿ` under `legendreConv`; `f⁰ = δ₀`. -/
noncomputable def legendreConvPow (f : ℝ≥0 → EReal) : ℕ → (ℝ≥0 → EReal)
  | 0 => legendreUnit
  | n + 1 => legendreConv (legendreConvPow f n) f

/-- `f⁰ = δ₀`. -/
@[simp] theorem legendreConvPow_zero (f : ℝ≥0 → EReal) :
    legendreConvPow f 0 = legendreUnit := rfl

/-- `f^(n+1) = fⁿ ⊗ f`. -/
theorem legendreConvPow_succ (f : ℝ≥0 → EReal) (n : ℕ) :
    legendreConvPow f (n + 1) = legendreConv (legendreConvPow f n) f := rfl

/-- A `legendreConv` of two non-negative curves is non-negative: each summand
`f u + g v ≥ 0`, so the infimum is `≥ 0`. -/
theorem legendreConv_nonneg {f g : ℝ≥0 → EReal}
    (hf : ∀ u, 0 ≤ f u) (hg : ∀ v, 0 ≤ g v) (t : ℝ≥0) :
    0 ≤ legendreConv f g t := by
  rw [legendreConv_apply]
  refine le_iInf fun p => ?_
  have := add_le_add (hf p.1.1) (hg p.1.2)
  rwa [add_zero] at this

/-- Each inf-convolution power of a non-negative curve is non-negative
(`legendreUnit` is, and `legendreConv` preserves it). -/
theorem legendreConvPow_nonneg {f : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u)
    (n : ℕ) (u : ℝ≥0) : 0 ≤ legendreConvPow f n u := by
  induction n generalizing u with
  | zero => exact legendreUnit_nonneg u
  | succ n ih =>
      rw [legendreConvPow_succ]
      exact legendreConv_nonneg (fun u => ih u) hf u

/-- A non-negative curve is proper (never `⊥`). -/
theorem apply_ne_bot_of_nonneg {f : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u) (u : ℝ≥0) :
    f u ≠ ⊥ := fun h => by simpa [h] using hf u

/-- **`𝓛(fⁿ) = n • 𝓛 f`** for a non-negative curve `f`: the transform of an
inf-convolution power is the `n`-fold additive multiple of the transform
(`𝓛(f⁰) = 𝓛 δ₀ = 0`; `𝓛(f^(n+1)) = 𝓛 fⁿ + 𝓛 f` via `legendre_legendreConv`). -/
theorem legendre_legendreConvPow {f : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u) (n : ℕ) :
    legendre (legendreConvPow f n) = n • legendre f := by
  induction n with
  | zero => rw [legendreConvPow_zero, legendre_legendreUnit, zero_smul]
  | succ n ih =>
      rw [legendreConvPow_succ,
        legendre_legendreConv (apply_ne_bot_of_nonneg (legendreConvPow_nonneg hf n))
          (apply_ne_bot_of_nonneg hf),
        ih, succ_nsmul]

/-- `f¹ = f` for a non-negative curve: the unit power `δ₀ ⊗ f` is `f`, since the
only finite summand is the origin split `(0, t)` giving `0 + f t = f t`. -/
theorem legendreConvPow_one {f : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u) :
    legendreConvPow f 1 = f := by
  funext t
  rw [legendreConvPow_succ, legendreConvPow_zero, legendreConv_apply]
  apply le_antisymm
  · exact iInf_le_of_le ⟨(0, t), zero_add t⟩ (by rw [legendreUnit_zero, zero_add])
  · refine le_iInf fun p => ?_
    obtain ⟨⟨u, v⟩, (huv : u + v = t)⟩ := p
    rcases eq_or_ne u 0 with rfl | hu
    · rw [show (0 : ℝ≥0) + v = v from zero_add v] at huv
      subst huv
      rw [legendreUnit_zero, zero_add]
    · rw [show legendreUnit u = ⊤ from if_neg hu,
        EReal.top_add_of_ne_bot (apply_ne_bot_of_nonneg hf v)]
      exact le_top

/-- The (min,+) **sub-additive closure** `f⋆ = ⨅ₙ fⁿ` of a curve under the
inf-convolution `legendreConv`. -/
noncomputable def legendreClosure (f : ℝ≥0 → EReal) : ℝ≥0 → EReal :=
  fun t => ⨅ n : ℕ, legendreConvPow f n t

/-- `f⋆ t = ⨅ₙ fⁿ t` (the defining infimum over convolution powers). -/
theorem legendreClosure_apply (f : ℝ≥0 → EReal) (t : ℝ≥0) :
    legendreClosure f t = ⨅ n : ℕ, legendreConvPow f n t := rfl

/-- The closure of a non-negative curve is non-negative. -/
theorem legendreClosure_nonneg {f : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u) (t : ℝ≥0) :
    0 ≤ legendreClosure f t :=
  le_iInf fun n => legendreConvPow_nonneg hf n t

/-- **The closure lies below the input**: `f⋆ ≤ f` pointwise for a non-negative
curve (the `n = 1` power `f¹ = f` is one of the terms of the infimum). -/
theorem legendreClosure_le {f : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u) (t : ℝ≥0) :
    legendreClosure f t ≤ f t :=
  (iInf_le _ 1).trans_eq (congrFun (legendreConvPow_one hf) t)

/-- **`𝓛 f ≤ 𝓛(f⋆)`**: since the closure lies below `f` (`legendreClosure_le`),
its larger value is subtracted, so the transform is pointwise larger
(`legendre_antitone`). -/
theorem legendre_le_legendre_legendreClosure {f : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u)
    (t : ℝ≥0) : legendre f t ≤ legendre (legendreClosure f) t :=
  legendre_antitone (fun u => legendreClosure_le hf u) t

/-- **`𝓛(f⋆) = ⨆ₙ (n • 𝓛 f)`** for a non-negative curve: the transform of the
sub-additive closure is the supremum of the additive multiples of `𝓛 f`. It
therefore depends only on `𝓛 f`. -/
theorem legendre_legendreClosure {f : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u) :
    legendre (legendreClosure f) = fun t => ⨆ n : ℕ, (n • legendre f) t := by
  have heq : legendreClosure f = fun u => ⨅ n : ℕ, legendreConvPow f n u := rfl
  rw [heq, legendre_iInf]
  funext t
  exact iSup_congr fun n => congrFun (legendre_legendreConvPow hf n) t

/-! ## Lemma 4.10 [4.12] — the closure descends to the quotient `ℱ↑/𝓛`

The transform of the closure depends only on the transform of the input
(`legendre_legendreClosure`: `𝓛(f⋆) = ⨆ₙ n • 𝓛 f`), so the sub-additive
closure `⋆` respects the Legendre–Fenchel congruence: it is well-defined on the
quotient dioid `ℱ↑/𝓛` (equation [4.9], the closure case of [4.12]). -/

namespace Container

/-- **[4.12]/[4.9] is well-defined: `⋆` respects `≡_𝓛`.** Two non-negative curves
with the same Legendre–Fenchel transform have closures with the same transform —
`𝓛 f = 𝓛 g` gives `𝓛(f⋆) = ⨆ₙ n • 𝓛 f = ⨆ₙ n • 𝓛 g = 𝓛(g⋆)`
(`legendre_legendreClosure`). So the sub-additive closure descends to `ℱ↑/𝓛`. -/
theorem SameLegendre.legendreClosure {f g : ℝ≥0 → EReal}
    (hf : ∀ u, 0 ≤ f u) (hg : ∀ v, 0 ≤ g v) (h : SameLegendre f g) :
    SameLegendre (legendreClosure f) (legendreClosure g) := by
  unfold SameLegendre at h ⊢
  rw [legendre_legendreClosure hf, legendre_legendreClosure hg, h]

/-- **Lemma 4.10 [4.12]** (the exact book equivalence): the closure of the
canonical representative `Cvx f = f̂` lands in the same class as `f⋆`
(`[f]⋆_𝓛 = [f⋆]_𝓛`, i.e. `𝓛((f̂)⋆) = 𝓛(f⋆)`) **iff** their convex hulls agree
(`Cvx((Cvx f)⋆) = Cvx(f⋆)`). This is `sameLegendre_iff_biconj_eq` at the two
closures — exactly "follows from Propositions 4.2 and 4.3". -/
theorem sameLegendre_legendreClosure_biconj_iff (f : ℝ≥0 → EReal) :
    legendre (legendreClosure (biconj f)) = legendre (legendreClosure f)
      ↔ biconj (legendreClosure (biconj f)) = biconj (legendreClosure f) :=
  sameLegendre_iff_biconj_eq (legendreClosure (biconj f)) (legendreClosure f)

/-- The truth of [4.12]'s class equality `[f]⋆_𝓛 = [f⋆]_𝓛` for a non-negative
curve `f` whose convex hull `f̂` is also non-negative: closing `f` and closing
its canonical representative `f̂` give the same Legendre–Fenchel class
(`𝓛((f̂)⋆) = 𝓛(f⋆)`), since `f̂` and `f` already share their transform
(`legendre_biconj`). -/
theorem sameLegendre_legendreClosure_biconj {f : ℝ≥0 → EReal}
    (hf : ∀ u, 0 ≤ f u) (hfhat : ∀ u, 0 ≤ biconj f u) :
    SameLegendre (legendreClosure (biconj f)) (legendreClosure f) :=
  SameLegendre.legendreClosure hfhat hf (legendre_biconj f)

end Container

/-! ## Faithfulness checks (anonymous restatements vs the book) -/

-- `legendre_iInf` generalizes `legendre_inf` (`𝓛(f ⊓ g) = 𝓛 f ⊔ 𝓛 g`).
example (f g : ℝ≥0 → EReal) : legendre (f ⊓ g) = legendre f ⊔ legendre g :=
  legendre_inf f g

-- Lemma 4.10 [4.12] (well-definedness, the [4.9] closure case): `⋆` respects `≡_𝓛`.
example {f g : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u) (hg : ∀ v, 0 ≤ g v)
    (h : legendre f = legendre g) :
    legendre (legendreClosure f) = legendre (legendreClosure g) :=
  Container.SameLegendre.legendreClosure hf hg h

-- Lemma 4.10 [4.12] exact form: `[f]⋆_𝓛 = [f⋆]_𝓛 ⇔ Cvx(Cvx f⋆) = Cvx(f⋆)`,
-- with `Cvx = biconj` and `[f]⋆_𝓛` computed via the canonical representative `Cvx f`.
example (f : ℝ≥0 → EReal) :
    legendre (legendreClosure (Container.biconj f)) = legendre (legendreClosure f)
      ↔ Container.biconj (legendreClosure (Container.biconj f))
          = Container.biconj (legendreClosure f) :=
  Container.sameLegendre_legendreClosure_biconj_iff f

end DeepWiki
