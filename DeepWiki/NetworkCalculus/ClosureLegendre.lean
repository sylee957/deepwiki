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
theorem ne_bot_of_nonneg {f : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u) (u : ℝ≥0) :
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
        legendre_legendreConv (ne_bot_of_nonneg (legendreConvPow_nonneg hf n))
          (ne_bot_of_nonneg hf),
        ih, succ_nsmul]

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

/-- **`𝓛(f⋆) = ⨆ₙ (n • 𝓛 f)`** for a non-negative curve: the transform of the
sub-additive closure is the supremum of the additive multiples of `𝓛 f`. It
therefore depends only on `𝓛 f`. -/
theorem legendre_legendreClosure {f : ℝ≥0 → EReal} (hf : ∀ u, 0 ≤ f u) :
    legendre (legendreClosure f) = fun t => ⨆ n : ℕ, (n • legendre f) t := by
  have heq : legendreClosure f = fun u => ⨅ n : ℕ, legendreConvPow f n u := rfl
  rw [heq, legendre_iInf]
  funext t
  exact iSup_congr fun n => congrFun (legendre_legendreConvPow hf n) t

end DeepWiki
