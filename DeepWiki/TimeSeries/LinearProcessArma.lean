import DeepWiki.TimeSeries.LinearProcess
import DeepWiki.TimeSeries.ArmaProcesses

/-! # The linear process over ARMA white noise (Theorem 3.2.1)
Combining the `L²` linear-process autocovariance with the white-noise → `L²` bridge: a linear
process `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` driven by a genuine `WN(0,σ²)` (Definition 3.1.1) has the Theorem 3.2.1
autocovariance `γ(h) = σ² ∑ₖ ψₖ ψ_{k+h}`. This is the fully book-faithful endpoint: it starts from
the book's `IsWhiteNoise` predicate, not an abstract `L²`-orthogonality hypothesis. -/

namespace DeepWiki.TimeSeries

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Theorem 3.2.1 for a book `WN(0,σ²)`:** a linear process `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` (`∑ⱼ |ψⱼ| < ∞`)
driven by white noise `Z` (Definition 3.1.1, square-integrable and uniformly `L²`-bounded after
embedding) has autocovariance `γ(h) = ⟪X_{t+h}, Xₜ⟫ = σ² ∑ₖ ψₖ ψ_{k+h}`. -/
theorem isWhiteNoise_linearProcess_acvf [IsProbabilityMeasure μ] {ψ : ℤ → ℝ} (hψ : Summable ψ)
    {Z : ℤ → Ω → ℝ} (hmem : ∀ t, MemLp (Z t) 2 μ) {σ2 : ℝ} (hwn : IsWhiteNoise Z μ σ2)
    {C : ℝ} (hZb : ∀ t, ‖toLpSeq Z hmem t‖ ≤ C) (t h : ℤ) :
    inner ℝ (linearProcessLp ψ (toLpSeq Z hmem) (t + h)) (linearProcessLp ψ (toLpSeq Z hmem) t)
      = σ2 * ∑' k, ψ k * ψ (k + h) :=
  linearProcessLp_inner_toLpSeq hψ hmem hZb (hwn.integral_mul hmem) t h

end DeepWiki.TimeSeries
