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

/-- **§3.3 Second Method (homogeneous difference equation):** if the `φ`-convolution of the weights
vanishes pointwise — `ψⱼ · ∑ₖ φₖ ψ_{j+(h−k)} = 0` for every `j` (which holds for `h > deg θ`, since
`∑ₖ φₖ ψ_{m−k} = θ_m = 0` for `m > deg θ` and `ψⱼ = 0` for `j < 0`) — then the linear-process
autocovariance `γ(m) = σ² ∑ⱼ ψⱼ ψ_{j+m}` satisfies the homogeneous recursion
`∑_{k=0}^p φₖ γ(h−k) = 0`. -/
theorem acvf_homogeneous {ψ : ℤ → ℝ} (hψ : Summable ψ) (φ : Polynomial ℝ) (σ2 : ℝ) (h : ℤ)
    (hvanish : ∀ j : ℤ,
      ψ j * ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ψ (j + (h - k)) = 0) :
    ∑ k ∈ Finset.range (φ.natDegree + 1),
      φ.coeff k * (σ2 * ∑' j : ℤ, ψ j * ψ (j + (h - k))) = 0 := by
  have hzero : ∑ k ∈ Finset.range (φ.natDegree + 1),
      φ.coeff k * ∑' j : ℤ, ψ j * ψ (j + (h - k)) = 0 := by
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (f := fun (k : ℕ) (j : ℤ) => φ.coeff k * (ψ j * ψ (j + (h - k))))
      fun k _ => (summable_mul_shift hψ (h - k)).mul_left (φ.coeff k)]
    refine (tsum_congr fun j => ?_).trans tsum_zero
    rw [← hvanish j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [show (∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * (σ2 * ∑' j : ℤ, ψ j * ψ (j + (h - k))))
      = σ2 * ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ∑' j : ℤ, ψ j * ψ (j + (h - k)) from by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hzero, mul_zero]

end DeepWiki.TimeSeries
