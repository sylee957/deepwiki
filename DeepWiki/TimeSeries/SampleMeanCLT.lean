import DeepWiki.TimeSeries.SampleAutocovariance
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Asymptotic normality of the sample mean (§7.1, iid base case)
The foundational large-sample result of Chapter 7: for an iid finite-variance noise sequence
`Z₀, Z₁, …` with mean `μ` and variance `σ²`, the standardized sample mean satisfies the central
limit theorem `√n (X̄ₙ − μ) ⇒ N(0, σ²)`. This is the iid base case on which the linear-process,
sample-autocovariance, and Yule–Walker central limit theorems are built, obtained here by wiring
Mathlib's classical central limit theorem (`tendstoInDistribution_inv_sqrt_mul_sum_sub`) to the
sample mean `sampleMean`. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}

/-- The standardized sample mean equals the centered, `(√n)⁻¹`-scaled partial sum:
`√n (x̄ₙ − μ) = (√n)⁻¹ (∑_{t<n} xₜ − n μ)` — the algebraic identity bridging `sampleMean` to the
form of Mathlib's central limit theorem. -/
theorem sqrt_mul_sampleMean_sub (n : ℕ) (x : ℕ → ℝ) (μ : ℝ) :
    Real.sqrt n * (sampleMean n x - μ)
      = (Real.sqrt n)⁻¹ * ((∑ t ∈ Finset.range n, x t) - (n : ℝ) * μ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [sampleMean]
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hs : Real.sqrt n ≠ 0 := by positivity
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn'.le
    rw [sampleMean]
    refine mul_left_cancel₀ hs ?_
    rw [← mul_assoc, hsq, ← mul_assoc, mul_inv_cancel₀ hs, one_mul, mul_sub, ← mul_assoc,
      mul_inv_cancel₀ hn'.ne', one_mul]

variable [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- **Central limit theorem for the sample mean of iid noise (§7.1, base case):** for an iid
sequence `Z : ℕ → Ω → ℝ` (`iIndepFun`, identically distributed) with `Z₀ ∈ L²`, mean `μ = E Z₀`
and variance `σ² = Var Z₀`, the standardized sample mean `√n (X̄ₙ − μ)` converges in distribution
to `N(0, σ²)`. The foundation of the Chapter 7–8 large-sample theory, from Mathlib's classical
central limit theorem via `sqrt_mul_sampleMean_sub`. -/
theorem iidNoise_sampleMean_clt {Z : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 Var[Z 0; P].toNNReal) P') (hmem : MemLp (Z 0) 2 P)
    (hindep : iIndepFun Z P) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n * (sampleMean n (fun t => Z t ω) - P[Z 0]))
      atTop Y (fun _ => P) P' := by
  have heq : (fun (n : ℕ) ω => Real.sqrt n * (sampleMean n (fun t => Z t ω) - P[Z 0]))
      = fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ((∑ k ∈ Finset.range n, Z k ω) - (n : ℝ) * P[Z 0]) := by
    ext n ω
    exact sqrt_mul_sampleMean_sub n _ _
  rw [heq]
  exact tendstoInDistribution_inv_sqrt_mul_sum_sub hY hmem hindep hident

/-- **Slutsky's theorem for the central limit theorem (`L²` form):** if `Yₙ ⇒ Z` in distribution and
`Xₙ` is asymptotically `L²`-close to `Yₙ` (`‖Xₙ − Yₙ‖₂ → 0`), then `Xₙ ⇒ Z`. The bridge that
transfers a central limit theorem along a negligible `L²` perturbation — the step that turns the iid
sample-mean CLT into the linear-process / `MA(q)` central limit theorems. -/
theorem tendstoInDistribution_of_tendsto_eLpNorm_sub {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hY : TendstoInDistribution Y atTop Z (fun _ => P) P') (hX : ∀ n, AEStronglyMeasurable (X n) P)
    (hL2 : Tendsto (fun n => eLpNorm (X n - Y n) 2 P) atTop (𝓝 0)) :
    TendstoInDistribution X atTop Z (fun _ => P) P' := by
  refine tendstoInDistribution_of_tendstoInMeasure_sub (Y := X) Z hY ?_
    (fun n => (hX n).aemeasurable)
  refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    (fun n => (hX n).sub ((hY.forall_aemeasurable n).aestronglyMeasurable))
    aestronglyMeasurable_zero ?_
  simpa using hL2

-- Faithfulness: the limit is the centered Gaussian whose variance is the noise variance `Var Z₀`,
-- and the statistic is exactly the standardized sample mean `√n (X̄ₙ − μ)`.
example {Z : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 Var[Z 0; P].toNNReal) P') (hmem : MemLp (Z 0) 2 P)
    (hindep : iIndepFun Z P) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n * (sampleMean n (fun t => Z t ω) - P[Z 0]))
      atTop Y (fun _ => P) P' :=
  iidNoise_sampleMean_clt hY hmem hindep hident

end DeepWiki.TimeSeries
