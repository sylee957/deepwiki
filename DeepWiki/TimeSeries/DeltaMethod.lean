import DeepWiki.TimeSeries.MultivariateCLT
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # The delta method (Brockwell–Davis Example 6.4.2)
The one-dimensional delta method: if `√n (Xₙ − μ)` is asymptotically normal and `Xₙ →ᵖ μ`, then for
`g` differentiable at `μ`, `√n (g Xₙ − g μ)` is asymptotically normal with the derivative-scaled
limit `g'(μ) · Y₀`. Proved without tightness, via the slope decomposition
`√n (g Xₙ − g μ) = slope(Xₙ) · √n (Xₙ − μ)` (Slutsky's product theorem, the slope tending in measure
to `g'(μ)`). The §6.4 inference engine for smooth functionals of asymptotically normal estimators
(e.g. the sample autocorrelation `ρ̂ = γ̂(h)/γ̂(0)` in Bartlett's formula). -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Continuous mapping for convergence in measure to a constant:** if `fₙ →ᵖ c` and `h` is
continuous at `c`, then `h ∘ fₙ →ᵖ h c`. The set `{|h(fₙ) − h c| ≥ ε}` is contained in
`{|fₙ − c| ≥ δ}` for the continuity modulus `δ`, whose measure vanishes. -/
theorem tendstoInMeasure_comp_const {f : ℕ → Ω → ℝ} {c : ℝ} {h : ℝ → ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => c)) (hc : ContinuousAt h c) :
    TendstoInMeasure μ (fun n ω => h (f n ω)) atTop (fun _ => h c) := by
  intro ε hε
  rcases lt_or_ge ε ⊤ with hεlt | hεtop
  · obtain ⟨δ, hδ, hδh⟩ :=
      Metric.continuousAt_iff.mp hc ε.toReal (ENNReal.toReal_pos hε.ne' hεlt.ne)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hf (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)) (fun _ => zero_le) (fun n => measure_mono ?_)
    intro ω hω
    simp only [Set.mem_setOf_eq, edist_dist] at hω ⊢
    rw [ENNReal.ofReal_le_ofReal_iff dist_nonneg]
    by_contra hd
    rw [not_le] at hd
    have hcontr := hδh hd
    rw [← ENNReal.ofReal_toReal hεlt.ne, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hω
    linarith
  · have hεtop' : ε = ⊤ := top_le_iff.mp hεtop
    have hempty : ∀ n : ℕ, {ω | ε ≤ edist (h (f n ω)) (h c)} = ∅ := fun n => by
      ext ω; simp [hεtop', top_le_iff, edist_ne_top]
    simp only [hempty, measure_empty]
    exact tendsto_const_nhds

end DeepWiki.TimeSeries
