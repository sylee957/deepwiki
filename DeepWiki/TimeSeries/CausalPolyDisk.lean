import DeepWiki.TimeSeries.ArmaProcesses
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Causal AR polynomials are zero-free on a disk of radius `> 1`
The analytic foundation for the `MA(∞)` representation: if `φ(z) ≠ 0` on the closed unit disk
(`IsCausalPoly`), then by compactness `φ` is zero-free on an open disk of radius `r > 1`, so `1/φ`
is analytic there and its Taylor (`ψ`-weight) coefficients decay geometrically (`∑ⱼ |ψⱼ| < ∞`). This
file proves the radius step; the coefficient-summability is the remaining analytic wiring. -/

namespace DeepWiki.TimeSeries

open scoped Polynomial

/-- **Causality ⟹ a strictly larger zero-free disk:** if `φ(z) ≠ 0` for all `‖z‖ ≤ 1`, then there is
a radius `r > 1` with `φ(z) ≠ 0` for all `‖z‖ < r` — by compactness of the closed unit disk inside
the open zero-free set. -/
theorem IsCausalPoly.exists_radius_gt_one {φ : ℝ[X]} (hφ : IsCausalPoly φ) :
    ∃ r : ℝ, 1 < r ∧ ∀ z : ℂ, ‖z‖ < r → Polynomial.aeval z φ ≠ 0 := by
  have hopen : IsOpen {z : ℂ | Polynomial.aeval z φ ≠ 0} :=
    (isClosed_eq (Polynomial.continuous_aeval φ) continuous_const).isOpen_compl
  have hsub : Metric.closedBall (0 : ℂ) 1 ⊆ {z | Polynomial.aeval z φ ≠ 0} := fun z hz =>
    hφ z (by rwa [Metric.mem_closedBall, dist_zero_right] at hz)
  obtain ⟨δ, hδ, hsubthick⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hopen hsub
  refine ⟨1 + δ, by linarith, fun z hz => hsubthick ?_⟩
  rw [Metric.mem_thickening_iff]
  rcases le_or_gt ‖z‖ 1 with h | h
  · exact ⟨z, by rwa [Metric.mem_closedBall, dist_zero_right], by rwa [dist_self]⟩
  · refine ⟨(1 / ‖z‖ : ℝ) • z, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity), one_div, inv_mul_cancel₀ (by positivity)]
    · have hzy : z - (1 / ‖z‖ : ℝ) • z = (1 - 1 / ‖z‖ : ℝ) • z := by rw [sub_smul, one_smul]
      rw [dist_eq_norm, hzy, norm_smul, Real.norm_eq_abs, abs_of_pos (by
        have : (1 : ℝ) / ‖z‖ < 1 := by rw [div_lt_one (by positivity)]; exact h
        linarith), sub_mul, one_mul, one_div, inv_mul_cancel₀ (by positivity)]
      linarith

end DeepWiki.TimeSeries
