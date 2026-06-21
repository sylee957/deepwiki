import DeepWiki.TimeSeries.ArmaProcesses
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

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

open scoped NNReal ENNReal

/-- `z ↦ φ(z)` is complex-differentiable for a real polynomial `φ` — it is a polynomial function
`∑ᵢ φᵢ zⁱ`, differentiated term by term. -/
theorem differentiable_aeval_ofReal (φ : ℝ[X]) :
    Differentiable ℂ (fun z : ℂ => Polynomial.aeval z φ) := by
  simp_rw [Polynomial.aeval_eq_sum_range]
  exact Differentiable.fun_sum fun i _ => (differentiable_pow i).const_smul (φ.coeff i)

/-- A real polynomial `φ` evaluated at `z : ℂ` is the (finite) convergent series `∑ₖ φₖ zᵏ`. -/
theorem hasSum_aeval_smul (φ : ℝ[X]) (z : ℂ) :
    HasSum (fun k => (φ.coeff k : ℝ) • z ^ k) (Polynomial.aeval z φ) := by
  rw [Polynomial.aeval_eq_sum_range]
  refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
  rw [Finset.mem_range, not_lt] at hk
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]

/-- **Causal ⟹ `θ/φ` has a power series on a disk of radius `> 1`:** the rational function `θ/φ` of
a causal ARMA is analytic on a disk of radius `> 1`, represented there by its Cauchy power series
(the `MA(∞)` `ψ`-weights). The object underlying both the summability and the recursion. -/
theorem hasFPowerSeriesOnBall_div_aeval {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) :
    ∃ R : ℝ≥0, 1 < R ∧ HasFPowerSeriesOnBall
      (fun z : ℂ => Polynomial.aeval z θ * (Polynomial.aeval z φ)⁻¹)
      (cauchyPowerSeries (fun z : ℂ => Polynomial.aeval z θ * (Polynomial.aeval z φ)⁻¹) 0 R) 0 R := by
  obtain ⟨r, hr1, hr0⟩ := hφ.exists_radius_gt_one
  obtain ⟨R₀, hR1, hRr⟩ := exists_between hr1
  have hR0 : (0 : ℝ) ≤ R₀ := by linarith
  refine ⟨⟨R₀, hR0⟩, by exact_mod_cast hR1, ?_⟩
  exact ((differentiable_aeval_ofReal θ).differentiableOn.mul
    (DifferentiableOn.inv (differentiable_aeval_ofReal φ).differentiableOn fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact hr0 z (lt_of_le_of_lt hz hRr))).hasFPowerSeriesOnBall
      (show (0 : ℝ≥0) < ⟨R₀, hR0⟩ by exact_mod_cast (by linarith : (0:ℝ) < R₀))

/-- **The `MA(∞)` series representation:** on the disk `‖z‖ < R`, the causal ARMA's `θ(z)/φ(z)`
equals the convergent series `∑ₙ ψₙ zⁿ` of its Cauchy (`ψ`-weight) coefficients. -/
theorem hasSum_coeff_div_aeval {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) :
    ∃ R : ℝ≥0, 1 < R ∧ ∀ z : ℂ, ‖z‖ < (R : ℝ) → HasSum
      (fun n => z ^ n * (cauchyPowerSeries (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹)
        0 R).coeff n) (Polynomial.aeval z θ * (Polynomial.aeval z φ)⁻¹) := by
  obtain ⟨R, hR1, hball⟩ := hasFPowerSeriesOnBall_div_aeval (θ := θ) hφ
  refine ⟨R, hR1, fun z hz => ?_⟩
  have hmem : z ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]; exact_mod_cast hz
  have h := hball.hasSum hmem
  simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] using h

/-- **Causal ⟹ `∑|ψⱼ| < ∞` (analytic `ψ`-weights):** the Cauchy power-series (Taylor) coefficients
of `1/φ` at `0` are absolutely summable. This is the `MA(∞)` weight summability — the analytic
content that the formal `armaPsi = θ/φ` lacked. `1/φ` is analytic on a disk of radius `R > 1`
(`exists_radius_gt_one`), so its power series has radius `> 1` and `summable_norm_mul_pow` at `r = 1`
gives `∑ₙ ‖coeffₙ‖ < ∞`. -/
theorem summable_norm_cauchyPowerSeries_inv_aeval {φ : ℝ[X]} (hφ : IsCausalPoly φ) :
    ∃ R : ℝ≥0, 1 < R ∧ Summable fun n : ℕ =>
      ‖cauchyPowerSeries (fun z : ℂ => (Polynomial.aeval z φ)⁻¹) 0 R n‖ := by
  obtain ⟨r, hr1, hr0⟩ := hφ.exists_radius_gt_one
  obtain ⟨R₀, hR1, hRr⟩ := exists_between hr1
  have hR0 : (0 : ℝ) ≤ R₀ := by linarith
  refine ⟨⟨R₀, hR0⟩, by exact_mod_cast hR1, ?_⟩
  set R : ℝ≥0 := ⟨R₀, hR0⟩ with hRdef
  set g : ℂ → ℂ := fun z => (Polynomial.aeval z φ)⁻¹ with hg
  have hd : DifferentiableOn ℂ g (Metric.closedBall 0 (R : ℝ)) := by
    apply DifferentiableOn.inv (differentiable_aeval_ofReal φ).differentiableOn
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact hr0 z (lt_of_le_of_lt hz hRr)
  have hball := hd.hasFPowerSeriesOnBall (show (0 : ℝ≥0) < R by exact_mod_cast (by linarith : (0:ℝ) < R₀))
  have hrad : ((1 : ℝ≥0) : ℝ≥0∞) < (cauchyPowerSeries g 0 R).radius :=
    lt_of_lt_of_le (by exact_mod_cast hR1) hball.r_le
  simpa using (cauchyPowerSeries g 0 R).summable_norm_mul_pow hrad

/-- **Causal ⟹ `∑|ψⱼ| < ∞` for the full `ARMA(p,q)` weights `ψ = θ/φ`:** the Cauchy (Taylor)
coefficients of `θ(z)/φ(z)` at `0` are absolutely summable. Same argument as the `1/φ` case —
`θ/φ = θ · (1/φ)` is analytic on the zero-free disk of radius `> 1`. -/
theorem summable_norm_cauchyPowerSeries_div_aeval {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) :
    ∃ R : ℝ≥0, 1 < R ∧ Summable fun n : ℕ =>
      ‖cauchyPowerSeries (fun z : ℂ => Polynomial.aeval z θ * (Polynomial.aeval z φ)⁻¹) 0 R n‖ := by
  obtain ⟨r, hr1, hr0⟩ := hφ.exists_radius_gt_one
  obtain ⟨R₀, hR1, hRr⟩ := exists_between hr1
  have hR0 : (0 : ℝ) ≤ R₀ := by linarith
  refine ⟨⟨R₀, hR0⟩, by exact_mod_cast hR1, ?_⟩
  set R : ℝ≥0 := ⟨R₀, hR0⟩ with hRdef
  set g : ℂ → ℂ := fun z => Polynomial.aeval z θ * (Polynomial.aeval z φ)⁻¹ with hg
  have hd : DifferentiableOn ℂ g (Metric.closedBall 0 (R : ℝ)) :=
    (differentiable_aeval_ofReal θ).differentiableOn.mul
      (DifferentiableOn.inv (differentiable_aeval_ofReal φ).differentiableOn fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        exact hr0 z (lt_of_le_of_lt hz hRr))
  have hball := hd.hasFPowerSeriesOnBall (show (0 : ℝ≥0) < R by exact_mod_cast (by linarith : (0:ℝ) < R₀))
  have hrad : ((1 : ℝ≥0) : ℝ≥0∞) < (cauchyPowerSeries g 0 R).radius :=
    lt_of_lt_of_le (by exact_mod_cast hR1) hball.r_le
  simpa using (cauchyPowerSeries g 0 R).summable_norm_mul_pow hrad

end DeepWiki.TimeSeries
