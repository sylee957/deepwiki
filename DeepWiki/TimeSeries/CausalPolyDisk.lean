import DeepWiki.TimeSeries.ArmaProcesses
import DeepWiki.TimeSeries.ArmaPsiWeights
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
    ∃ R : ℝ≥0, 1 < R ∧ (∀ z : ℂ, ‖z‖ < (R : ℝ) → Polynomial.aeval z φ ≠ 0) ∧
      HasFPowerSeriesOnBall
      (fun z : ℂ => Polynomial.aeval z θ * (Polynomial.aeval z φ)⁻¹)
      (cauchyPowerSeries (fun z : ℂ => Polynomial.aeval z θ * (Polynomial.aeval z φ)⁻¹) 0 R) 0 R := by
  obtain ⟨r, hr1, hr0⟩ := hφ.exists_radius_gt_one
  obtain ⟨R₀, hR1, hRr⟩ := exists_between hr1
  have hR0 : (0 : ℝ) ≤ R₀ := by linarith
  refine ⟨⟨R₀, hR0⟩, by exact_mod_cast hR1, fun z hz => hr0 z (lt_trans hz hRr), ?_⟩
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
  obtain ⟨R, hR1, _, hball⟩ := hasFPowerSeriesOnBall_div_aeval (θ := θ) hφ
  refine ⟨R, hR1, fun z hz => ?_⟩
  have hmem : z ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]; exact_mod_cast hz
  have h := hball.hasSum hmem
  simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] using h

/-- **The Cauchy product `φ·(θ/φ) = θ`:** on the disk, `θ(z) = ∑ₘ ∑_{i+j=m} φᵢ zⁱ · (zʲ ψⱼ)` — the
product of the polynomial `φ(z) = ∑φₖzᵏ` and the series `θ/φ = ∑ψₙzⁿ`, via the `tsum` Cauchy
product. The coefficient form of this is the `ψ`-weight recursion. -/
theorem aeval_eq_tsum_cauchy {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) :
    ∃ R : ℝ≥0, 1 < R ∧ ∀ z : ℂ, ‖z‖ < (R : ℝ) →
      Polynomial.aeval z θ = ∑' m : ℕ, ∑ q ∈ Finset.antidiagonal m,
        ((φ.coeff q.1 : ℝ) • z ^ q.1) * (z ^ q.2 *
          (cauchyPowerSeries (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R).coeff q.2) := by
  obtain ⟨R, hR1, hne, hball⟩ := hasFPowerSeriesOnBall_div_aeval (θ := θ) hφ
  refine ⟨R, hR1, fun z hz => ?_⟩
  set p := cauchyPowerSeries (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R with hp
  have hmem : z ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]; exact_mod_cast hz
  have hg : HasSum (fun n => z ^ n * p.coeff n) (Polynomial.aeval z θ * (Polynomial.aeval z φ)⁻¹) := by
    simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] using
      hball.hasSum hmem
  have hf : HasSum (fun k => (φ.coeff k : ℝ) • z ^ k) (Polynomial.aeval z φ) := hasSum_aeval_smul φ z
  have hsumf : Summable (fun k => ‖(φ.coeff k : ℝ) • z ^ k‖) :=
    summable_of_ne_finset_zero (s := Finset.range (φ.natDegree + 1)) fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul, norm_zero]
  have hrad : (‖z‖₊ : ℝ≥0∞) < p.radius := lt_of_lt_of_le (by exact_mod_cast hz) hball.r_le
  have hcoeff_le : ∀ n, ‖p.coeff n‖ ≤ ‖p n‖ := fun n => by
    have h := (p n).le_opNorm (1 : Fin n → ℂ)
    simp only [Pi.one_apply, norm_one, Finset.prod_const_one, mul_one] at h
    exact h
  have hsumg : Summable (fun n => ‖z ^ n * p.coeff n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (p.summable_norm_mul_pow hrad)
    rw [norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hcoeff_le n) (by positivity)
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsumf hsumg
  rw [hf.tsum_eq, hg.tsum_eq] at hcauchy
  rw [← hcauchy, mul_comm (Polynomial.aeval z θ) (Polynomial.aeval z φ)⁻¹,
    mul_inv_cancel_left₀ (hne z hz)]

/-- **`θ(z) = ∑ₘ z^m c_m`** with `c_m = ∑_{i+j=m} φᵢ ψⱼ`: factoring `z^m` out of the Cauchy product.
The coefficient sequence `c` is the `φ`-convolution of the `ψ`-weights. -/
theorem aeval_eq_tsum_zpow_conv {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) :
    ∃ R : ℝ≥0, 1 < R ∧ ∀ z : ℂ, ‖z‖ < (R : ℝ) →
      Polynomial.aeval z θ = ∑' m : ℕ, z ^ m * ∑ q ∈ Finset.antidiagonal m,
        (φ.coeff q.1 : ℝ) • (cauchyPowerSeries
          (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R).coeff q.2 := by
  obtain ⟨R, hR1, hcauchy⟩ := aeval_eq_tsum_cauchy (θ := θ) hφ
  refine ⟨R, hR1, fun z hz => ?_⟩
  rw [hcauchy z hz]
  refine tsum_congr fun m => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_antidiagonal] at hq
  rw [smul_mul_assoc, ← mul_assoc, ← pow_add, hq, mul_smul_comm]

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

/-- The `m`-th antidiagonal term of the Cauchy product `φ(z) · (∑ ψⱼ zʲ)` factors as `cₘ · zᵐ`,
with `cₘ = ∑_{i+j=m} φᵢ ψⱼ`: `∑_{i+j=m} (φᵢ zⁱ)(zʲ ψⱼ) = (∑_{i+j=m} φᵢ ψⱼ) zᵐ`. -/
theorem antidiagonal_term_eq (φ : ℝ[X]) (ψ : ℕ → ℂ) (z : ℂ) (m : ℕ) :
    (∑ q ∈ Finset.antidiagonal m, ((φ.coeff q.1 : ℝ) • z ^ q.1) * (z ^ q.2 * ψ q.2))
      = (∑ q ∈ Finset.antidiagonal m, (φ.coeff q.1 : ℝ) • ψ q.2) • z ^ m := by
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_antidiagonal] at hq
  rw [← hq]
  simp only [Complex.real_smul, smul_eq_mul, pow_add]
  ring

/-- **Package a uniformly-convergent scalar power series as a `HasFPowerSeriesAt`:** if the scalar
series `∑ₙ aₙ zⁿ` converges to `θ(z)` on the disk `‖z‖ < ρ` and `∑ₙ ‖aₙ‖ ρⁿ < ∞`, then `ofScalars ℂ a`
is the power-series expansion of `z ↦ θ(z)` at `0`. The bridge from a bare `HasSum` to the
formal-multilinear-series machinery (radius from `le_radius_of_summable`, terms from
`ofScalars_apply_eq`). -/
theorem hasFPowerSeriesAt_ofScalars_aeval (θ : ℝ[X]) (a : ℕ → ℂ) (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hsum : Summable fun n => ‖a n‖ * (ρ : ℝ) ^ n)
    (hhs : ∀ z : ℂ, ‖z‖ < (ρ : ℝ) → HasSum (fun n => a n • z ^ n) (Polynomial.aeval z θ)) :
    HasFPowerSeriesAt (fun z : ℂ => Polynomial.aeval z θ)
      (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
  refine ⟨ρ, { r_le := ?_, r_pos := by exact_mod_cast hρ, hasSum := ?_ }⟩
  · refine FormalMultilinearSeries.le_radius_of_summable _ (hsum.congr fun n => ?_)
    rw [FormalMultilinearSeries.ofScalars_norm]
  · intro y hy
    rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe] at hy
    have hy' : ‖y‖ < (ρ : ℝ) := by exact_mod_cast hy
    simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq] using hhs y hy'

/-- **`θ(z) = ∑ₘ cₘ zᵐ` as a power-series expansion** (`cₘ = ∑_{i+j=m} φᵢ ψⱼ`, the `φ`-convolution
of the `MA(∞)` weights): the Cauchy product `φ · (θ/φ)` is the power series of `z ↦ θ(z)` at `0`. The
analytic carrier of the `ψ`-weight recursion: its coefficient uniqueness gives eq (3.3.3). -/
theorem hasFPowerSeriesAt_conv_div {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) :
    ∃ R : ℝ≥0, 1 < R ∧ Summable (fun n : ℕ => ‖(cauchyPowerSeries
        (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R).coeff n‖) ∧
      HasFPowerSeriesAt (fun z : ℂ => Polynomial.aeval z θ)
      (FormalMultilinearSeries.ofScalars ℂ (fun m : ℕ => ∑ q ∈ Finset.antidiagonal m,
        (φ.coeff q.1 : ℝ) • (cauchyPowerSeries
          (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R).coeff q.2)) 0 := by
  obtain ⟨R, hR1, hne, hball⟩ := hasFPowerSeriesOnBall_div_aeval (θ := θ) hφ
  set p := cauchyPowerSeries (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R with hp
  set cseq : ℕ → ℂ := fun m => ∑ q ∈ Finset.antidiagonal m, (φ.coeff q.1 : ℝ) • p.coeff q.2 with hcseq
  have hcoeff_le : ∀ n, ‖p.coeff n‖ ≤ ‖p n‖ := fun n => by
    have h := (p n).le_opNorm (1 : Fin n → ℂ)
    simp only [Pi.one_apply, norm_one, Finset.prod_const_one, mul_one] at h
    exact h
  have hsum_coeff : Summable (fun n => ‖p.coeff n‖) := by
    have hrad1 : ((1 : ℝ≥0) : ℝ≥0∞) < p.radius := lt_of_lt_of_le (by exact_mod_cast hR1) hball.r_le
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoeff_le ?_
    simpa using p.summable_norm_mul_pow hrad1
  -- the Cauchy product converges to `θ(z)` on the whole disk `‖z‖ < R`
  have hconv : ∀ z : ℂ, ‖z‖ < (R : ℝ) → HasSum (fun m : ℕ => cseq m • z ^ m)
      (Polynomial.aeval z θ) := by
    intro z hz
    have hmem : z ∈ Metric.eball (0 : ℂ) R := by
      rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]; exact_mod_cast hz
    have hg : HasSum (fun n => z ^ n * p.coeff n)
        (Polynomial.aeval z θ * (Polynomial.aeval z φ)⁻¹) := by
      simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] using
        hball.hasSum hmem
    have hf : HasSum (fun k => (φ.coeff k : ℝ) • z ^ k) (Polynomial.aeval z φ) :=
      hasSum_aeval_smul φ z
    have hfn : Summable (fun k => ‖(φ.coeff k : ℝ) • z ^ k‖) :=
      summable_of_ne_finset_zero (s := Finset.range (φ.natDegree + 1)) fun k hk => by
        rw [Finset.mem_range, not_lt] at hk
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul, norm_zero]
    have hrad : (‖z‖₊ : ℝ≥0∞) < p.radius := lt_of_lt_of_le (by exact_mod_cast hz) hball.r_le
    have hgn : Summable (fun n => ‖z ^ n * p.coeff n‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
        (p.summable_norm_mul_pow hrad)
      rw [norm_mul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right (hcoeff_le n) (by positivity)
    have hsummable :=
      summable_sum_mul_antidiagonal_of_summable_norm' hfn hf.summable hgn hg.summable
    have hval : ∑' m, ∑ q ∈ Finset.antidiagonal m,
        ((φ.coeff q.1 : ℝ) • z ^ q.1) * (z ^ q.2 * p.coeff q.2) = Polynomial.aeval z θ := by
      rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn, hf.tsum_eq, hg.tsum_eq,
        mul_comm (Polynomial.aeval z θ), mul_inv_cancel_left₀ (hne z hz)]
    have hterm : (fun m => ∑ q ∈ Finset.antidiagonal m,
        ((φ.coeff q.1 : ℝ) • z ^ q.1) * (z ^ q.2 * p.coeff q.2)) = fun m => cseq m • z ^ m :=
      funext fun m => antidiagonal_term_eq φ p.coeff z m
    rw [hterm] at hsummable hval
    rw [← hval]; exact hsummable.hasSum
  -- choose `1 < ρ < R`; the convolution norms are summable at radius `ρ`, giving radius `≥ ρ > 0`
  obtain ⟨ρ, hρ1, hρR⟩ := exists_between hR1
  have hρ0 : (0 : ℝ≥0) < ρ := lt_trans (by norm_num) hρ1
  have hzr : ‖((ρ : ℝ) : ℂ)‖ = (ρ : ℝ) := by simp [abs_of_nonneg ρ.coe_nonneg]
  have hBsum : Summable (fun n => ‖cseq n‖ * (ρ : ℝ) ^ n) := by
    have hF : Summable (fun k => ‖(φ.coeff k : ℝ) • ((ρ : ℝ) : ℂ) ^ k‖) :=
      summable_of_ne_finset_zero (s := Finset.range (φ.natDegree + 1)) fun k hk => by
        rw [Finset.mem_range, not_lt] at hk
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul, norm_zero]
    have hradρ : (‖((ρ : ℝ) : ℂ)‖₊ : ℝ≥0∞) < p.radius := by
      refine lt_of_lt_of_le ?_ hball.r_le
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, hzr]
      exact_mod_cast hρR
    have hG : Summable (fun k => ‖((ρ : ℝ) : ℂ) ^ k * p.coeff k‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
        (p.summable_norm_mul_pow hradρ)
      rw [norm_mul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right (hcoeff_le n) (by positivity)
    refine (summable_norm_sum_mul_antidiagonal_of_summable_norm hF hG).congr fun n => ?_
    rw [antidiagonal_term_eq φ p.coeff ((ρ : ℝ) : ℂ) n, norm_smul, norm_pow, hzr]
  exact ⟨R, hR1, hsum_coeff, hasFPowerSeriesAt_ofScalars_aeval θ cseq ρ hρ0 hBsum
    (fun z hz => hconv z (lt_trans hz (by exact_mod_cast hρR)))⟩

/-- **The `ψ`-weight recursion, coefficient form (eq 3.3.3):** the Cauchy convolution of the AR
coefficients `φₖ` with the `MA(∞)` weights `ψⱼ` (the Taylor coefficients of `θ/φ`) reproduces the MA
coefficients — `∑_{i+j=m} φᵢ ψⱼ = θ_m` for every `m` — by the uniqueness of power-series
coefficients applied to `φ(z) · (θ(z)/φ(z)) = θ(z)`. In particular `∑_{i+j=m} φᵢ ψⱼ = 0` for
`m > deg θ`. -/
theorem conv_coeff_div_eq_coeff {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) :
    ∃ R : ℝ≥0, 1 < R ∧ Summable (fun n : ℕ => ‖(cauchyPowerSeries
        (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R).coeff n‖) ∧
      ∀ m : ℕ,
      (∑ q ∈ Finset.antidiagonal m, (φ.coeff q.1 : ℝ) • (cauchyPowerSeries
        (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R).coeff q.2)
      = (θ.coeff m : ℂ) := by
  obtain ⟨R, hR1, hsum, hB⟩ := hasFPowerSeriesAt_conv_div (θ := θ) hφ
  refine ⟨R, hR1, hsum, fun m => ?_⟩
  have hA : HasFPowerSeriesAt (fun z : ℂ => Polynomial.aeval z θ)
      (FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ => (θ.coeff n : ℂ))) 0 := by
    refine hasFPowerSeriesAt_ofScalars_aeval θ (fun n => (θ.coeff n : ℂ)) 1 one_pos ?_ (fun z _ => ?_)
    · refine summable_of_ne_finset_zero (s := Finset.range (θ.natDegree + 1)) fun k hk => ?_
      rw [Finset.mem_range, not_lt] at hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
    · have heq : (fun n => (θ.coeff n : ℂ) • z ^ n) = fun n => (θ.coeff n : ℝ) • z ^ n := by
        funext n; simp only [Complex.real_smul, smul_eq_mul]
      rw [heq]; exact hasSum_aeval_smul θ z
  exact congrFun (FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (hB.eq_formalMultilinearSeries hA)) m

/-- **Invertible ⟹ `∑ⱼ |πⱼ| < ∞` (AR(∞) weights)** (Thm 3.1.2 / Def 3.1.4 analytic content): for an
*invertible* ARMA — `θ(z) ≠ 0` on `|z| ≤ 1` (`IsInvertiblePoly`) — the `AR(∞)` weights `πⱼ` (the Taylor
coefficients of `φ(z)/θ(z)`) are absolutely summable. The same zero-free-disk estimate as causality,
with `φ, θ` swapped: `IsInvertiblePoly θ` is definitionally the same `≠ 0 on |z| ≤ 1` condition as
`IsCausalPoly θ`, so this is `summable_norm_cauchyPowerSeries_div_aeval` applied to `φ/θ`. -/
theorem summable_norm_cauchyPowerSeries_arInv {φ θ : ℝ[X]} (hθ : IsInvertiblePoly θ) :
    ∃ R : ℝ≥0, 1 < R ∧ Summable fun n : ℕ =>
      ‖cauchyPowerSeries (fun z : ℂ => Polynomial.aeval z φ * (Polynomial.aeval z θ)⁻¹) 0 R n‖ :=
  summable_norm_cauchyPowerSeries_div_aeval (φ := θ) (θ := φ) hθ

/-- **The `AR(∞)` weight recursion `∑_{i+j=m} θᵢ πⱼ = φ_m`** (the `θ · (φ/θ) = φ` coefficient identity):
for an invertible ARMA, the `AR(∞)` weights `πⱼ` (Taylor coefficients of `φ/θ`) reproduce `φ` under
Cauchy convolution with `θ`. The invertibility dual of `conv_coeff_div_eq_coeff` (roles of `φ, θ`
swapped). -/
theorem conv_coeff_arInv_eq_coeff {φ θ : ℝ[X]} (hθ : IsInvertiblePoly θ) :
    ∃ R : ℝ≥0, 1 < R ∧ Summable (fun n : ℕ => ‖(cauchyPowerSeries
        (fun w : ℂ => Polynomial.aeval w φ * (Polynomial.aeval w θ)⁻¹) 0 R).coeff n‖) ∧
      ∀ m : ℕ,
      (∑ q ∈ Finset.antidiagonal m, (θ.coeff q.1 : ℝ) • (cauchyPowerSeries
        (fun w : ℂ => Polynomial.aeval w φ * (Polynomial.aeval w θ)⁻¹) 0 R).coeff q.2)
      = (φ.coeff m : ℂ) :=
  conv_coeff_div_eq_coeff (φ := θ) (θ := φ) hθ

/-- **The analytic `MA(∞)` weights ARE the formal `θ/φ` weights** (eq 3.3.2 bridge): for a causal
ARMA, the Taylor coefficients of `θ(z)/φ(z)` equal the coefficients of the formal power series
`armaPsi φ θ = (↑φ)⁻¹ ↑θ` (cast `ℝ → ℂ`) — in particular they are *real*. By uniqueness of the
solution of `↑φ · ψ = ↑θ` in the integral domain `ℂ⟦X⟧` (`↑φ ≠ 0`, since `φ(0) ≠ 0` for a causal
`φ`): both the analytic `ψ`-weights and the formal `armaPsi` solve it, so they agree. -/
theorem cauchyCoeff_div_aeval_eq_armaPsi {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) :
    ∃ R : ℝ≥0, 1 < R ∧ Summable (fun n : ℕ => ‖(cauchyPowerSeries
        (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R).coeff n‖) ∧ ∀ n : ℕ,
      (cauchyPowerSeries (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R).coeff n
      = ((PowerSeries.coeff n (armaPsi φ θ) : ℝ) : ℂ) := by
  obtain ⟨R, hR1, hsum, hrec⟩ := conv_coeff_div_eq_coeff (φ := φ) (θ := θ) hφ
  refine ⟨R, hR1, hsum, fun n => ?_⟩
  set p := cauchyPowerSeries (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R
    with hp
  have hφ0 : PowerSeries.constantCoeff (φ : PowerSeries ℝ) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe]
    exact fun h0 => hφ 0 (by simp)
      (by rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero, h0, map_zero])
  set F : PowerSeries ℝ →+* PowerSeries ℂ := PowerSeries.map Complex.ofRealHom with hF
  set Q : PowerSeries ℂ := PowerSeries.mk fun k => p.coeff k with hQ
  -- `Q` solves `↑φ · Q = ↑θ` (the analytic recursion), as does `F (armaPsi)` (the formal identity)
  have hmulQ : F (φ : PowerSeries ℝ) * Q = F (θ : PowerSeries ℝ) := by
    ext m
    simp only [hF, hQ, PowerSeries.coeff_mul, PowerSeries.coeff_map, Polynomial.coeff_coe,
      PowerSeries.coeff_mk, Complex.ofRealHom_eq_coe]
    rw [← hrec m]
    exact Finset.sum_congr rfl fun q _ => by rw [Complex.real_smul]
  have hmulψ : F (φ : PowerSeries ℝ) * F (armaPsi φ θ) = F (θ : PowerSeries ℝ) := by
    rw [← map_mul, coe_mul_armaPsi hφ0]
  have hφF : F (φ : PowerSeries ℝ) ≠ 0 := by
    intro h
    apply hφ0
    have h0 := congrArg (PowerSeries.coeff 0) h
    rw [hF, PowerSeries.coeff_map, map_zero, Complex.ofRealHom_eq_coe] at h0
    rw [Polynomial.constantCoeff_coe]
    exact_mod_cast h0
  have hcoeff := congrArg (PowerSeries.coeff n) (mul_left_cancel₀ hφF (hmulQ.trans hmulψ.symm))
  rwa [hQ, PowerSeries.coeff_mk, hF, PowerSeries.coeff_map, Complex.ofRealHom_eq_coe] at hcoeff

/-- **The genuine `MA(∞)` weights `ψ = θ/φ` are absolutely summable** (Example 3.2.3, formal form):
for a causal ARMA, the coefficients of the formal power series `armaPsi φ θ = (↑φ)⁻¹ ↑θ` satisfy
`∑ⱼ |ψⱼ| < ∞`. This is the analytic `∑ⱼ |ψⱼ| < ∞` (`summable_norm_cauchyPowerSeries_div_aeval`)
transported to the *formal* weights via the realness bridge `cauchyCoeff_div_aeval_eq_armaPsi`
(`|ψⱼ| = ‖(θ/φ)-Taylor-coeffⱼ‖`). -/
theorem summable_armaPsi_coeff {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) :
    Summable (fun n : ℕ => PowerSeries.coeff n (armaPsi φ θ)) := by
  obtain ⟨R, hR1, hsum, heq⟩ := cauchyCoeff_div_aeval_eq_armaPsi (φ := φ) (θ := θ) hφ
  refine Summable.of_norm_bounded hsum fun n => le_of_eq ?_
  rw [heq n, Complex.norm_real]

end DeepWiki.TimeSeries
