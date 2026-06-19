import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! # The mean vector and covariance matrix of a random vector (§1.6)
The mean vector `EX` (1.6.1) and covariance matrix `Σ_XX = [Cov(Xᵢ,Xⱼ)]` (1.6.2) of a
random vector `X = (X₁,…,Xₙ)`, and **Proposition 1.6.2**: the covariance matrix is
symmetric and positive semidefinite. The multivariate normal distribution itself
(Definition 1.6.1) is Mathlib's `ProbabilityTheory.multivariateGaussian`. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Equation (1.6.1)**: the mean vector `EX = (EX₁, …, EXₙ)ᵀ` of a random vector
`X = (X₁, …, Xₙ)`. -/
noncomputable def meanVector {n : ℕ} (X : Fin n → Ω → ℝ) (μ : Measure Ω) : Fin n → ℝ :=
  fun i => ∫ ω, X i ω ∂μ

/-- **Equation (1.6.2)**: the covariance matrix `Σ_XX = [Cov(Xᵢ, Xⱼ)]` of a random
vector `X = (X₁, …, Xₙ)`. -/
noncomputable def covMatrix {n : ℕ} (X : Fin n → Ω → ℝ) (μ : Measure Ω) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => cov[X i, X j; μ]

@[simp] theorem covMatrix_apply {n : ℕ} (X : Fin n → Ω → ℝ) (μ : Measure Ω) (i j : Fin n) :
    covMatrix X μ i j = cov[X i, X j; μ] := rfl

/-- The covariance matrix is Hermitian (over `ℝ`, symmetric): `Cov(Xⱼ,Xᵢ) = Cov(Xᵢ,Xⱼ)`. -/
theorem covMatrix_isHermitian {n : ℕ} (X : Fin n → Ω → ℝ) (μ : Measure Ω) :
    (covMatrix X μ).IsHermitian := by
  show (covMatrix X μ)ᴴ = covMatrix X μ
  ext i j
  simp only [Matrix.conjTranspose_apply, covMatrix_apply, star_trivial]
  exact covariance_comm (X j) (X i)

/-- **Proposition 1.6.2**: the covariance matrix of a square-integrable random vector is
symmetric and positive semidefinite — `bᵀ Σ b = Var(∑ᵢ bᵢ Xᵢ) ≥ 0`. -/
theorem posSemidef_covMatrix [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) : (covMatrix X μ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨covMatrix_isHermitian X μ, fun b => ?_⟩
  set Y : Fin n → Ω → ℝ := fun i ω => b i * X i ω with hYdef
  have hYmem : ∀ i, MemLp (Y i) 2 μ := fun i => (hX i).const_mul (b i)
  have hSmem : MemLp (fun ω => ∑ i, Y i ω) 2 μ := memLp_finsetSum _ fun i _ => hYmem i
  have key : star b ⬝ᵥ (covMatrix X μ *ᵥ b) = ∑ i, ∑ j, b i * b j * cov[X i, X j; μ] := by
    simp only [dotProduct, mulVec, covMatrix_apply, star_trivial, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  have hcov : ∑ i, ∑ j, b i * b j * cov[X i, X j; μ]
      = cov[fun ω => ∑ i, Y i ω, fun ω => ∑ j, Y j ω; μ] := by
    rw [covariance_fun_sum_fun_sum hYmem hYmem]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hYdef]
    rw [covariance_const_mul_left, covariance_const_mul_right]; ring
  rw [hcov, covariance_self hSmem.aestronglyMeasurable.aemeasurable]
  exact variance_nonneg _ _

end DeepWiki.TimeSeries
