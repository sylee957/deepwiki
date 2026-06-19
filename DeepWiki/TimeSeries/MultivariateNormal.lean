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

/-- The linear transform `Y = a + B·X` of a random vector `X` (`a : Fin m → ℝ`,
`B : Matrix (Fin m) (Fin n) ℝ`): `Yᵢ = aᵢ + ∑ₖ Bᵢₖ Xₖ`. -/
noncomputable def linTransform {m n : ℕ} (a : Fin m → ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) : Fin m → Ω → ℝ := fun i ω => a i + ∑ k, B i k * X k ω

/-- **Proposition 1.6.1** (mean, 1.6.4): `E(a + B·X) = a + B·(EX)`. -/
theorem meanVector_linTransform [IsProbabilityMeasure μ] {m n : ℕ} (a : Fin m → ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) {X : Fin n → Ω → ℝ} (hX : ∀ k, Integrable (X k) μ) :
    meanVector (linTransform a B X) μ = a + B *ᵥ meanVector X μ := by
  funext i
  have hint : ∀ k, Integrable (fun ω => B i k * X k ω) μ := fun k => (hX k).const_mul _
  have hrhs : (a + B *ᵥ meanVector X μ) i = a i + ∑ k, B i k * meanVector X μ k := by
    simp [Matrix.mulVec, dotProduct]
  rw [hrhs]
  have hconst : ∫ _ : Ω, a i ∂μ = a i := by simp
  show ∫ ω, (a i + ∑ k, B i k * X k ω) ∂μ = a i + ∑ k, B i k * meanVector X μ k
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun k _ => hint k), hconst,
    integral_finsetSum _ fun k _ => hint k]
  simp only [integral_const_mul, meanVector]

/-- **Proposition 1.6.1** (covariance, 1.6.5): `Cov(a + B·X) = B · Σ_XX · Bᵀ`. -/
theorem covMatrix_linTransform [IsProbabilityMeasure μ] {m n : ℕ} (a : Fin m → ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) {X : Fin n → Ω → ℝ} (hX : ∀ k, MemLp (X k) 2 μ) :
    covMatrix (linTransform a B X) μ = B * covMatrix X μ * Bᵀ := by
  have hmem : ∀ (c : ℝ) (k : Fin n), MemLp (fun ω => c * X k ω) 2 μ := fun c k => (hX k).const_mul c
  have hint : ∀ (c : ℝ) (k : Fin n), Integrable (fun ω => c * X k ω) μ :=
    fun c k => (hmem c k).integrable (by norm_num)
  ext i j
  simp only [covMatrix_apply]
  show cov[fun ω => a i + ∑ k, B i k * X k ω, fun ω => a j + ∑ l, B j l * X l ω; μ]
      = (B * covMatrix X μ * Bᵀ) i j
  rw [covariance_const_add_left (integrable_finsetSum _ fun k _ => hint (B i k) k),
    covariance_const_add_right (integrable_finsetSum _ fun l _ => hint (B j l) l),
    covariance_fun_sum_fun_sum (fun k => hmem (B i k) k) (fun l => hmem (B j l) l)]
  have hmat : (B * covMatrix X μ * Bᵀ) i j = ∑ k, ∑ l, B i k * B j l * cov[X k, X l; μ] := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, covMatrix_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hmat]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]; ring

end DeepWiki.TimeSeries
