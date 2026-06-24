import DeepWiki.TimeSeries.MDependentCLT
import DeepWiki.TimeSeries.MultivariateCLT

/-! # Toward the multivariate m-dependent CLT
The scalar projections `⟪Yₜ, λ⟫` of a vector `m`-dependent process inherit `m`-dependence
(`IsMDependent.comp`) and strict stationarity (`IsStrictlyStationary.comp`); their long-run variance is
the quadratic form `λ ⬝ᵥ S λ` of the long-run cross-covariance matrix (`covariance_inner_inner` summed
over lags). Here: the cross-covariance of coordinate blocks vanishes beyond the dependence range, the
finite-support fact giving summability of the cross-covariances. -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Cross-covariance of coordinates vanishes beyond the dependence range:** for a vector `m`-dependent
process `Y`, `cov[Yₜⁱ, Yₛʲ] = 0` whenever `s + m < t` — the blocks `Y s`, `Y t` are independent, hence so
are their coordinate projections. The finite-support fact giving summability of the cross-covariances feeding
the multivariate m-dependent CLT. -/
theorem covariance_component_eq_zero_of_mDependent {d m : ℕ} [IsFiniteMeasure μ]
    {Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)} (h : IsMDependent m Y μ)
    (hmem : ∀ t i, MemLp (fun ω => Y t ω i) 2 μ) {s t : ℤ} (hst : s + (m : ℤ) < t) (i j : Fin d) :
    cov[fun ω => Y t ω i, fun ω => Y s ω j; μ] = 0 := by
  have hindep : IndepFun (Y s) (Y t) μ := h.indepFun hst
  have hjmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v j) := by fun_prop
  have himeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v i) := by fun_prop
  rw [covariance_comm]
  exact (hindep.comp hjmeas himeas).covariance_eq_zero (hmem s j) (hmem t i)

/-- **The cross-covariances of a vector `m`-dependent process are summable over lags:** each
`k ↦ cov[Yₖⁱ, Y₀ʲ]` has finite support (it vanishes for `|k| > m` by
`covariance_component_eq_zero_of_mDependent`), hence is summable. The long-run cross-covariance
`Sᵢⱼ = ∑'ₖ cov[Yₖⁱ, Y₀ʲ]` is therefore well-defined — the entries of the limiting covariance matrix. -/
theorem summable_covariance_component_of_mDependent {d m : ℕ} [IsFiniteMeasure μ]
    {Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)} (h : IsMDependent m Y μ)
    (hmem : ∀ t i, MemLp (fun ω => Y t ω i) 2 μ) (i j : Fin d) :
    Summable fun k => cov[fun ω => Y k ω i, fun ω => Y 0 ω j; μ] := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(m : ℤ)) m) fun k hk => ?_
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  rcases hk with hlt | hgt
  · rw [covariance_comm]
    exact covariance_component_eq_zero_of_mDependent h hmem (by omega : k + (m : ℤ) < 0) j i
  · exact covariance_component_eq_zero_of_mDependent h hmem (by omega : (0 : ℤ) + m < k) i j

/-- **Variance identification:** the long-run variance of a projected vector `m`-dependent process is the
quadratic form of the long-run cross-covariance matrix —
`∑'ₖ acvf⟪Y,λ⟫(k) = ∑ᵢ ∑ⱼ λᵢ λⱼ (∑'ₖ cov[Yₖⁱ, Y₀ʲ])`. Each lag's autocovariance expands bilinearly
(`covariance_inner_inner`) and the lag-sum commutes with the finite coordinate sums (`tsum_sum`, justified
by `summable_covariance_component_of_mDependent`). This is the variance feeding the Cramér–Wold lift: it
equals `λ ⬝ᵥ S λ` with `Sᵢⱼ = ∑'ₖ cov[Yₖⁱ, Y₀ʲ]`. -/
theorem tsum_acvfStat_inner_eq {d m : ℕ} [IsFiniteMeasure μ]
    {Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)} (h : IsMDependent m Y μ)
    (hmem : ∀ t i, MemLp (fun ω => Y t ω i) 2 μ) (lam : EuclideanSpace ℝ (Fin d)) :
    ∑' k, acvfStat (fun t ω => (⟪Y t ω, lam⟫ : ℝ)) μ k
      = ∑ i, ∑ j, lam i * lam j * ∑' k, cov[fun ω => Y k ω i, fun ω => Y 0 ω j; μ] := by
  have hbil : ∀ k, acvfStat (fun t ω => (⟪Y t ω, lam⟫ : ℝ)) μ k
      = ∑ i, ∑ j, lam i * lam j * cov[fun ω => Y k ω i, fun ω => Y 0 ω j; μ] := fun k => by
    rw [acvfStat_apply]; exact covariance_inner_inner lam (fun i => hmem k i) fun j => hmem 0 j
  simp_rw [hbil]
  rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ =>
    (summable_covariance_component_of_mDependent h hmem i j).mul_left _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum fun j _ =>
    (summable_covariance_component_of_mDependent h hmem i j).mul_left _]
  exact Finset.sum_congr rfl fun j _ => tsum_mul_left

/-- **A matrix quadratic form as a double sum:** `v ⬝ᵥ S v = ∑ᵢ ∑ⱼ vᵢ vⱼ Sᵢⱼ`. -/
theorem dotProduct_mulVec_eq_quadratic {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ S *ᵥ v = ∑ i, ∑ j, v i * v j * S i j := by
  rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The long-run cross-covariance matrix** of a vector process: `Sᵢⱼ = ∑'ₖ cov[Yₖⁱ, Y₀ʲ]`. For a
vector `m`-dependent process its quadratic forms are the long-run variances of the projections
(`longRunCovMatrix_quadratic`); it is the covariance matrix of the limiting Gaussian. -/
noncomputable def longRunCovMatrix {d : ℕ} (Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑' k, cov[fun ω => Y k ω i, fun ω => Y 0 ω j; μ]

/-- **The quadratic form of the long-run covariance matrix is the long-run variance of the projection:**
`λ ⬝ᵥ S λ = ∑'ₖ acvf⟪Y,λ⟫(k)` where `S = longRunCovMatrix Y μ`. Combines the matrix quadratic-form
expansion with the variance identification `tsum_acvfStat_inner_eq`. -/
theorem longRunCovMatrix_quadratic {d m : ℕ} [IsFiniteMeasure μ]
    {Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)} (h : IsMDependent m Y μ)
    (hmem : ∀ t i, MemLp (fun ω => Y t ω i) 2 μ) (lam : EuclideanSpace ℝ (Fin d)) :
    lam ⬝ᵥ longRunCovMatrix Y μ *ᵥ lam = ∑' k, acvfStat (fun t ω => (⟪Y t ω, lam⟫ : ℝ)) μ k := by
  rw [dotProduct_mulVec_eq_quadratic, tsum_acvfStat_inner_eq h hmem]
  rfl

end DeepWiki.TimeSeries
