import Mathlib.Probability.Process.FiniteDimensionalLaws
import DeepWiki.MeasureTheory.KolmogorovExtension

/-! # Finite-dimensional distributions and Kolmogorov's existence theorem
§1.2: the finite-dimensional distributions of a stochastic process (Def 1.2.3), the
Kolmogorov consistency conditions they satisfy, and Kolmogorov's existence theorem
(Thm 1.2.1) — every consistent family is realized by the coordinate process on the
projective limit. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℤ → Ω → ℝ}

/-- **Definition 1.2.3**: the finite-dimensional distribution of the process `X` on the
finite index set `I` — the joint law of `(Xₜ)_{t ∈ I}`, i.e. the pushforward
`μ.map (ω ↦ I.restrict (X · ω))`. The book's distribution function
`F_t(x) = P(X_{t₁} ≤ x₁, …, X_{tₙ} ≤ xₙ)` (1.2.7) is the CDF of this law. -/
noncomputable def fdd (X : ℤ → Ω → ℝ) (μ : Measure Ω) (I : Finset ℤ) : Measure (↥I → ℝ) :=
  μ.map (fun ω => I.restrict (fun t => X t ω))

/-- **Definition 1.2.3** in distribution-function form (eq 1.2.7): the distribution function
`F_t(x) = P(X_{t₁} ≤ x₁, …, X_{tₙ} ≤ xₙ)` of `(Xₜ)_{t ∈ I}` — the CDF of the law `fdd`, i.e.
the measure of the lower orthant `{y : yᵢ ≤ xᵢ for all i}`. -/
noncomputable def fddCDF (X : ℤ → Ω → ℝ) (μ : Measure Ω) (I : Finset ℤ) (x : ↥I → ℝ) : ℝ≥0∞ :=
  fdd X μ I (Set.univ.pi fun i => Set.Iic (x i))

/-- The distribution function `F_t(x)` (1.2.7) is the probability of the event
`{Xₜ ≤ xₜ for all t ∈ I}`. -/
theorem fddCDF_eq_measure (hX : ∀ t, Measurable (X t)) (I : Finset ℤ) (x : ↥I → ℝ) :
    fddCDF X μ I x = μ {ω | ∀ i : I, X i ω ≤ x i} := by
  have hmeas : Measurable (fun ω => I.restrict (fun t => X t ω)) :=
    measurable_pi_lambda _ fun i => hX i.1
  rw [fddCDF, fdd, Measure.map_apply hmeas (MeasurableSet.univ_pi fun i => measurableSet_Iic)]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Iic, Set.mem_setOf_eq]
  exact ⟨fun h i => h i, fun h i => h i⟩

/-- The finite-dimensional distributions of a process satisfy Kolmogorov's consistency
conditions (1.2.8): they form a projective measure family. -/
theorem isProjectiveMeasureFamily_fdd (hX : ∀ t, AEMeasurable (X t) μ) :
    IsProjectiveMeasureFamily (α := fun _ : ℤ => ℝ) (fun I => fdd X μ I) :=
  isProjectiveMeasureFamily_map_restrict hX

/-- The law of a process is the projective limit of its finite-dimensional distributions. -/
theorem isProjectiveLimit_fdd (hX : AEMeasurable (fun ω => (X · ω)) μ) :
    IsProjectiveLimit (α := fun _ : ℤ => ℝ) (μ.map (fun ω => (X · ω))) (fun I => fdd X μ I) :=
  isProjectiveLimit_map hX

/-- **Theorem 1.2.1** (Kolmogorov's existence theorem): a family `P` of finite-dimensional
distributions satisfying the consistency conditions (1.2.8) is the finite-dimensional
distribution family of some process — the coordinate process `(t, ω) ↦ ω t` on the
projective-limit probability space `(ℤ → ℝ, projectiveLimit P hP)`. -/
theorem exists_process_fdd_eq (P : ∀ I : Finset ℤ, Measure (↥I → ℝ))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ℤ => ℝ) P) :
    ∃ ν : Measure (ℤ → ℝ), IsProbabilityMeasure ν ∧
      ∀ I, fdd (fun t ω => ω t) ν I = P I := by
  refine ⟨projectiveLimit P hP, isProbabilityMeasure_projectiveLimit hP, fun I => ?_⟩
  exact isProjectiveLimit_projectiveLimit hP I

end DeepWiki.TimeSeries
