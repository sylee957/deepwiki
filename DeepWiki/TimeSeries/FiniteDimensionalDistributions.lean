import Mathlib.Probability.Process.FiniteDimensionalLaws
import DeepWiki.MeasureTheory.KolmogorovExtension

/-! # Finite-dimensional distributions and Kolmogorov's existence theorem
§1.2: the finite-dimensional distributions of a stochastic process (Def 1.2.3), the
Kolmogorov consistency conditions they satisfy, and Kolmogorov's existence theorem
(Thm 1.2.1) — every consistent family is realized by the coordinate process on the
projective limit. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℤ → Ω → ℝ}

/-- **Definition 1.2.3**: the finite-dimensional distribution of the process `X` on the
finite index set `I` — the joint law of `(Xₜ)_{t ∈ I}`, i.e. the pushforward
`μ.map (ω ↦ I.restrict (X · ω))`. The book's distribution function
`F_t(x) = P(X_{t₁} ≤ x₁, …, X_{tₙ} ≤ xₙ)` (1.2.7) is the CDF of this law. -/
noncomputable def fdd (X : ℤ → Ω → ℝ) (μ : Measure Ω) (I : Finset ℤ) : Measure (↥I → ℝ) :=
  μ.map (fun ω => I.restrict (fun t => X t ω))

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
