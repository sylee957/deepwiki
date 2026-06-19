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

/-- **Definition 1.2.3** (eq 1.2.7), book form: the finite-dimensional distribution function
`F_t(x) = P(X_{t₁} ≤ x₁, …, X_{tₙ} ≤ xₙ)` of a process `X : T → Ω → ℝ` over an arbitrary index
set `T` (the book's `T ⊆ ℝ`; instantiates to `ℝ`, `ℤ`, …). It is a function of an `n`-tuple of
times `t = (t₁, …, tₙ)` (`t : Fin n → T`, the book's `t ∈ Tⁿ`) and an argument
`x = (x₁, …, xₙ) ∈ ℝⁿ` (`x : Fin n → ℝ`), equal to the probability of the lower-orthant event
`{ω | Xₜᵢ(ω) ≤ xᵢ for all i}`. The book indexes the family by the strictly increasing tuples
`t₁ < ⋯ < tₙ` (the set `𝒯`); the value `F_t(x)` is well-defined for any tuple. -/
noncomputable def distFn {T Ω : Type*} [MeasurableSpace Ω] (X : T → Ω → ℝ) (μ : Measure Ω)
    {n : ℕ} (t : Fin n → T) (x : Fin n → ℝ) : ℝ≥0∞ :=
  μ {ω | ∀ i, X (t i) ω ≤ x i}

-- **Equation (1.2.7)** holds by definition: `F_t(x) = P(X_{t₁} ≤ x₁, …, X_{tₙ} ≤ xₙ)`.
example {T : Type*} (X : T → Ω → ℝ) {n : ℕ} (t : Fin n → T) (x : Fin n → ℝ) :
    distFn X μ t x = μ {ω | ∀ i, X (t i) ω ≤ x i} := rfl

/-- The finite-dimensional (joint) **law** of `X` on a finite index set `I` — the pushforward
`μ.map (ω ↦ I.restrict (X · ω))`, the joint distribution of `(Xₜ)_{t ∈ I}`. This is the
measure-valued reformulation of the distribution functions `distFn` (Def 1.2.3), and the object
on which Kolmogorov's existence theorem `exists_process_fdd_eq` (Thm 1.2.1) is stated. -/
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
