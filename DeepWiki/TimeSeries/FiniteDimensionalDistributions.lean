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
set `T` (the book's `T ⊆ ℝ`). It is a function of a tuple of times `t : ι → T` and an argument
`x : ι → ℝ`, equal to the lower-orthant probability `P(Xₜᵢ ≤ xᵢ for all i)`. The book's
finite-dimensional distribution uses the ordered `n`-tuple `ι = Fin n` (`t = (t₁ < ⋯ < tₙ) ∈ Tⁿ`,
the set `𝒯`); taking `ι = ↥I` for a `Finset I` instead gives the CDF of the joint law `fdd`
(`fdd_apply_Iic_eq_distFn`). -/
noncomputable def distFn {T Ω : Type*} [MeasurableSpace Ω] (X : T → Ω → ℝ) (μ : Measure Ω)
    {ι : Type*} (t : ι → T) (x : ι → ℝ) : ℝ≥0∞ :=
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

/-! ### `distFn` (distribution-function form) versus `fdd` (joint-law form)
Both are the finite-dimensional distribution of Definition 1.2.3: `distFn` is the distribution
**function** `F_t(x)` (a lower-orthant probability) for a tuple of times, while `fdd` is the
joint **law** of `(Xₜ)_{t∈I}` for a finite index set `I` (the object Kolmogorov's theorem is
stated on). Since `distFn`'s index is arbitrary, `fdd`'s lower-orthant CDF is *literally*
`distFn` over `ι = ↥I` (`fdd_apply_Iic_eq_distFn`); each is the orthant CDF of a pushforward
`ω ↦ (Xₜ(ω))ₜ`. -/

/-- `distFn` is the lower-orthant CDF of the joint law `μ.map (ω ↦ (X_{tᵢ}(ω))ᵢ)` of the tuple
`(X_{tᵢ})ᵢ` — exhibiting the distribution function as the CDF of a finite-dimensional law, the
same kind of object as `fdd`. -/
theorem distFn_eq_map_Iic {T ι : Type*} [Fintype ι] (X : T → Ω → ℝ) {t : ι → T}
    (hX : ∀ i, Measurable (X (t i))) (x : ι → ℝ) :
    distFn X μ t x
      = (μ.map fun ω => fun i => X (t i) ω) (Set.univ.pi fun i => Set.Iic (x i)) := by
  rw [distFn, Measure.map_apply (measurable_pi_lambda _ hX)
      (MeasurableSet.univ_pi fun _ => measurableSet_Iic)]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Iic, Set.mem_setOf_eq]

/-- The lower-orthant CDF of the joint law `fdd X μ I` is the distribution-function value
`P(Xₜ ≤ xₜ for all t ∈ I)` — i.e. `distFn` (Def 1.2.3) is exactly the CDF of `fdd`, here in the
`Finset`-indexed form `x : ↥I → ℝ`. -/
theorem fdd_Iic (hX : ∀ t, Measurable (X t)) (I : Finset ℤ) (x : ↥I → ℝ) :
    fdd X μ I (Set.univ.pi fun i => Set.Iic (x i)) = μ {ω | ∀ i : ↥I, X i ω ≤ x i} := by
  have hmeas : Measurable (fun ω => I.restrict (fun t => X t ω)) :=
    measurable_pi_lambda _ fun i => hX i.1
  rw [fdd, Measure.map_apply hmeas (MeasurableSet.univ_pi fun _ => measurableSet_Iic)]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Iic, Set.mem_setOf_eq]
  exact ⟨fun h i => h i, fun h i => h i⟩

/-- **`fdd` is the joint law whose CDF is `distFn`**: the lower-orthant value of `fdd X μ I` is
exactly `distFn` over the index `ι = ↥I` with the inclusion tuple `(Subtype.val : ↥I → ℤ)`. So
the book's distribution function (Def 1.2.3, `distFn`) is literally the CDF of the
finite-dimensional law `fdd`. -/
theorem fdd_apply_Iic_eq_distFn (hX : ∀ t, Measurable (X t)) (I : Finset ℤ) (x : ↥I → ℝ) :
    fdd X μ I (Set.univ.pi fun i => Set.Iic (x i)) = distFn X μ (Subtype.val) x := by
  rw [fdd_Iic hX]
  rfl

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
