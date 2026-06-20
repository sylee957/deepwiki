import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import DeepWiki.MeasureTheory.KolmogorovExtension

/-! # Finite-dimensional distributions and Kolmogorov's existence theorem
§1.2: the finite-dimensional distributions of a stochastic process (Def 1.2.3), the
Kolmogorov consistency conditions they satisfy, and Kolmogorov's existence theorem
(Thm 1.2.1) — every consistent family is realized by the coordinate process on the
projective limit. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Type*} {X : T → Ω → ℝ}

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
`μ.map (ω ↦ I.restrict (X · ω))`, the joint distribution of `(Xₜ)_{t ∈ I}`, over an arbitrary
index set `T` (the book's `T ⊆ ℝ`; the time series specializes to `T = ℤ`). This is the
measure-valued reformulation of the distribution functions `distFn` (Def 1.2.3), and the object
on which Kolmogorov's existence theorem `exists_process_fdd_eq` (Thm 1.2.1) is stated. -/
noncomputable def fdd {T : Type*} (X : T → Ω → ℝ) (μ : Measure Ω) (I : Finset T) :
    Measure (↥I → ℝ) :=
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
theorem fdd_Iic (hX : ∀ t, Measurable (X t)) (I : Finset T) (x : ↥I → ℝ) :
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
theorem fdd_apply_Iic_eq_distFn (hX : ∀ t, Measurable (X t)) (I : Finset T) (x : ↥I → ℝ) :
    fdd X μ I (Set.univ.pi fun i => Set.Iic (x i)) = distFn X μ (Subtype.val) x := by
  rw [fdd_Iic hX]
  rfl

/-- **Theorem 1.2.1 (Kolmogorov), consistency direction, in the book's exact notation (eq
1.2.8)**: the distribution functions of a process are **consistent** — letting the `i`-th
argument tend to `+∞` recovers the distribution function with the `i`-th coordinate deleted,
`lim_{xᵢ → ∞} F_t(x) = F_{t(i)}(x(i))`, with `t(i)`, `x(i)` (`Fin.removeNth i`) the time- and
argument-tuples with their `i`-th component removed. Sending the threshold `xᵢ` to `+∞` drops the
constraint `X_{tᵢ} ≤ xᵢ`, and continuity from below of `μ` yields the marginal. This is the
distribution-**function** form of the projective consistency `isProjectiveMeasureFamily_fdd`;
together with the existence theorem `exists_process_fdd_eq` it is the full equivalence (1.2.8) of
Theorem 1.2.1. -/
theorem distFn_tendsto_marginal {T : Type*} (X : T → Ω → ℝ) {n : ℕ} (t : Fin (n + 1) → T)
    (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Filter.Tendsto (fun c => distFn X μ t (Function.update x i c)) Filter.atTop
      (nhds (distFn X μ (i.removeNth t) (i.removeNth x))) := by
  have key : ⋃ c : ℝ, {ω | ∀ j, X (t j) ω ≤ Function.update x i c j}
      = {ω | ∀ j, X (i.removeNth t j) ω ≤ i.removeNth x j} := by
    ext ω
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨c, hc⟩ j
      have hcj := hc (i.succAbove j)
      rwa [Function.update_of_ne (Fin.succAbove_ne i j)] at hcj
    · intro h
      refine ⟨X (t i) ω, fun j => ?_⟩
      rcases eq_or_ne j i with rfl | hj
      · simp
      · rw [Function.update_of_ne hj]
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        exact h k
  have hmono : Monotone fun c : ℝ => {ω | ∀ j, X (t j) ω ≤ Function.update x i c j} := by
    intro c c' hcc' ω hω j
    refine (hω j).trans ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using hcc'
    · simp [Function.update_of_ne hj]
  simpa only [distFn, key, Function.comp_def] using tendsto_measure_iUnion_atTop (μ := μ) hmono

/-! ### Characteristic-function form of the consistency condition (1.2.9) -/

/-- **Equation (1.2.9)** setup: the characteristic function
`φ_t(u) = ∫_{ℝⁿ} e^{i u'x} F_t(dx)` of the finite-dimensional distribution at the times `t`,
written as the equivalent integral `∫ exp(i ∑ⱼ uⱼ X_{tⱼ}(ω)) dμ` over `(Ω, μ)` — the
characteristic function of the joint law of `(X_{tⱼ})`. -/
noncomputable def charFunFdd {T Ω : Type*} [MeasurableSpace Ω] (X : T → Ω → ℝ) (μ : Measure Ω)
    {n : ℕ} (t : Fin n → T) (u : Fin n → ℝ) : ℂ :=
  ∫ ω, Complex.exp (((∑ j, u j * X (t j) ω : ℝ) : ℂ) * Complex.I) ∂μ

/-- Zeroing the `i`-th frequency marginalizes the characteristic function:
`φ_t(u)|_{uᵢ = 0} = φ_{t(i)}(u(i))` — the `i`-th summand drops out of the exponent
(`t(i)`, `u(i)` are `Fin.removeNth i`). -/
theorem charFunFdd_update_zero {T : Type*} (X : T → Ω → ℝ) {n : ℕ} (t : Fin (n + 1) → T)
    (u : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    charFunFdd X μ t (Function.update u i 0) = charFunFdd X μ (i.removeNth t) (i.removeNth u) := by
  simp only [charFunFdd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hsum : (∑ j, Function.update u i 0 j * X (t j) ω)
      = ∑ j, i.removeNth u j * X (i.removeNth t j) ω := by
    rw [Fin.sum_univ_succAbove (fun j => Function.update u i 0 j * X (t j) ω) i]
    simp only [Function.update_self, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Function.update_of_ne (Fin.succAbove_ne i j), Fin.removeNth_apply, Fin.removeNth_apply]
  simp only [hsum]

/-- **Equation (1.2.9)**: the characteristic functions of a process are **consistent** — letting
the `i`-th frequency `uᵢ → 0` recovers the characteristic function with the `i`-th time deleted,
`lim_{uᵢ → 0} φ_t(u) = φ_{t(i)}(u(i))`. This is the characteristic-function form of the
distribution-function consistency `distFn_tendsto_marginal`; together they are the two equivalent
statements of the consistency condition of Theorem 1.2.1. -/
theorem charFunFdd_tendsto_marginal [IsFiniteMeasure μ] {T : Type*} (X : T → Ω → ℝ)
    (hX : ∀ s, Measurable (X s)) {n : ℕ} (t : Fin (n + 1) → T) (u : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    Filter.Tendsto (fun c => charFunFdd X μ t (Function.update u i c)) (nhds 0)
      (nhds (charFunFdd X μ (i.removeNth t) (i.removeNth u))) := by
  rw [← charFunFdd_update_zero X t u i]
  have hcont : Continuous fun c : ℝ => charFunFdd X μ t (Function.update u i c) := by
    unfold charFunFdd
    refine continuous_of_dominated (bound := fun _ => 1) (fun c => ?_) (fun c => ?_)
      (integrable_const 1) (Filter.Eventually.of_forall fun ω => ?_)
    · exact (Complex.continuous_exp.measurable.comp
        ((Complex.measurable_ofReal.comp
          (Finset.measurable_sum _ fun j _ => measurable_const.mul (hX (t j)))).mul
            measurable_const)).aestronglyMeasurable
    · filter_upwards with ω
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
    · refine Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
      refine continuous_finsetSum _ fun j _ =>
        (?_ : Continuous fun c => Function.update u i c j).mul continuous_const
      rcases eq_or_ne j i with rfl | hj
      · simpa only [Function.update_self] using continuous_id'
      · simpa only [Function.update_of_ne hj] using continuous_const
  exact hcont.tendsto 0

/-- The finite-dimensional distributions of a process satisfy Kolmogorov's consistency
conditions (1.2.8): they form a projective measure family. -/
theorem isProjectiveMeasureFamily_fdd (hX : ∀ t, AEMeasurable (X t) μ) :
    IsProjectiveMeasureFamily (α := fun _ : T => ℝ) (fun I => fdd X μ I) :=
  isProjectiveMeasureFamily_map_restrict hX

/-- The law of a process is the projective limit of its finite-dimensional distributions. -/
theorem isProjectiveLimit_fdd (hX : AEMeasurable (fun ω => (X · ω)) μ) :
    IsProjectiveLimit (α := fun _ : T => ℝ) (μ.map (fun ω => (X · ω))) (fun I => fdd X μ I) :=
  isProjectiveLimit_map hX

/-- **Theorem 1.2.1** (Kolmogorov's existence theorem): a family `P` of finite-dimensional
distributions satisfying the consistency conditions (1.2.8) is the finite-dimensional
distribution family of some process — the coordinate process `(t, ω) ↦ ω t` on the
projective-limit probability space `(T → ℝ, projectiveLimit P hP)`. The index set `T` is
arbitrary (`Nonempty`): the book's `T ⊆ ℝ` and the time series' `T = ℤ` are both instances. -/
theorem exists_process_fdd_eq {T : Type*} [Nonempty T] (P : ∀ I : Finset T, Measure (↥I → ℝ))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : T => ℝ) P) :
    ∃ ν : Measure (T → ℝ), IsProbabilityMeasure ν ∧
      ∀ I, fdd (fun t ω => ω t) ν I = P I := by
  refine ⟨projectiveLimit P hP, isProbabilityMeasure_projectiveLimit hP, fun I => ?_⟩
  exact isProjectiveLimit_projectiveLimit hP I

end DeepWiki.TimeSeries
