import DeepWiki.TimeSeries.MDependentCLT

/-! # Moving-average processes are m-dependent (Brockwell–Davis §6.4, Examples 6.4.3–6.4.4)
An MA(q) process `Xₜ = ∑_{j=0}^q θⱼ Z_{t−j}` driven by i.i.d. noise is `q`-dependent: two blocks of the
series separated by more than `q` time steps depend on disjoint noise windows, hence are independent.
Combined with the m-dependent central limit theorem this yields the asymptotic normality of `X̄ₙ` for
finite moving averages. This file builds the process and its structural properties; the `q`-dependence
and the resulting CLT follow. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **MA(q) process** `Xₜ = ∑_{j=0}^q θⱼ Z_{t−j}` driven by the noise `Z`. -/
noncomputable def movingAverage (θ : ℕ → ℝ) (q : ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range (q + 1), θ j * Z (t - j) ω

omit [MeasurableSpace Ω] in
/-- Pointwise value of the MA(q) process. -/
@[simp] theorem movingAverage_apply (θ : ℕ → ℝ) (q : ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    movingAverage θ q Z t ω = ∑ j ∈ Finset.range (q + 1), θ j * Z (t - j) ω := rfl

/-- The MA(q) process is measurable when the noise is. -/
theorem measurable_movingAverage {θ : ℕ → ℝ} {q : ℕ} {Z : ℤ → Ω → ℝ} (hZ : ∀ t, Measurable (Z t))
    (t : ℤ) : Measurable (movingAverage θ q Z t) :=
  Finset.measurable_sum _ fun _ _ => (hZ _).const_mul _

/-- The MA(q) process is `L²` when the noise is. -/
theorem memLp_movingAverage {θ : ℕ → ℝ} {q : ℕ} {Z : ℤ → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ) (t : ℤ) :
    MemLp (movingAverage θ q Z t) 2 μ :=
  memLp_finsetSum _ fun _ _ => (hZ _).const_mul _

/-- The MA(q) process is centered when the noise is. -/
theorem integral_movingAverage [IsProbabilityMeasure μ] {θ : ℕ → ℝ} {q : ℕ} {Z : ℤ → Ω → ℝ}
    (hZmem : ∀ t, MemLp (Z t) 2 μ) (hZc : ∀ t, μ[Z t] = 0) (t : ℤ) :
    μ[movingAverage θ q Z t] = 0 := by
  simp only [movingAverage]
  rw [integral_finsetSum _ fun _ _ => ((hZmem _).const_mul _).integrable one_le_two]
  simp [integral_const_mul, hZc]

end DeepWiki.TimeSeries
