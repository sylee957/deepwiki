import DeepWiki.TimeSeries.MultivariateCLT

/-! # Asymptotic normality (Brockwell–Davis §6.4)
A real sequence `Xₙ` is **asymptotically normal** `AN(aₙ, bₙ²)` if the standardized `(Xₙ − aₙ)/bₙ`
converges in distribution to the standard normal. Equivalently (Lévy's continuity theorem) the
characteristic function of the standardized sequence converges pointwise to that of `N(0,1)`; this
characteristic-function form is taken as the definition, so the predicate is self-contained (no
reference Gaussian variable). The library's `TendstoInDistribution`-form central limit theorems feed it
through `IsAsymptoticallyNormal.of_tendstoInDistribution`. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Asymptotic normality** `AN(aₙ, bₙ²)`: the characteristic function of the standardized sequence
`(Xₙ − aₙ)/bₙ` converges pointwise to that of `N(0,1)`. -/
def IsAsymptoticallyNormal (X : ℕ → Ω → ℝ) (a b : ℕ → ℝ) (μ : Measure Ω) : Prop :=
  ∀ s : ℝ, Tendsto (fun n => charFun (μ.map fun ω => (X n ω - a n) / b n) s) atTop
    (𝓝 (charFun (gaussianReal 0 1) s))

/-- **Convergence in distribution of the standardized sequence to `N(0,1)` gives asymptotic normality**:
the bridge from the library's `TendstoInDistribution`-form CLTs to the `AN` predicate (Lévy's continuity
theorem, `ProbabilityMeasure.tendsto_iff_tendsto_charFun`). -/
theorem IsAsymptoticallyNormal.of_tendstoInDistribution [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    {a b : ℕ → ℝ} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {G : Ω' → ℝ} (hG : HasLaw G (gaussianReal 0 1) P')
    (h : TendstoInDistribution (fun n ω => (X n ω - a n) / b n) atTop G (fun _ => μ) P') :
    IsAsymptoticallyNormal X a b μ := by
  intro s
  rw [← hG.map_eq]
  exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp h.tendsto s

end DeepWiki.TimeSeries
