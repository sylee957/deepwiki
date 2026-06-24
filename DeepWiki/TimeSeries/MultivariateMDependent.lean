import DeepWiki.TimeSeries.MDependentCLT
import DeepWiki.TimeSeries.MultivariateCLT

/-! # Toward the multivariate m-dependent CLT
The scalar projections `⟪Yₜ, λ⟫` of a vector `m`-dependent process inherit `m`-dependence
(`IsMDependent.comp`) and strict stationarity (`IsStrictlyStationary.comp`); their long-run variance is
the quadratic form `λ ⬝ᵥ S λ` of the long-run cross-covariance matrix (`covariance_inner_inner` summed
over lags). Here: the cross-covariance of coordinate blocks vanishes beyond the dependence range, the
finite-support fact giving summability of the cross-covariances. -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

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

end DeepWiki.TimeSeries
