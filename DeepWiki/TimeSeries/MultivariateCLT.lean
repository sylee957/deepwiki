import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Multivariate central limit theorem (foundation)
Building the multivariate CLT for iid random vectors via the Cramér–Wold device: the characteristic
function of a measure on a finite-dimensional inner product space, evaluated at `t`, equals the
characteristic function of the *one-dimensional projection* `⟪·, t⟫` at `1` (`charFun_proj`). This
reduces multivariate charFun convergence to Mathlib's univariate CLT, and Lévy's continuity theorem
(`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) then gives convergence in distribution. The
foundational enabler for Bartlett's formula (Thm 7.2.1/7.2.2) and the Ch10–13 multivariate theory. -/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology RealInnerProductSpace ENNReal

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Characteristic function via one-dimensional projection:** for `X : Ω → E` into a real inner
product space, the characteristic function of the law of `X` at `t` equals that of the law of the
scalar projection `⟪X ·, t⟫` at `1` — both are `∫ exp(I⟪X ω, t⟫) dμ`. The bridge that reduces
multivariate characteristic functions to univariate ones (the Cramér–Wold device). -/
theorem charFun_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] {X : Ω → E} (hX : AEMeasurable X μ) (t : E) :
    charFun (μ.map X) t = charFun (μ.map fun ω => (⟪X ω, t⟫ : ℝ)) 1 := by
  rw [charFun_apply, charFun_apply, integral_map hX (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp [RCLike.inner_apply]

end DeepWiki.TimeSeries
