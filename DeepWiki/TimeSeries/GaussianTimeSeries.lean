import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

/-! # Gaussian time series (Def 1.3.4)
A Gaussian time series is a process all of whose finite-dimensional distributions
are multivariate normal — Mathlib's `IsGaussianProcess`, whose defining condition is
that every finite marginal `(X t)_{t ∈ I}` has a Gaussian law. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Definition 1.3.4**: `X` is a Gaussian time series if all of its
finite-dimensional distributions are multivariate normal. Unfolds to Mathlib's
`IsGaussianProcess`. -/
def IsGaussianTimeSeries (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop := IsGaussianProcess X μ

end DeepWiki.TimeSeries
