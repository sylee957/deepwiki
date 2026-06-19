import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-! # The spectral distribution and the autocovariance (§4.2–§4.3)
The autocovariance function determined by a spectral distribution: `γ(h) = ∫ e^{ihν} dμ(ν)`
(eq 4.2.6). By Herglotz's theorem (4.3.1) every non-negative definite function on `ℤ` arises
this way from a unique finite spectral measure `μ` on `(-π, π]`; the converse construction (the
spectral measure from a non-negative definite sequence) and the spectral representation of the
process itself, `Xₜ = ∫ e^{itν} dZ(ν)` (4.2.5, a stochastic integral against an
orthogonal-increment process), need measure- and stochastic-integration infrastructure not
present here. -/

namespace DeepWiki.TimeSeries

open MeasureTheory

/-- **§4.2–§4.3 (eq 4.2.6)**: the autocovariance function `γ(h) = ∫ e^{ihν} dμ(ν)` determined
by a spectral distribution `μ` (a finite measure on `(-π, π]`). Herglotz's theorem (4.3.1) is
the statement that a function on `ℤ` is non-negative definite iff it has this form for some
finite measure `μ`. -/
noncomputable def spectralACVF (μ : Measure ℝ) (h : ℤ) : ℂ :=
  ∫ ν, Complex.exp (Complex.I * h * ν) ∂μ

end DeepWiki.TimeSeries
