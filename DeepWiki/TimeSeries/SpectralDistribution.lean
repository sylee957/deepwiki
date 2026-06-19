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

open MeasureTheory ComplexConjugate

/-- **§4.2–§4.3 (eq 4.2.6)**: the autocovariance function `γ(h) = ∫ e^{ihν} dμ(ν)` determined
by a spectral distribution `μ` (a finite measure on `(-π, π]`). Herglotz's theorem (4.3.1) is
the statement that a function on `ℤ` is non-negative definite iff it has this form for some
finite measure `μ`. -/
noncomputable def spectralACVF (μ : Measure ℝ) (h : ℤ) : ℂ :=
  ∫ ν, Complex.exp (Complex.I * h * ν) ∂μ

/-- **§4.1 (Theorem 4.1.1)**: a complex function `K : ℤ → ℂ` is **non-negative definite** — the
complex analogue of `IsNonnegDefinite` — when `∑ᵢⱼ aᵢ conj(aⱼ) K(tᵢ − tⱼ)` is a non-negative
real for every finite family of complex coefficients `a` and integer times `t`. -/
def IsComplexNonnegDefinite (K : ℤ → ℂ) : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℂ) (t : Fin n → ℤ),
    0 ≤ (∑ i, ∑ j, a i * conj (a j) * K (t i - t j)).re ∧
      (∑ i, ∑ j, a i * conj (a j) * K (t i - t j)).im = 0

/-- `spectralACVF` is **Hermitian** (eq 4.1.5): `γ(−h) = conj γ(h)`, since
`conj e^{ihν} = e^{-ihν}`. -/
theorem spectralACVF_neg (μ : Measure ℝ) (h : ℤ) :
    spectralACVF μ (-h) = conj (spectralACVF μ h) := by
  rw [spectralACVF, spectralACVF, ← integral_conj]
  congr 1
  ext ν
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
  push_cast
  ring

end DeepWiki.TimeSeries
