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

/-- **§4.3 (Herglotz, forward direction)**: `spectralACVF μ` of a finite spectral measure `μ`
is non-negative definite — `∑ᵢⱼ aᵢ conj(aⱼ) γ(tᵢ − tⱼ) = ∫ |∑ᵢ aᵢ e^{itᵢν}|² dμ ≥ 0`. (The
converse — every non-negative definite function is `spectralACVF` of some `μ` — is the analytic
content of Herglotz's theorem 4.3.1, infra-blocked.) -/
theorem isComplexNonnegDefinite_spectralACVF [IsFiniteMeasure μ] :
    IsComplexNonnegDefinite (spectralACVF μ) := by
  intro n a t
  have hnorm : ∀ (k : ℤ) (ν : ℝ), ‖Complex.exp (Complex.I * (k : ℂ) * (ν : ℂ))‖ = 1 := by
    intro k ν
    rw [show Complex.I * (k : ℂ) * (ν : ℂ) = ((k : ℝ) * ν : ℝ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hint : ∀ i j : Fin n,
      Integrable (fun ν : ℝ =>
        a i * conj (a j) * Complex.exp (Complex.I * ((t i - t j : ℤ) : ℂ) * (ν : ℂ))) μ :=
    fun i j => (Integrable.mono' (integrable_const (1 : ℝ))
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ν => (hnorm (t i - t j) ν).le)).const_mul _
  have hptwise : ∀ ν : ℝ,
      ∑ i, ∑ j, a i * conj (a j) * Complex.exp (Complex.I * ((t i - t j : ℤ) : ℂ) * (ν : ℂ))
        = (Complex.normSq (∑ i, a i * Complex.exp (Complex.I * (t i : ℂ) * (ν : ℂ))) : ℂ) := by
    intro ν
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← Complex.exp_conj,
      show (starRingEnd ℂ) (Complex.I * (t j : ℂ) * (ν : ℂ)) = -(Complex.I * (t j : ℂ) * (ν : ℂ)) by
        rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]; ring,
      show Complex.I * ((t i - t j : ℤ) : ℂ) * (ν : ℂ)
          = Complex.I * (t i : ℂ) * (ν : ℂ) + -(Complex.I * (t j : ℂ) * (ν : ℂ)) by push_cast; ring,
      Complex.exp_add]
    ring
  have key : ∑ i, ∑ j, a i * conj (a j) * spectralACVF μ (t i - t j)
      = ((∫ ν, Complex.normSq (∑ i, a i * Complex.exp (Complex.I * (t i : ℂ) * (ν : ℂ))) ∂μ :
          ℝ) : ℂ) := by
    have e1 : ∑ i, ∑ j, a i * conj (a j) * spectralACVF μ (t i - t j)
        = ∫ ν, ∑ i, ∑ j,
            a i * conj (a j) * Complex.exp (Complex.I * ((t i - t j : ℤ) : ℂ) * (ν : ℂ)) ∂μ := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hint i j]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [spectralACVF, ← integral_const_mul]
    rw [e1]
    simp_rw [hptwise]
    rw [integral_complex_ofReal]
  rw [key]
  exact ⟨by rw [Complex.ofReal_re]; exact integral_nonneg fun ν => Complex.normSq_nonneg _,
    Complex.ofReal_im _⟩

end DeepWiki.TimeSeries
