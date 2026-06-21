import DeepWiki.TimeSeries.SpectralDistribution
import DeepWiki.TimeSeries.SpectralDensity
import DeepWiki.TimeSeries.SpectralDensityFourier
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 4: The Spectral Representation of a Stationary Process
The book numbering lives here in the catalog; the citation (section, page) is in each
docstring, the DOI in `Sources.Doi_10_1007_978_1_4419_0320_4.Source`. Chapter 4 is largely
**spectral-measure and stochastic-integration theory**, most of which is infra-blocked in this
Mathlib (see the per-section notes); the formalized item is the autocovariance determined by a
spectral distribution (eq 4.2.6). -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries

/-! ## §4.1 Complex-Valued Stationary Time Series (pp.114–115)

**Definition 4.1.1** (a complex stationary process: `E|Xₜ|² < ∞` with `EXₜ` and `E(X_{t+h} X̄ₜ)`
independent of `t`), **Definition 4.1.2** (the complex autocovariance
`γ(h) = E(X_{t+h} X̄ₜ) − EX_{t+h} EX̄ₜ`), its properties `γ(0) ≥ 0`, `|γ(h)| ≤ γ(0)`, Hermitian
`γ(−h) = conj γ(h)` (eqs 4.1.3–4.1.5), and **Theorem 4.1.1** (a function is the autocovariance of
a complex stationary process iff it is Hermitian and non-negative definite — the complex
analogue of Theorem 1.5.1, `thm_1_5_1`). This is a parallel `ℂ`-valued reprise of the real Ch1
theory; the forward direction (a complex stationary process has a Hermitian non-negative-definite
autocovariance) is formalizable by building a complex-process layer over `Lp ℂ 2 μ` (future
work), and the converse (existence of a process with a given such autocovariance) needs the
complex Gaussian construction, infra-blocked like the real converse. -/

/-- **§4.1 (eq 4.1.6, the condition in Theorem 4.1.1)**: complex non-negative definiteness of a
function `K : ℤ → ℂ` — `∑ᵢⱼ aᵢ conj(aⱼ) K(tᵢ − tⱼ) ≥ 0` (a non-negative real). The library's
`IsComplexNonnegDefinite`. -/
abbrev eq_4_1_6 := @DeepWiki.TimeSeries.IsComplexNonnegDefinite

/-- **§4.1 (eq 4.1.5)**: the autocovariance `spectralACVF μ` is Hermitian, `γ(−h) = conj γ(h)`.
The library's `spectralACVF_neg`. -/
theorem spectralACVF_hermitian (μ : MeasureTheory.Measure ℝ) (h : ℤ) :
    spectralACVF μ (-h) = (starRingEnd ℂ) (spectralACVF μ h) :=
  spectralACVF_neg μ h

/-- **§4.2–§4.3, eq 4.2.6**: the autocovariance function `γ(h) = ∫ e^{ihν} dμ(ν)` determined by a
spectral distribution `μ` (a finite measure on `(−π, π]`). The library's `spectralACVF`. -/
noncomputable abbrev eq_4_2_6 := @DeepWiki.TimeSeries.spectralACVF

/-- **§4.3 (Theorem 4.3.1, Herglotz — forward direction)**: for a finite spectral measure `μ`,
the autocovariance `spectralACVF μ` is non-negative definite, since
`∑ᵢⱼ aᵢ conj(aⱼ) γ(tᵢ − tⱼ) = ∫ |∑ᵢ aᵢ e^{itᵢν}|² dμ ≥ 0`. The library's
`isComplexNonnegDefinite_spectralACVF`. (The converse is infra-blocked; see the note below.) -/
theorem thm_4_3_1_forward {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasure μ] :
    IsComplexNonnegDefinite (spectralACVF μ) :=
  isComplexNonnegDefinite_spectralACVF

/-- **Theorem 4.3.2** (§4.3, p.120): an absolutely summable `K : ℤ → ℂ` (`∑ₙ |K(n)| < ∞`) is
recovered from its **Fourier-series spectral density** `f(λ) = (1/2π) ∑ₙ e^{−inλ} K(n)` (eq 4.3.7,
`fourierSpectralDensity`) by inversion `K(h) = ∫_{−π}^{π} e^{ihν} f(ν) dν` (eq 4.3.5–4.3.6) — so `f`
is the spectral density of `K`. Used in particular to read off the (rational) spectral density of an
ARMA process. The library's `fourierSpectralDensity_inversion`. -/
alias thm_4_3_2 := DeepWiki.TimeSeries.fourierSpectralDensity_inversion

/-! ## §4.2 The Spectral Distribution (pp.116–117) and §4.3 Herglotz's Theorem (pp.117–118)

The **spectral distribution function** `F` (eq 4.2.4, a right-continuous non-decreasing bounded
function with `F(−π) = 0`, equivalently a finite measure on `(−π, π]`) and the **spectral
density** `f` (when `F(λ) = ∫₋π^λ f`). **Theorem 4.3.1 (Herglotz)**: a function `γ` on `ℤ` is
non-negative definite iff `γ(h) = ∫ e^{ihν} dF(ν)` for a bounded distribution function `F`.

The **forward** direction — a `γ` of the form `eq_4_2_6 = spectralACVF μ` is non-negative
definite — is now FORMALIZED as `thm_4_3_1_forward` above. The **converse** (constructing the
spectral measure `F` from a non-negative definite sequence, via a Fejér-kernel weak limit) needs
a measure-from-positive-definite-sequence theorem (Herglotz/Bochner on the circle) absent in this
Mathlib — infra-blocked.

The **spectral representation of the process itself**, `Xₜ = ∫ e^{itν} dZ(ν)` (eq 4.2.5, a
stochastic integral against an orthogonal-increment process, developed in §4.7), needs `L²`
stochastic-integration infrastructure absent in this Mathlib — infra-blocked. -/

/-! ## §4.4 Spectral Densities and ARMA Processes (pp.122–123)

**Theorem 4.4.1**: a time-invariant linear filter `ψ(B) = ∑ⱼ ψⱼ Bʲ` (`∑|ψⱼ| < ∞`) applied to a
stationary process multiplies its spectral measure by the **power transfer function**
`|ψ(e^{-iλ})|²`, i.e. `f_X(λ) = |∑ⱼ ψⱼ e^{-ijλ}|² f_Y(λ)` (eq 4.4.3). **Theorem 4.4.2**: an
ARMA(p,q) process (no common zeroes, `φ(z) ≠ 0` on `|z| = 1`) has the **rational spectral
density** `f(λ) = (σ²/2π) |θ(e^{-iλ})|² / |φ(e^{-iλ})|²` (eq 4.4.5).

Both proofs run through the `MA(∞)` representation and the spectral representation of the
process (infra-blocked). The spectral-density **formula** itself is the algebraic
`armaSpectralDensity` below, with its non-negativity and the white-noise case (`φ = θ = 1`,
constant `σ²/2π`), and **Example 4.4.1** (the MA(1) density `(σ²/2π)(1 + 2θ₁cos λ + θ₁²)`) all
proved. -/

/-- **§4.4, Theorem 4.4.2 (eq 4.4.5)**: the rational spectral density of an ARMA(p,q) process,
`f(λ) = (σ²/2π) · |θ(e^{-iλ})|² / |φ(e^{-iλ})|²`. The library's `armaSpectralDensity` (with
`armaSpectralDensity_nonneg` and `armaSpectralDensity_one_one`, the white-noise constant). -/
noncomputable abbrev thm_4_4_2 := @DeepWiki.TimeSeries.armaSpectralDensity

/-- **Example 4.4.1** (§4.4, p.123): the spectral density of an `MA(1)` process
`Xₜ = Zₜ + θ₁Zₜ₋₁` (`φ = 1`, `θ = 1 + θ₁z`) is `(σ²/2π)(1 + 2θ₁ cos λ + θ₁²)`. The library's
`armaSpectralDensity_ma1`. -/
theorem ex_4_4_1 (θ1 σ2 lam : ℝ) :
    armaSpectralDensity 1 (1 + Polynomial.C θ1 * Polynomial.X) σ2 lam
      = σ2 / (2 * Real.pi) * (1 + 2 * θ1 * Real.cos lam + θ1 ^ 2) :=
  armaSpectralDensity_ma1 θ1 σ2 lam

/-- **Example 4.4.2** (§4.4, p.125): the spectral density of an `AR(1)` process
`Xₜ = φ₁Xₜ₋₁ + Zₜ` (`φ = 1 − φ₁z`, `θ = 1`) is `(σ²/2π) / (1 − 2φ₁ cos λ + φ₁²)`. The library's
`armaSpectralDensity_ar1`. -/
theorem ex_4_4_2 (φ1 σ2 lam : ℝ) :
    armaSpectralDensity (1 - Polynomial.C φ1 * Polynomial.X) 1 σ2 lam
      = σ2 / (2 * Real.pi) / (1 - 2 * φ1 * Real.cos lam + φ1 ^ 2) :=
  armaSpectralDensity_ar1 φ1 σ2 lam

end DeepWiki.Ts
