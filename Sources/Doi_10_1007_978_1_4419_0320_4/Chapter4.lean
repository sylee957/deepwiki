import DeepWiki.TimeSeries.SpectralDistribution
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

/-! ## §4.2 The Spectral Distribution (pp.116–117) and §4.3 Herglotz's Theorem (pp.117–118)

The **spectral distribution function** `F` (eq 4.2.4, a right-continuous non-decreasing bounded
function with `F(−π) = 0`, equivalently a finite measure on `(−π, π]`) and the **spectral
density** `f` (when `F(λ) = ∫₋π^λ f`). **Theorem 4.3.1 (Herglotz)**: a function `γ` on `ℤ` is
non-negative definite iff `γ(h) = ∫ e^{ihν} dF(ν)` for a bounded distribution function `F`.

The **forward** direction — a `γ` of the form `eq_4_2_6 = spectralACVF μ` is non-negative
definite, since `∑ⱼₖ aⱼ conj(aₖ) γ(j − k) = ∫ |∑ⱼ aⱼ e^{ijν}|² dμ ≥ 0` — is formalizable from
`spectralACVF` and is the cleanly-doable next nugget. The **converse** (constructing the spectral
measure `F` from a non-negative definite sequence, via a Fejér-kernel weak limit) needs a
measure-from-positive-definite-sequence theorem (Herglotz/Bochner on the circle) absent in this
Mathlib — infra-blocked.

The **spectral representation of the process itself**, `Xₜ = ∫ e^{itν} dZ(ν)` (eq 4.2.5, a
stochastic integral against an orthogonal-increment process, developed in §4.7), needs `L²`
stochastic-integration infrastructure absent in this Mathlib — infra-blocked. -/

end DeepWiki.Ts
