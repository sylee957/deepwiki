import DeepWiki.TimeSeries.LagPolynomials
import DeepWiki.TimeSeries.ArmaProcesses
import Mathlib.Tactic

/-! # ARIMA and seasonal ARIMA (SARIMA) processes
The differencing and seasonal-differencing polynomials, the seasonal lag operator
`Φ(Bˢ)`, and the ARIMA(p,d,q) (§9.1) and SARIMA(p,d,q)(P,D,Q)ₛ (§9.6) processes.
The headline structural fact — **SARIMA is an ARMA model with a factored
autoregressive polynomial** — is the multiplicativity of lag polynomials
(`lagPoly_mul`): the full seasonal operator `φ(B)·Φ(Bˢ)·(1−B)ᵈ·(1−Bˢ)ᴰ` collapses
to the single lag polynomial `(φ · Φ(zˢ) · (1−z)ᵈ · (1−zˢ)ᴰ)(B)`. -/

namespace DeepWiki.TimeSeries

open Polynomial

/-! ## Differencing and seasonal polynomials -/

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- The differencing polynomial `(1 − z)ᵈ`, whose lag operator is `∇ᵈ = (1 − B)ᵈ`. -/
noncomputable def diffPoly (d : ℕ) : K[X] := (1 - X) ^ d

/-- The seasonal differencing polynomial `(1 − z)ᵈ (1 − zˢ)ᴰ`, whose lag operator is
`(1 − B)ᵈ (1 − Bˢ)ᴰ`. -/
noncomputable def seasonalDiffPoly (d D s : ℕ) : K[X] := (1 - X) ^ d * (1 - X ^ s) ^ D

/-- The seasonal lag operator `Φ(Bˢ)`: the seasonal polynomial `Φ` evaluated at the
seasonal backshift `Bˢ`. -/
noncomputable def seasonalLagPoly (Φ : K[X]) (s : ℕ) : Module.End K (ℤ → M) :=
  lagPoly (Φ.comp (X ^ s))

/-- The combined SARIMA autoregressive/differencing polynomial
`φ(z) · Φ(zˢ) · (1 − z)ᵈ · (1 − zˢ)ᴰ`. -/
noncomputable def sarimaArPoly (φ Φ : K[X]) (d D s : ℕ) : K[X] :=
  φ * Φ.comp (X ^ s) * seasonalDiffPoly d D s

/-- The combined SARIMA moving-average polynomial `θ(z) · Θ(zˢ)`. -/
noncomputable def sarimaMaPoly (θ Θ : K[X]) (s : ℕ) : K[X] := θ * Θ.comp (X ^ s)

/-- **SARIMA is a constrained ARMA** (operator form): the full multiplicative
seasonal operator `φ(B)·Φ(Bˢ)·(1−B)ᵈ·(1−Bˢ)ᴰ` is the single lag polynomial
`sarimaArPoly`. -/
theorem lagPoly_sarimaArPoly (φ Φ : K[X]) (d D s : ℕ) :
    (lagPoly (sarimaArPoly φ Φ d D s) : Module.End K (ℤ → M))
      = lagPoly φ * seasonalLagPoly Φ s * (lagPoly (diffPoly d) * lagPoly ((1 - X ^ s) ^ D)) := by
  simp only [sarimaArPoly, seasonalDiffPoly, seasonalLagPoly, diffPoly, lagPoly_mul, mul_assoc]

/-! ## ARIMA and SARIMA processes -/

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Definition 9.1.1**: `x` is an **ARIMA(p,d,q) process** if the differenced series
`(1 − B)ᵈ x` is an ARMA(p,q) process (with AR polynomial `φ`, MA polynomial `θ`,
driven by white noise `z ~ WN(0, σ²)`). -/
abbrev IsARIMA (φ θ : ℝ[X]) (d : ℕ) (x z : ℤ → Ω → ℝ) (μ : Measure Ω) (σ2 : ℝ) : Prop :=
  IsARMA φ θ (lagPoly (diffPoly d : ℝ[X]) x) z μ σ2

/-- **Definition 9.6.1**: `x` is a **SARIMA(p,d,q)(P,D,Q)ₛ process with period `s`** if
the differenced series `Y = (1 − B)ᵈ (1 − Bˢ)ᴰ x` satisfies `φ(B) Φ(Bˢ) Y =
θ(B) Θ(Bˢ) z` — i.e. `Y` is an ARMA process with AR polynomial `φ · Φ(zˢ)` and MA
polynomial `θ · Θ(zˢ)`. -/
abbrev IsSARIMA (φ Φ θ Θ : ℝ[X]) (d D s : ℕ) (x z : ℤ → Ω → ℝ) (μ : Measure Ω)
    (σ2 : ℝ) : Prop :=
  IsARMA (φ * Φ.comp (X ^ s)) (θ * Θ.comp (X ^ s))
    (lagPoly (seasonalDiffPoly d D s : ℝ[X]) x) z μ σ2

/-- The ARIMA difference equation in combined form: `φ(B) (1 − B)ᵈ x = θ(B) z`
(eq. 9.1.1). -/
theorem IsARIMA.armaEq {φ θ : ℝ[X]} {d : ℕ} {x z : ℤ → Ω → ℝ} {σ2 : ℝ}
    (h : IsARIMA φ θ d x z μ σ2) : lagPoly (φ * diffPoly d) x = lagPoly θ z := by
  have hd := h.diffEq
  rw [lagPoly_mul_apply]; exact hd

/-- **SARIMA is a constrained ARMA** (process form): a SARIMA(p,d,q)(P,D,Q)ₛ process
satisfies the ARMA-type difference equation `(φ·Φ(zˢ)·(1−z)ᵈ·(1−zˢ)ᴰ)(B) x =
(θ·Θ(zˢ))(B) z`, i.e. an ARMA model whose autoregressive polynomial is the
factored `sarimaArPoly`. -/
theorem IsSARIMA.armaEq {φ Φ θ Θ : ℝ[X]} {d D s : ℕ} {x z : ℤ → Ω → ℝ} {σ2 : ℝ}
    (h : IsSARIMA φ Φ θ Θ d D s x z μ σ2) :
    lagPoly (sarimaArPoly φ Φ d D s) x = lagPoly (sarimaMaPoly θ Θ s) z := by
  have hd := h.diffEq
  simp only [sarimaArPoly, sarimaMaPoly]
  rw [lagPoly_mul_apply]
  exact hd

end DeepWiki.TimeSeries
