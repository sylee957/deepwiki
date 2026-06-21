import DeepWiki.TimeSeries.SeasonalArma
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 9: Model Building and Forecasting with ARIMA Processes
Book items of Chapter 9 named by book number, discharged by the `DeepWiki`
library. The numbering lives here; citations are in each docstring, the DOI in
`Sources.Doi_10_1007_978_1_4419_0320_4.Source`. -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries
open scoped Polynomial

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

/-! ## §9.1 ARIMA Models for Non-Stationary Time Series -/

/-- **Definition 9.1.1** (§9.1, p.274), the ARIMA(p,d,q) process: `Xₜ` such that the
differenced series `(1 − B)ᵈ Xₜ` is a causal ARMA(p,q) process. The library's
`IsARIMA`. -/
abbrev def_9_1_1 := @DeepWiki.TimeSeries.IsARIMA

/-- **Equation (9.1.1)** (§9.1, p.274), the combined ARIMA difference equation
`φ(B)(1 − B)ᵈ Xₜ = θ(B) Zₜ` (i.e. `φ*(B)Xₜ = θ(B)Zₜ` with `φ*(z) = φ(z)(1−z)ᵈ`).
Discharged by the library's `IsARIMA.armaEq`. -/
theorem eq_9_1_1 {φ θ : ℝ[X]} {d : ℕ} {x z : ℤ → Ω → ℝ} {σ2 : ℝ}
    (h : IsARIMA φ θ d x z μ σ2) : lagPoly (φ * diffPoly d) x = lagPoly θ z :=
  h.armaEq

/-! ## §9.6 Seasonal ARIMA Models -/

/-- **§9.6** (p.321), the seasonal lag operator `Φ(Bˢ)`: the seasonal polynomial
evaluated at the seasonal backshift `Bˢ`. The library's `seasonalLagPoly`. -/
noncomputable abbrev seasonalLagPoly := @DeepWiki.TimeSeries.seasonalLagPoly

/-- **Definition 9.6.1** (§9.6, p.323), the SARIMA(p,d,q)(P,D,Q)ₛ process with period
`s`: `Xₜ` such that `Yₜ = (1 − B)ᵈ(1 − Bˢ)ᴰ Xₜ` is a causal ARMA process satisfying
`φ(B)Φ(Bˢ) Yₜ = θ(B)Θ(Bˢ) Zₜ` (eq. 9.6.5). The library's `IsSARIMA`. -/
abbrev def_9_6_1 := @DeepWiki.TimeSeries.IsSARIMA

/-- **§9.6** (p.323), the SARIMA process as a constrained ARMA: the full
multiplicative operator equation `φ(B)Φ(Bˢ)(1−B)ᵈ(1−Bˢ)ᴰ Xₜ = θ(B)Θ(Bˢ) Zₜ`, an
ARMA difference equation whose autoregressive polynomial is the factored
`sarimaArPoly`. Discharged by the library's `IsSARIMA.armaEq`. -/
theorem sarima_constrained_arma {φ Φ θ Θ : ℝ[X]} {d D s : ℕ} {x z : ℤ → Ω → ℝ} {σ2 : ℝ}
    (h : IsSARIMA φ Φ θ Θ d D s x z μ σ2) :
    lagPoly (sarimaArPoly φ Φ d D s) x = lagPoly (sarimaMaPoly θ Θ s) z :=
  h.armaEq

/-! ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§9.2–§9.4: identification techniques (model selection from the sample ACF/PACF) [infra]; order
selection by the AICC criterion [infra]; diagnostic checking (residual analysis, portmanteau tests)
[infra]
§9.5: forecasting `ARIMA` processes (the best linear predictor of the integrated model and the
`h`-step prediction bounds) [infra]
(The `ARIMA`/`SARIMA` model definitions and difference equations — def 9.1.1, eq 9.1.1, def 9.6.1, the
constrained-ARMA equation — are done; the data-analytic model-building, order-selection, diagnostic,
and forecasting procedures rest on the Chapter 6–8 estimation/limit theory.) -/

end DeepWiki.Ts
