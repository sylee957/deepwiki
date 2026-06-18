import DeepWiki.TimeSeries.LagPolynomials
import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.Tactic

/-! # ARMA processes
White noise (Def 3.1.1) and the ARMA(p,q) process (Def 3.1.2): a stationary
process `X` satisfying the lag-polynomial difference equation `φ(B) X = θ(B) Z`
driven by white noise `Z`, with `φ` the autoregressive and `θ` the moving-average
polynomial. The MA(q) and AR(p) processes are the special cases `φ = 1` and
`θ = 1`. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory
open scoped Polynomial

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Definition 3.1.1**: white noise `WN(0, σ²)` — a stationary process with mean
zero and autocovariance `γ(h) = σ²` at lag `0` and `0` otherwise. -/
structure IsWhiteNoise (Z : ℤ → Ω → ℝ) (μ : Measure Ω) (σ2 : ℝ) : Prop where
  /-- White noise is (weakly) stationary. -/
  stationary : IsWeaklyStationary Z μ
  /-- White noise has mean zero. -/
  mean_zero : ∀ t : ℤ, mean Z μ t = 0
  /-- The autocovariance is `σ²` at lag 0 and `0` at all nonzero lags. -/
  acvf_eq : ∀ h : ℤ, acvfStat Z μ h = if h = 0 then σ2 else 0

/-- **Definition 3.1.2**: `X` is an **ARMA(p,q) process** with autoregressive
polynomial `φ` and moving-average polynomial `θ`, driven by white noise
`Z ~ WN(0, σ²)`, if `X` is stationary and satisfies the difference equation
`φ(B) X = θ(B) Z` (eq. 3.1.5). -/
structure IsARMA (φ θ : ℝ[X]) (X Z : ℤ → Ω → ℝ) (μ : Measure Ω) (σ2 : ℝ) : Prop where
  /-- The process is (weakly) stationary. -/
  stationary : IsWeaklyStationary X μ
  /-- The driving noise is white noise `WN(0, σ²)`. -/
  whiteNoise : IsWhiteNoise Z μ σ2
  /-- The lag-polynomial difference equation `φ(B) X = θ(B) Z`. -/
  diffEq : lagPoly φ X = lagPoly θ Z

/-- **Example 3.1.1**: an MA(q) process is the ARMA process with autoregressive
polynomial `1`, i.e. `X = θ(B) Z`. -/
abbrev IsMA (θ : ℝ[X]) (X Z : ℤ → Ω → ℝ) (μ : Measure Ω) (σ2 : ℝ) : Prop :=
  IsARMA 1 θ X Z μ σ2

/-- An AR(p) process is the ARMA process with moving-average polynomial `1`, i.e.
`φ(B) X = Z`. -/
abbrev IsAR (φ : ℝ[X]) (X Z : ℤ → Ω → ℝ) (μ : Measure Ω) (σ2 : ℝ) : Prop :=
  IsARMA φ 1 X Z μ σ2

/-- The defining equation of an MA(q) process in solved form: `X = θ(B) Z`. -/
theorem IsMA.eq {θ : ℝ[X]} {X Z : ℤ → Ω → ℝ} {σ2 : ℝ} (h : IsMA θ X Z μ σ2) :
    X = lagPoly θ Z := by
  have hd := h.diffEq
  rwa [lagPoly_one, Module.End.one_apply] at hd

/-- The defining equation of an AR(p) process in operator form: `φ(B) X = Z`. -/
theorem IsAR.eq {φ : ℝ[X]} {X Z : ℤ → Ω → ℝ} {σ2 : ℝ} (h : IsAR φ X Z μ σ2) :
    lagPoly φ X = Z := by
  have hd := h.diffEq
  rwa [lagPoly_one, Module.End.one_apply] at hd

end DeepWiki.TimeSeries
