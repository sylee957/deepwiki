import DeepWiki.TimeSeries.LagPolynomials
import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.Analysis.RCLike.Basic
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

/-- **Equation (3.1.4)**, the ARMA difference equation written out: at every time `t`,
`∑ⱼ φⱼ X_{t−j} = ∑ⱼ θⱼ Z_{t−j}`, i.e. `Xₜ − φ₁X_{t−1} − ⋯ − φₚX_{t−p} = Zₜ + θ₁Z_{t−1} + ⋯ +
θ_q Z_{t−q}` (with `φ(z) = 1 − φ₁z − ⋯` and `θ(z) = 1 + θ₁z + ⋯`). The expanded reading of the
operator form `φ(B) X = θ(B) Z` (`IsARMA.diffEq`), via `lagPoly_apply`. -/
theorem IsARMA.diffEq_apply {φ θ : ℝ[X]} {X Z : ℤ → Ω → ℝ} {σ2 : ℝ} (h : IsARMA φ θ X Z μ σ2)
    (t : ℤ) :
    ∑ j ∈ Finset.range (φ.natDegree + 1), φ.coeff j • X (t - j)
      = ∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j • Z (t - j) := by
  have hd := congrFun h.diffEq t
  rwa [lagPoly_apply, lagPoly_apply] at hd

/-- **Example 3.1.1**, the MA(q) process written out: `Xₜ = ∑_{j=0}^q θⱼ Z_{t−j} = Zₜ + θ₁Z_{t−1}
+ ⋯ + θ_q Z_{t−q}`, the expanded reading of `X = θ(B) Z` (`IsMA.eq`). -/
theorem IsMA.eq_apply {θ : ℝ[X]} {X Z : ℤ → Ω → ℝ} {σ2 : ℝ} (h : IsMA θ X Z μ σ2) (t : ℤ) :
    X t = ∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j • Z (t - j) := by
  rw [h.eq, lagPoly_apply]

/-- **The AR(1) difference equation written out**: an AR(1) process with autoregressive
polynomial `φ(z) = 1 − φ₁ z`, i.e. `(1 − φ₁B) X = Z`, satisfies `Xₜ − φ₁ Xₜ₋₁ = Zₜ` — equivalently
the autoregressive recursion `Xₜ = φ₁ Xₜ₋₁ + Zₜ`. -/
theorem IsAR.ar1_apply {φ₁ : ℝ} {X Z : ℤ → Ω → ℝ} {σ2 : ℝ}
    (h : IsAR (1 - Polynomial.C φ₁ * Polynomial.X) X Z μ σ2) (t : ℤ) :
    X t - φ₁ • X (t - 1) = Z t := by
  have hd := congrFun h.eq t
  rwa [lagPoly_one_sub_C_mul_X_apply] at hd

/-- **§3.1 (Theorem 3.1.1, causality criterion).** The autoregressive polynomial `φ`
satisfies the **causality condition** when it has no zero in the closed complex unit disk:
`φ(z) ≠ 0` for all `‖z‖ ≤ 1`. By Theorem 3.1.1 this is equivalent to the existence of an
absolutely-summable causal `MA(∞)` representation `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` with `∑ⱼ |ψⱼ| < ∞`; that
equivalence is the analytic content of the theorem and needs `PowerSeries`-reciprocal and
mean-square summability infrastructure not developed here. -/
def IsCausalPoly (φ : ℝ[X]) : Prop := ∀ z : ℂ, ‖z‖ ≤ 1 → Polynomial.aeval z φ ≠ 0

/-- **§3.1 (Theorem 3.1.2, invertibility criterion).** The moving-average polynomial `θ`
satisfies the **invertibility condition** when `θ(z) ≠ 0` for all `‖z‖ ≤ 1`; by Theorem 3.1.2
this is equivalent to an absolutely-summable `AR(∞)` representation `Zₜ = ∑ⱼ πⱼ Xₜ₋ⱼ` (same
analytic caveat as causality). -/
def IsInvertiblePoly (θ : ℝ[X]) : Prop := ∀ z : ℂ, ‖z‖ ≤ 1 → Polynomial.aeval z θ ≠ 0

/-- The AR(1) autoregressive polynomial `1 - φ₁ z` evaluated at `z : ℂ`. -/
theorem aeval_ar1 (φ₁ : ℝ) (z : ℂ) :
    Polynomial.aeval z (1 - Polynomial.C φ₁ * Polynomial.X) = 1 - (φ₁ : ℂ) * z := by
  simp only [map_sub, map_one, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Complex.coe_algebraMap]

/-- **§3.1**: the `AR(1)` process is causal iff `|φ₁| < 1` — its autoregressive polynomial
`1 - φ₁ z` has its only root `1/φ₁` strictly outside the closed unit disk. -/
theorem isCausalPoly_ar1 (φ₁ : ℝ) :
    IsCausalPoly (1 - Polynomial.C φ₁ * Polynomial.X) ↔ |φ₁| < 1 := by
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have hφ₁ : φ₁ ≠ 0 := fun h0 => by rw [h0, abs_zero] at hle; norm_num at hle
    have hz : ‖(φ₁ : ℂ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
      exact inv_le_one_of_one_le₀ hle
    have key := h (φ₁ : ℂ)⁻¹ hz
    rw [aeval_ar1, mul_inv_cancel₀ (by exact_mod_cast hφ₁ : (φ₁ : ℂ) ≠ 0)] at key
    exact key (sub_self 1)
  · intro h z hz
    rw [aeval_ar1]
    intro hcontra
    rw [sub_eq_zero] at hcontra
    have h1 : ‖(φ₁ : ℂ) * z‖ = 1 := by rw [← hcontra, norm_one]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
    have hb : |φ₁| * ‖z‖ ≤ |φ₁| := by
      simpa using mul_le_mul_of_nonneg_left hz (abs_nonneg φ₁)
    linarith

end DeepWiki.TimeSeries
