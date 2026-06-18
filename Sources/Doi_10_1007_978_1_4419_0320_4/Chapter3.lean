import DeepWiki.TimeSeries.ArmaProcesses
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 3: Stationary ARMA Processes
Each numbered item of the book's Chapter 3 is named by its book number: an
`abbrev` aliasing the library declaration for definitions, a `theorem` (discharged
by the `DeepWiki` library) for theorems/examples. The book numbering lives here in
the catalog; the citation is in each docstring, the DOI in
`Sources.Doi_10_1007_978_1_4419_0320_4.Source`. -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries
open scoped Polynomial

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

/-! ## §3.1 Causal and Invertible ARMA Processes -/

/-- **§3.1** (p.78), the lag polynomial `p(B)` (eqs 3.1.5–3.1.8): a polynomial
(the AR/MA polynomial) evaluated at the backshift operator `B`. The library's
`lagPoly`. -/
noncomputable abbrev lagPoly := @DeepWiki.TimeSeries.lagPoly

/-- **Definition 3.1.1** (§3.1, p.78), white noise `WN(0,σ²)`: a stationary process
with mean zero and autocovariance `γ(h) = σ²` if `h = 0` else `0`. The library's
`IsWhiteNoise`. -/
abbrev def_3_1_1 := @DeepWiki.TimeSeries.IsWhiteNoise

/-- **Definition 3.1.2** (§3.1, p.78), the ARMA(p,q) process: a stationary `X` with
`φ(B)X = θ(B)Z`, `Z ~ WN(0,σ²)`, where `φ(z) = 1 − φ₁z − ⋯ − φₚzᵖ` (3.1.6) and
`θ(z) = 1 + θ₁z + ⋯ + θ_qz^q` (3.1.7). The library's `IsARMA`. -/
abbrev def_3_1_2 := @DeepWiki.TimeSeries.IsARMA

/-- **Equation (3.1.5)** (§3.1, p.78), the compact ARMA difference equation
`φ(B)X = θ(B)Z`. The library's `IsARMA.diffEq`. -/
abbrev eq_3_1_5 := @DeepWiki.TimeSeries.IsARMA.diffEq

/-- **Example 3.1.1** (§3.1, p.78), the MA(q) process (the case `φ ≡ 1`): `X = θ(B)Z`.
The library's `IsMA`. -/
abbrev ex_3_1_1 := @DeepWiki.TimeSeries.IsMA

/-- **Example 3.1.1** (§3.1, p.78), the MA(q) defining equation in solved form
`X = θ(B)Z`. The library's `IsMA.eq`. -/
theorem ex_3_1_1_eq {θ : ℝ[X]} {Xp Z : ℤ → Ω → ℝ} {σ2 : ℝ}
    (h : IsMA θ Xp Z μ σ2) : Xp = lagPoly θ Z :=
  h.eq

-- Book-faithful restatement (step 5): white noise is uncorrelated at nonzero lags.
example {Z : ℤ → Ω → ℝ} {σ2 : ℝ} (h : IsWhiteNoise Z μ σ2) {k : ℤ} (hk : k ≠ 0) :
    acvfStat Z μ k = 0 := by rw [h.acvf_eq]; simp [hk]

-- Book-faithful restatement: the AR(p) defining equation `φ(B)X = Z`.
example {φ : ℝ[X]} {Xp Z : ℤ → Ω → ℝ} {σ2 : ℝ} (h : IsAR φ Xp Z μ σ2) :
    lagPoly φ Xp = Z :=
  h.eq

end DeepWiki.Ts
