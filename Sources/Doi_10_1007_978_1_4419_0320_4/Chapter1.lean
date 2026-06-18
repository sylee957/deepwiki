import DeepWiki.TimeSeries.BackshiftOperator
import DeepWiki.TimeSeries.StationaryProcesses
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 1: Stationary Time Series
Each numbered item of the book's Chapter 1 is one declaration named by its book
number: an `abbrev` aliasing the library declaration for definitions, a `theorem`
(the book-faithful statement, discharged by the `DeepWiki` library) for
theorems/propositions. The book numbering lives here in the catalog, never in the
library; the citation (section, page) is in each docstring, the source's DOI in
`Sources.Doi_10_1007_978_1_4419_0320_4.Source`. -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : ℤ → Ω → ℝ}

/-! ## §1.3 Stationarity and Strict Stationarity -/

/-- **Definition 1.3.1** (§1.3, p.11), the autocovariance function
`γ_X(r,s) = Cov(Xᵣ, Xₛ)` of a process with finite second moments. The library's
`acvf`. -/
noncomputable abbrev def_1_3_1 := @DeepWiki.TimeSeries.acvf

/-- **Definition 1.3.2** (§1.3, p.12), (weak) stationarity: `E|Xₜ|² < ∞`, the mean
`E[Xₜ]` is constant, and `γ_X(r,s) = γ_X(r+t, s+t)`. The library's
`IsWeaklyStationary`. -/
abbrev def_1_3_2 := @DeepWiki.TimeSeries.IsWeaklyStationary

/-- **Definition 1.3.3** (§1.3, p.12), strict stationarity: the joint distributions
of `(X_{t₁},…,X_{tₖ})` and `(X_{t₁+h},…,X_{tₖ+h})` agree for all `k, t, h`. The
library's `IsStrictlyStationary`. -/
abbrev def_1_3_3 := @DeepWiki.TimeSeries.IsStrictlyStationary

/-! ## §1.5 The Autocovariance Function of a Stationary Process -/

/-- **Proposition 1.5.1** (§1.5, p.26), elementary properties of the autocovariance
`γ` of a stationary process: `γ(0) ≥ 0` (1.5.1), `|γ(h)| ≤ γ(0)` (1.5.2), and `γ`
is even, `γ(h) = γ(−h)` (1.5.3). -/
theorem prop_1_5_1 [MeasureTheory.IsProbabilityMeasure μ] (hX : IsWeaklyStationary X μ) :
    0 ≤ acvfStat X μ 0 ∧
      (∀ h : ℤ, |acvfStat X μ h| ≤ acvfStat X μ 0) ∧
      (∀ h : ℤ, acvfStat X μ h = acvfStat X μ (-h)) :=
  ⟨hX.acvfStat_zero_nonneg, hX.abs_acvfStat_le, fun h => (hX.acvfStat_neg h).symm⟩

/-- **Definition 1.5.1** (§1.5, p.26), non-negative definiteness of a function
`κ : ℤ → ℝ`: `∑ᵢⱼ aᵢ aⱼ κ(tᵢ − tⱼ) ≥ 0`. The library's `IsNonnegDefinite`. -/
abbrev def_1_5_1 := @DeepWiki.TimeSeries.IsNonnegDefinite

/-- **§1.5** (p.26): the autocovariance function of a stationary process is
non-negative definite (the property of Definition 1.5.1). The library's
`IsWeaklyStationary.isNonnegDefinite_acvfStat`. -/
theorem acvf_nonnegDefinite [MeasureTheory.IsProbabilityMeasure μ]
    (hX : IsWeaklyStationary X μ) : IsNonnegDefinite (acvfStat X μ) :=
  hX.isNonnegDefinite_acvfStat

/-- **Theorem 1.5.2** (§1.5, p.27), characterization of autocovariance functions
(forward direction): the autocovariance of a stationary process is even and
non-negative definite. The converse (every such function is an ACVF, via
Kolmogorov's theorem) is not formalized. The library's
`IsWeaklyStationary.even_and_isNonnegDefinite_acvfStat`. -/
theorem thm_1_5_2 [MeasureTheory.IsProbabilityMeasure μ] (hX : IsWeaklyStationary X μ) :
    (∀ h : ℤ, acvfStat X μ h = acvfStat X μ (-h)) ∧ IsNonnegDefinite (acvfStat X μ) :=
  hX.even_and_isNonnegDefinite_acvfStat

/-! ## §1.4 The Estimation and Elimination of Trend and Seasonal Components -/

/-- **§1.4** (p.20), the backshift operator `B`: `B Xₜ = X_{t−1}`. The library's
`backshift`. -/
abbrev backshift := @DeepWiki.TimeSeries.backshift

/-- **§1.4** (p.20), the difference operator `∇ = 1 − B`: `∇ Xₜ = Xₜ − X_{t−1}`.
Applied `k` times it reduces a polynomial trend of degree `k` to a constant. The
library's `difference`. -/
abbrev difference := @DeepWiki.TimeSeries.difference

/-- **Equation (1.4.19)** (§1.4, p.24), the lag-`d` difference operator
`∇_d Xₜ = Xₜ − X_{t−d} = (1 − Bᵈ) Xₜ` (not to be confused with `∇ᵈ = (1 − B)ᵈ`).
The library's `seasonalDifference`. -/
abbrev eq_1_4_19 := @DeepWiki.TimeSeries.seasonalDifference

/-- **§1.4** (p.24), purpose of `∇_d`: applied to a model `Xₜ = mₜ + sₜ + Yₜ`
whose seasonal component `sₜ` has period `d`, the operator `∇_d` annihilates the
seasonal part. Here the bare period-`d` series is removed: `∇_d s = 0`. The
library's `seasonalDifference_periodic`. -/
theorem seasonal_elimination {d : ℕ} {s : ℤ → ℝ} (hper : ∀ t : ℤ, s (t + d) = s t) :
    seasonalDifference d s = 0 :=
  seasonalDifference_periodic hper

/-! ## Book-faithful restatements of the §1.4 defining equations -/

-- `B Xₜ = X_{t−1}`.
example (X : ℤ → ℝ) (t : ℤ) : backshift X t = X (t - 1) := rfl

-- `∇ Xₜ = Xₜ − X_{t−1}`.
example (X : ℤ → ℝ) (t : ℤ) : difference X t = X t - X (t - 1) := rfl

-- `∇_d Xₜ = Xₜ − X_{t−d}` (the defining equation of 1.4.19).
example (X : ℤ → ℝ) (d : ℕ) (t : ℤ) : eq_1_4_19 d X t = X t - X (t - d) := rfl

-- `(1.4.19)`: `∇_d = 1 − Bᵈ`.
example (X : ℤ → ℝ) (d : ℕ) : eq_1_4_19 d X = X - backshift^[d] X :=
  seasonalDifference_eq_sub_backshift_iterate d X

-- §1.4 trend elimination: `∇` reduces a linear trend `a·t + b` to the constant `a`.
example (a b : ℝ) : difference (fun t : ℤ => a * (t : ℝ) + b) = fun _ => a :=
  difference_linear a b

end DeepWiki.Ts
