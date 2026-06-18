import DeepWiki.TimeSeries.BackshiftOperator
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
