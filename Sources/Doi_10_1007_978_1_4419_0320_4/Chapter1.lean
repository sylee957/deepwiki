import DeepWiki.TimeSeries.BackshiftOperator
import DeepWiki.TimeSeries.StationaryProcesses
import DeepWiki.TimeSeries.ProcessExamples
import DeepWiki.TimeSeries.GaussianTimeSeries
import DeepWiki.TimeSeries.LinearFilters
import DeepWiki.TimeSeries.StationaryGaussianProcess
import DeepWiki.TimeSeries.FiniteDimensionalDistributions
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
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : ℤ → Ω → ℝ}

/-! ## §1.2 Stochastic Processes -/

/-- **Definition 1.2.1** (§1.2, p.8), a stochastic process: a family `(Xₜ, t ∈ T)` of
random variables on a probability space. The library models a real-valued, ℤ-indexed
process as `X : ℤ → Ω → ℝ` — the abbreviation `Process`. -/
abbrev def_1_2_1 := @DeepWiki.TimeSeries.Process

/-- **Definition 1.2.2** (§1.2, p.9), a realization (sample path) `t ↦ Xₜ(ω)` of a
process `X`. The library's `realization`. -/
abbrev def_1_2_2 := @DeepWiki.TimeSeries.realization

/-- **Example 1.2.1** (§1.2, p.9), the sinusoid with random phase and amplitude
`Xₜ = r⁻¹ A cos(νt + Θ)` (1.2.1), with `A ≥ 0` and `Θ ~ Uniform[0,2π]` independent. The
library's `sinusoidProcess`. -/
noncomputable abbrev ex_1_2_1 := @DeepWiki.TimeSeries.sinusoidProcess

/-- **Example 1.2.2** (§1.2, p.9), the binary process: an iid sequence of fair `±1`
flips, `P(Xₜ = 1) = P(Xₜ = -1) = 1/2` (1.2.3) with joint law `2⁻ⁿ` (1.2.4) — its existence
is guaranteed by Kolmogorov's theorem. The library's `exists_iidBinaryProcess`. -/
alias ex_1_2_2 := DeepWiki.TimeSeries.exists_iidBinaryProcess

/-- **Example 1.2.3** (§1.2, p.10), the random walk `Sₜ = X₁ + ⋯ + Xₜ` built from an iid
sequence (its existence guaranteed by Kolmogorov's theorem). The library's `randomWalk`;
its non-stationarity is **Example 1.3.4**. -/
noncomputable abbrev ex_1_2_3 := @DeepWiki.TimeSeries.randomWalk

/-- **Example 1.2.4** (§1.2, p.10), the Bienaymé–Galton–Watson branching process `X₀ = x`,
`X_{t+1} = ∑_{j < Xₜ} Z_{t,j}` (1.2.6), the offspring totals of an iid family. The
library's `branchingProcess`. -/
abbrev ex_1_2_4 := @DeepWiki.TimeSeries.branchingProcess

/-- **Definition 1.2.3** (§1.2, p.11), the (finite-dimensional) distribution functions
`F_t(x) = P(X_{t₁} ≤ x₁, …, X_{tₙ} ≤ xₙ)` (1.2.7) of a process. The library's `fdd`, the
joint law of `(Xₜ)_{t ∈ I}` on a finite index set `I`, whose CDF is the book's `F_t`. -/
noncomputable abbrev def_1_2_3 := @DeepWiki.TimeSeries.fdd

/-- **Theorem 1.2.1** (Kolmogorov's theorem, §1.2, p.11): a family of finite-dimensional
distribution functions arises from some stochastic process iff it satisfies the consistency
conditions (1.2.8). The existence (`if`) direction: a consistent (projective) family `P` is
realized by the coordinate process `(t, ω) ↦ ω t` on the projective limit; the consistency
(`only if`) direction is `isProjectiveMeasureFamily_fdd`. The library's `exists_process_fdd_eq`. -/
theorem thm_1_2_1 (P : ∀ I : Finset ℤ, MeasureTheory.Measure (↥I → ℝ))
    [∀ I, MeasureTheory.IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily (α := fun _ : ℤ => ℝ) P) :
    ∃ ν : MeasureTheory.Measure (ℤ → ℝ), MeasureTheory.IsProbabilityMeasure ν ∧
      ∀ I, fdd (fun t ω => ω t) ν I = P I :=
  exists_process_fdd_eq P hP

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

/-- **Definition 1.3.4** (§1.3, p.13), a Gaussian time series: a process all of whose
finite-dimensional distributions are multivariate normal. The library's
`IsGaussianTimeSeries` (Mathlib's `IsGaussianProcess`). -/
abbrev def_1_3_4 := @DeepWiki.TimeSeries.IsGaussianTimeSeries

/-- **Example 1.3.1** (§1.3, p.13), the cosine process `Xₜ = A cos(θt) + B sin(θt)`
with `A`, `B` uncorrelated, mean zero, common variance `σ²` has autocovariance
`γ(r,s) = σ² cos(θ(r − s))` (hence is stationary). The library's `cosProcess`,
`cosProcess_acvf`. -/
theorem ex_1_3_1 [IsFiniteMeasure μ] {A B : Ω → ℝ} {θ σ2 : ℝ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hVA : cov[A, A; μ] = σ2) (hVB : cov[B, B; μ] = σ2) (hAB : cov[A, B; μ] = 0)
    (r s : ℤ) :
    acvf (cosProcess A B θ) μ r s = σ2 * Real.cos (θ * ((r : ℝ) - (s : ℝ))) :=
  cosProcess_acvf hA hB hVA hVB hAB r s

/-- **Example 1.3.4** (§1.3, p.14), the random walk `Sₜ = X₁ + ⋯ + Xₜ` of a
zero-mean uncorrelated sequence with `σ² > 0` is not (covariance) stationary, since
`Var(Sₜ)` grows with `t`. The library's `randomWalk`, `randomWalk_not_stationary`. -/
theorem ex_1_3_4 [IsFiniteMeasure μ] {Xs : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hX : ∀ i, MemLp (Xs i) 2 μ) (huc : ∀ i j, cov[Xs i, Xs j; μ] = if i = j then σ2 else 0)
    (hσ : 0 < σ2) : ¬ IsWeaklyStationary (randomWalk Xs) μ :=
  randomWalk_not_stationary hX huc hσ

/-- **Example 1.3.2** (§1.3, p.13), the MA(1) process `Xₜ = Zₜ + θ Zₜ₋₁` of a
zero-mean uncorrelated sequence with variance `σ²` has autocovariance
`γ(0) = (1+θ²)σ²`, `γ(±1) = θσ²`, and `γ(h) = 0` for `|h| > 1`. The library's
`maProcess1`, `maProcess1_acvf_zero`/`_one`/`_ge_two`. -/
theorem ex_1_3_2 [IsFiniteMeasure μ] {Zs : ℤ → Ω → ℝ} {θ σ2 : ℝ}
    (hZ : ∀ i, MemLp (Zs i) 2 μ) (huc : ∀ i j, cov[Zs i, Zs j; μ] = if i = j then σ2 else 0)
    (s : ℤ) :
    cov[maProcess1 Zs θ s, maProcess1 Zs θ s; μ] = (1 + θ ^ 2) * σ2 ∧
      cov[maProcess1 Zs θ (s + 1), maProcess1 Zs θ s; μ] = θ * σ2 ∧
      (∀ h, 2 ≤ h → cov[maProcess1 Zs θ (s + h), maProcess1 Zs θ s; μ] = 0) :=
  ⟨maProcess1_acvf_zero hZ huc s, maProcess1_acvf_one hZ huc s,
    fun h hh => maProcess1_acvf_ge_two hZ huc s h hh⟩

/-- **Example 1.3.3** (§1.3, p.13), the process `Xₜ = Zₜ + 1{t odd}` has lag-only
autocovariance but a non-constant mean, hence is not (covariance) stationary. The
library's `parityShift`, `parityShift_not_stationary`. -/
theorem ex_1_3_3 [IsProbabilityMeasure μ] {Zs : ℤ → Ω → ℝ}
    (hZ : ∀ t, Integrable (Zs t) μ) (hZmean : mean Zs μ 0 = mean Zs μ 1) :
    ¬ IsWeaklyStationary (parityShift Zs) μ :=
  parityShift_not_stationary hZ hZmean

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

/-- **Theorem 1.5.1** (§1.5, p.27), characterization of autocovariance functions: a
function `κ : ℤ → ℝ` is the autocovariance of a stationary process iff it is even
and non-negative definite. (Propositions, Definitions and Theorems carry separate §1.5
counters, so this Theorem 1.5.1 coexists with Proposition 1.5.1 and Definition 1.5.1.)
The converse (existence) is constructed from a Gaussian projective family via the
Kolmogorov extension theorem (vendored in `DeepWiki/MeasureTheory/`). The library's
`isACVF_iff_even_and_isNonnegDefinite`. -/
theorem thm_1_5_1 (κ : ℤ → ℝ) :
    (∃ (ν : MeasureTheory.Measure (ℤ → ℝ)) (X : ℤ → (ℤ → ℝ) → ℝ),
        MeasureTheory.IsProbabilityMeasure ν ∧ IsWeaklyStationary X ν ∧
        ∀ h, acvfStat X ν h = κ h)
      ↔ (∀ h, κ (-h) = κ h) ∧ IsNonnegDefinite κ :=
  isACVF_iff_even_and_isNonnegDefinite κ

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

/-! ## Problems -/

/-- **Problem 1.2** (p.39), sufficiency: a linear filter `{aⱼ}` whose weights
satisfy `∑ⱼ aⱼ = 1` and `∑ⱼ jʳ aⱼ = 0` for `r = 1,…,k` passes every polynomial
trend of degree `≤ k` without distortion. The library's `filter_passes_poly`. -/
theorem ex_1_2 {a : ℤ → ℝ} {s : Finset ℤ} {k : ℕ}
    (h0 : ∑ j ∈ s, a j = 1) (hm : ∀ r, 1 ≤ r → r ≤ k → ∑ j ∈ s, (j : ℝ) ^ r * a j = 0)
    (c : ℕ → ℝ) (t : ℝ) :
    ∑ j ∈ s, a j * (∑ r ∈ Finset.range (k + 1), c r * (t - (j : ℝ)) ^ r)
      = ∑ r ∈ Finset.range (k + 1), c r * t ^ r :=
  filter_passes_poly h0 hm c t

/-- **Problem 1.8(a)** (p.40): the operator `∇ ∇_d` annihilates a linear trend plus a
period-`d` seasonal component: `∇(∇_d (a + b·t + sₜ)) = 0` when `{sₜ}` has period `d`.
(Hence for `Yₜ = a + b·t + sₜ + Xₜ`, `∇∇_d Yₜ = ∇∇_d Xₜ`.) Discharged by the
library's `seasonalDifference`/`difference` and `difference_const`. -/
theorem ex_1_8 {d : ℕ} (a b : ℝ) {s : ℤ → ℝ} (hper : ∀ t : ℤ, s (t + d) = s t) :
    difference (seasonalDifference d (fun t : ℤ => a + b * (t : ℝ) + s t)) = 0 := by
  have hsd : seasonalDifference d (fun t : ℤ => a + b * (t : ℝ) + s t)
      = fun _ => b * (d : ℝ) := by
    funext t
    have hst : s (t - (d : ℤ)) = s t := by
      have h := hper (t - (d : ℤ))
      rw [show (t - (d : ℤ)) + (d : ℤ) = t from by ring] at h
      exact h.symm
    simp only [seasonalDifference_apply, hst]
    push_cast
    ring
  rw [hsd]
  exact difference_const _

end DeepWiki.Ts
