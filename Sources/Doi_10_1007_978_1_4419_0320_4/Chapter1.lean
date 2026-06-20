import DeepWiki.TimeSeries.BackshiftOperator
import DeepWiki.TimeSeries.StationaryProcesses
import DeepWiki.TimeSeries.ProcessExamples
import DeepWiki.TimeSeries.GaussianTimeSeries
import DeepWiki.TimeSeries.LinearFilters
import DeepWiki.TimeSeries.StationaryGaussianProcess
import DeepWiki.TimeSeries.FiniteDimensionalDistributions
import DeepWiki.TimeSeries.SampleAutocovariance
import DeepWiki.TimeSeries.MultivariateNormal
import DeepWiki.TimeSeries.KolmogorovApplications
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.BrownianMotion.Basic
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

/-- **Definition 1.2.1** (§1.2, p.8), a stochastic process: a family `(Xₜ, t ∈ T)` of random
variables on a probability space, over an arbitrary index set `T` (Remark 1: `T` often `ℤ`,
`ℕ`, `[0,∞)`, `ℝ`, but need not be `⊆ ℝ`). The library's `Process T Ω 𝒳 := T → Ω → 𝒳`; the
time-series theory specializes to `T = ℤ`, `𝒳 = ℝ` (bare `ℤ → Ω → ℝ`). -/
abbrev def_1_2_1 := @DeepWiki.TimeSeries.Process

/-- **Definition 1.2.2** (§1.2, p.9), a realization (sample path) `t ↦ Xₜ(ω)` of a
process `X`. The library's `realization`. -/
abbrev def_1_2_2 := @DeepWiki.TimeSeries.realization

/-- **Example 1.2.1** (§1.2, p.9), the sinusoid with random phase and amplitude
`Xₜ = r⁻¹ A cos(νt + Θ)` (1.2.1), with `A ≥ 0` and `Θ ~ Uniform[0,2π]` independent. The
library's `sinusoidProcess`. -/
noncomputable abbrev ex_1_2_1 := @DeepWiki.TimeSeries.sinusoidProcess

/-- **Equation (1.2.2)** (§1.2, p.9), the realization of the sinusoid process at `ω`,
`Xₜ(ω) = r⁻¹ A(ω) cos(νt + Θ(ω))`. The library's `sinusoidProcess_apply`; that each `Xₜ` is a
random variable (so it is a genuine process) is `measurable_sinusoidProcess`. -/
theorem eq_1_2_2 {Ω : Type*} (r ν : ℝ) (A Θ : Ω → ℝ) (t : ℝ) (ω : Ω) :
    sinusoidProcess r ν A Θ t ω = r⁻¹ * A ω * Real.cos (ν * t + Θ ω) :=
  sinusoidProcess_apply r ν A Θ t ω

/-- **Example 1.2.2** (§1.2, p.9), the binary process: an iid sequence of fair `±1`
flips, `P(Xₜ = 1) = P(Xₜ = -1) = 1/2` (1.2.3) with joint law `2⁻ⁿ` (1.2.4) — its existence
is guaranteed by Kolmogorov's theorem. The library's `exists_iidBinaryProcess`. -/
alias ex_1_2_2 := DeepWiki.TimeSeries.exists_iidBinaryProcess

/-- **Equation (1.2.3)** (§1.2, p.9), the binary process stated by its marginal directly:
`P(Xₜ = 1) = P(Xₜ = -1) = 1/2`. The library's `exists_iidBinaryProcess_marginal`. -/
alias eq_1_2_3 := DeepWiki.TimeSeries.exists_iidBinaryProcess_marginal

/-- **Example 1.2.3** (§1.2, p.10), the random walk `S₀ = 0`, `Sₜ = X₁ + ⋯ + Xₜ` for `t ≥ 1`
(1.2.5), built from an iid sequence (its existence guaranteed by Kolmogorov's theorem). The
library's `randomWalk`, with the initial condition `S₀ = 0` as `randomWalk_zero`; its
non-stationarity is **Example 1.3.4**. -/
noncomputable abbrev ex_1_2_3 := @DeepWiki.TimeSeries.randomWalk

/-- **Example 1.2.4** (§1.2, p.10), the Bienaymé–Galton–Watson branching process `X₀ = x`,
`X_{t+1} = ∑_{j < Xₜ} Z_{t,j}` (1.2.6), the offspring totals of an iid family. The
library's `branchingProcess`. -/
abbrev ex_1_2_4 := @DeepWiki.TimeSeries.branchingProcess

/-- **Definition 1.2.3** (§1.2, p.11), the (finite-dimensional) distribution functions
`{F_t, t ∈ 𝒯}` of a process `X : T → Ω → ℝ`: for an `n`-tuple of times
`t = (t₁,…,tₙ) ∈ Tⁿ` (`t : Fin n → T`) and `x = (x₁,…,xₙ) ∈ ℝⁿ` (`x : Fin n → ℝ`),
`F_t(x) = P(X_{t₁} ≤ x₁, …, X_{tₙ} ≤ xₙ)` (1.2.7). The library's `distFn`. -/
noncomputable abbrev def_1_2_3 := @DeepWiki.TimeSeries.distFn

/-- **Equation (1.2.7)** (§1.2, p.11), the distribution-function formula
`F_t(x) = P(X_{t₁} ≤ x₁, …, X_{tₙ} ≤ xₙ)` — by definition the probability of the lower-orthant
event `{ω | X_{tᵢ}(ω) ≤ xᵢ for all i}`. The library's `distFn`. -/
noncomputable abbrev eq_1_2_7 := @DeepWiki.TimeSeries.distFn

/-- **Theorem 1.2.1** (Kolmogorov's theorem, §1.2, p.11), the book's *if and only if*, over an
arbitrary index set `T` (the book's real times `T ⊆ ℝ`; the time series specializes to `T = ℤ`):
a family `P` of finite-dimensional distributions — one probability measure `P I` per finite set
of times `I : Finset T`, whose distribution functions are the book's `F_t` —

`{F_t} are the distribution functions of some stochastic process  ⟺  the {F_t} are consistent`.

"Are the distribution functions of some process" = realized by the coordinate process
`(t, ω) ↦ ω t` on a probability space `(T → ℝ, ν)`, i.e. `∀ I, fdd (·) ν I = P I`.
"Consistent" = `IsProjectiveMeasureFamily P`, the measure form of the book's condition (1.2.8)
`lim_{xᵢ → ∞} F_t(x) = F_{t(i)}(x(i))` (its F-function rendering is `distFn_tendsto_marginal`,
`eq_1_2_8`). The `←` (existence) half is Kolmogorov's theorem (`exists_process_fdd_eq`); the `→`
(consistency) half is `isProjectiveMeasureFamily_fdd`, that an actual process's distributions are
always consistent. -/
theorem thm_1_2_1 {T : Type*} [Nonempty T] (P : ∀ I : Finset T, MeasureTheory.Measure (↥I → ℝ))
    [∀ I, MeasureTheory.IsProbabilityMeasure (P I)] :
    (∃ ν : MeasureTheory.Measure (T → ℝ), MeasureTheory.IsProbabilityMeasure ν ∧
        ∀ I : Finset T, fdd (fun (t : T) (ω : T → ℝ) => ω t) ν I = P I)
      ↔ MeasureTheory.IsProjectiveMeasureFamily (α := fun _ : T => ℝ) P := by
  refine ⟨fun ⟨ν, _, hfdd⟩ => ?_, fun hP => exists_process_fdd_eq P hP⟩
  have h := isProjectiveMeasureFamily_fdd (μ := ν) (X := fun (t : T) (ω : T → ℝ) => ω t)
    (fun t => (measurable_pi_apply t).aemeasurable)
  rwa [(funext hfdd : (fun I => fdd (fun (t : T) (ω : T → ℝ) => ω t) ν I) = P)] at h

/-- **Consistency condition (1.2.8)** (§1.2, p.11), the `only if` half of Theorem 1.2.1 in the
book's notation: the distribution functions of a process satisfy
`lim_{xᵢ → ∞} F_t(x) = F_{t(i)}(x(i))` — sending the `i`-th argument to `+∞` recovers the
distribution function with the `i`-th time and argument (`Fin.removeNth i`) deleted. The
library's `distFn_tendsto_marginal`. -/
abbrev eq_1_2_8 := @DeepWiki.TimeSeries.distFn_tendsto_marginal

/-- **Equation (1.2.9)** (§1.2, p.12), the characteristic-function form of the consistency
condition: with `φ_t(u) = ∫ e^{i u'x} F_t(dx)` the CF of the fdd, letting the `i`-th frequency
`uᵢ → 0` recovers the CF with the `i`-th time deleted, `lim_{uᵢ → 0} φ_t(u) = φ_{t(i)}(u(i))`.
The library's `charFunFdd` (the CF `φ_t`) and `charFunFdd_tendsto_marginal`. -/
abbrev eq_1_2_9 := @DeepWiki.TimeSeries.charFunFdd_tendsto_marginal

/-! ## §1.3 Stationarity and Strict Stationarity -/

/-- **Definition 1.3.1** (§1.3, p.11), the autocovariance function
`γ_X(r,s) = Cov(Xᵣ, Xₛ)` of a process with finite second moments. The library's
`acvf`. -/
noncomputable abbrev def_1_3_1 := @DeepWiki.TimeSeries.acvf

/-- **Definition 1.3.2** (§1.3, p.12), (weak) stationarity: `E|Xₜ|² < ∞`, the mean
`E[Xₜ]` is constant, and `γ_X(r,s) = γ_X(r+t, s+t)`. The library's
`IsWeaklyStationary`. -/
abbrev def_1_3_2 := @DeepWiki.TimeSeries.IsWeaklyStationary

/-- **§1.3, Remark 2 after Definition 1.3.2** (p.12), the **autocorrelation function**
`ρ_X(h) = γ_X(h)/γ_X(0) = Corr(X_{t+h}, Xₜ)` of a stationary process — the lag-`0`-normalized
autocovariance, with `ρ(0) = 1` (`acfStat_zero`) and `|ρ(h)| ≤ 1`
(`IsWeaklyStationary.abs_acfStat_le_one`). The population analogue of the sample autocorrelation
`ρ̂` (`sampleACF`). The library's `acfStat`. -/
noncomputable abbrev acf := @DeepWiki.TimeSeries.acfStat

-- Book-faithful restatement (step 5): `ρ(0) = 1` and `|ρ(h)| ≤ 1` for a stationary process.
example [MeasureTheory.IsProbabilityMeasure μ] (hX : IsWeaklyStationary X μ)
    (h0 : acvfStat X μ 0 ≠ 0) (h : ℤ) : acfStat X μ 0 = 1 ∧ |acfStat X μ h| ≤ 1 :=
  ⟨acfStat_zero h0, hX.abs_acfStat_le_one h⟩

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

omit [MeasurableSpace Ω] in
/-- **Example 1.3.2 connected to §3.1**: the MA(1) process `Xₜ = Zₜ + θ Zₜ₋₁` is exactly the
lag-polynomial moving average `θ(B) Z` with `θ(z) = 1 + θ z` (eqs 3.1.5–3.1.7) — linking the
concrete Example 1.3.2 to the general ARMA/MA difference-equation form (`IsMA`). The library's
`maProcess1_eq_lagPoly`. -/
theorem ex_1_3_2_lagPoly (Zs : ℤ → Ω → ℝ) (θ : ℝ) :
    maProcess1 Zs θ = lagPoly (1 + Polynomial.C θ * Polynomial.X) Zs :=
  maProcess1_eq_lagPoly Zs θ

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

/-- **Definition 1.5.2** (§1.5, p.28–29), the sample autocovariance function
`γ̂(h) = n⁻¹ ∑_{t<n−h} (x_{t+h} − x̄)(xₜ − x̄)` of an observed series `x₀, …, x_{n−1}`,
and the sample autocorrelation function `ρ̂(h) = γ̂(h)/γ̂(0)`. The library's `sampleACVF`
(companion `sampleACF`). -/
noncomputable abbrev def_1_5_2 := @DeepWiki.TimeSeries.sampleACVF

/-! ## §1.6 The Multivariate Normal Distribution -/

/-- **Equation (1.6.1)** (§1.6, p.32), the mean vector `EX = (EX₁, …, EXₙ)ᵀ` of a random
vector `X = (X₁, …, Xₙ)`. The library's `meanVector`. -/
noncomputable abbrev eq_1_6_1 := @DeepWiki.TimeSeries.meanVector

/-- **Equation (1.6.2)** (§1.6, p.32), the covariance matrix `Σ_XX = [Cov(Xᵢ, Xⱼ)]` of a
random vector. The library's `covMatrix`. -/
noncomputable abbrev eq_1_6_2 := @DeepWiki.TimeSeries.covMatrix

open Matrix in
/-- **Proposition 1.6.1** (§1.6, p.33), the linear transform `Y = a + B·X` of a random
vector has mean `EY = a + B·(EX)` (1.6.4) and covariance matrix `Σ_YY = B·Σ_XX·Bᵀ`
(1.6.5). The library's `meanVector_linTransform`, `covMatrix_linTransform`. -/
theorem prop_1_6_1 [MeasureTheory.IsProbabilityMeasure μ] {m n : ℕ} (a : Fin m → ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) {Y : Fin n → Ω → ℝ}
    (hY : ∀ k, MeasureTheory.MemLp (Y k) 2 μ) :
    meanVector (linTransform a B Y) μ = a + B *ᵥ meanVector Y μ ∧
      covMatrix (linTransform a B Y) μ = B * covMatrix Y μ * Bᵀ :=
  ⟨meanVector_linTransform a B fun k => (hY k).integrable (by norm_num),
    covMatrix_linTransform a B hY⟩

/-- **Proposition 1.6.2** (§1.6, p.33), the covariance matrix of a square-integrable
random vector is symmetric and positive semidefinite (`bᵀ Σ b = Var(∑ bᵢ Xᵢ) ≥ 0`).
The library's `posSemidef_covMatrix`. -/
theorem prop_1_6_2 [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ} {Y : Fin n → Ω → ℝ}
    (hY : ∀ i, MeasureTheory.MemLp (Y i) 2 μ) : (covMatrix Y μ).PosSemidef :=
  posSemidef_covMatrix hY

/-- **Proposition 1.6.3** (§1.6, p.33), spectral decomposition: a symmetric (Hermitian)
matrix factors as `Σ = PΛPᵀ` with `P` orthogonal and `Λ = diag(eigenvalues)` (1.6.7) — a
standard matrix-theory result. Mathlib's `Matrix.IsHermitian.spectral_theorem`
(`P = eigenvectorUnitary`, the conjugation `conjStarAlgAut` of `diagonal eigenvalues`). -/
alias prop_1_6_3 := Matrix.IsHermitian.spectral_theorem

/-- **Definition 1.6.1** (§1.6, p.33–34), the multivariate normal distribution `N(μ, Σ)`:
the law of `X = a + BZ` for a standard normal vector `Z` (mean `μ`, covariance matrix `Σ`).
Mathlib's `ProbabilityTheory.multivariateGaussian μ S` on `EuclideanSpace ℝ ι`. -/
noncomputable abbrev def_1_6_1 := @ProbabilityTheory.multivariateGaussian

/-- **Proposition 1.6.4** (§1.6, p.34), the characteristic function of the multivariate
normal `N(μ, Σ)` is `φ_Y(u) = exp(iu'μ − ½ u'Σu)` (1.6.11). Mathlib's
`charFun_multivariateGaussian`. -/
alias prop_1_6_4 := ProbabilityTheory.charFun_multivariateGaussian

/-- **Example 1.6.1** (§1.6, p.35), the bivariate normal distribution: mean `μ` and
covariance matrix `[[σ₁², ρσ₁σ₂], [ρσ₁σ₂, σ₂²]]` (1.6.14, positive semidefinite for
`|ρ| ≤ 1`). It is `multivariateGaussian μ (bivariateCovMatrix σ₁ σ₂ ρ)`; the library's
`bivariateCovMatrix`, `posSemidef_bivariateCovMatrix`. -/
abbrev ex_1_6_1 := @DeepWiki.TimeSeries.bivariateCovMatrix

/-! ## §1.7 Applications of Kolmogorov's Theorem -/

/-- **Definition 1.7.1** (§1.7, p.38), standard Brownian motion `{B(t), t ≥ 0}`: `B(0) = 0`,
independent increments, and `B(t) − B(s) ~ N(0, t − s)` for `t ≥ s` — its existence follows
from Kolmogorov's theorem (Thm 1.2.1). Mathlib's `ProbabilityTheory.IsBrownianReal` (the
conditions, sans continuity, are `IsPreBrownianReal`). -/
abbrev def_1_7_1 := @ProbabilityTheory.IsBrownianReal

/-- **Definition 1.7.2** (§1.7, p.38), Brownian motion with drift: `Y(t) = x + μt + σB(t)`
for a standard Brownian motion `B` (drift `μ`, scale `σ`, initial level `x`). The library's
`brownianWithDrift`. -/
noncomputable abbrev def_1_7_2 := @DeepWiki.TimeSeries.brownianWithDrift

/-- **Definition 1.7.3** (§1.7, p.38), the Poisson process with mean rate `λ`: `N(0) = 0`,
independent increments, and `N(t) − N(s) ~ Poisson(λ(t − s))` for `t ≥ s` — its existence
again follows from Kolmogorov's theorem. The library's `IsPoissonProcess`. -/
abbrev def_1_7_3 := @DeepWiki.TimeSeries.IsPoissonProcess

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

/-- **Problem 1.4** (p.40): a polynomial trend `mₜ = ∑_{j=0}^p cⱼ tʲ` of degree `p` is annihilated
by `p + 1` finite differences — `∇^{p+1} mₜ = 0` — because each difference lowers the degree by one.
Mathlib's `Polynomial.fwdDiff_iter_degree_add_one_eq_zero` states this for the forward difference
`Δ_[1] f = f(·+1) − f(·)` iterated `natDegree + 1` times (`Δ_[1]^[p+1] P.eval = 0`); the book's
backward difference `∇` gives the identical result. -/
alias ex_1_4 := Polynomial.fwdDiff_iter_degree_add_one_eq_zero

/-- **Problem 1.7(b)** (p.40): `Xₜ = a + b·Z` (a single random variable, the same for all
`t`) is weakly stationary, with autocovariance `b²·Var(Z)` at every lag — for `Z ~ N(0,σ²)`
this is mean `a` and autocovariance `b²σ²`. The library's `constProcess`,
`constProcess_isWeaklyStationary`, `constProcess_acvfStat`. -/
theorem ex_1_7_b [IsProbabilityMeasure μ] {a b : ℝ} {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) :
    IsWeaklyStationary (constProcess a b Z) μ ∧
      ∀ h : ℤ, acvfStat (constProcess a b Z) μ h = b ^ 2 * cov[Z, Z; μ] :=
  ⟨constProcess_isWeaklyStationary hZ, fun h => constProcess_acvfStat hZ h⟩

/-- **Problem 1.7(c)** (p.40): `Xₜ = Z₁ cos(ct) + Z₂ sin(ct)` (with `Z₁, Z₂` uncorrelated,
mean `0`, common variance `σ²`) is stationary with `γ(h) = σ² cos(ch)`. It is the cosine
process of Example 1.3.1 — the library's `cosProcess`, `cosProcess_acvf`. -/
theorem ex_1_7_c [IsFiniteMeasure μ] {Z₁ Z₂ : Ω → ℝ} {c σ2 : ℝ}
    (h1 : MemLp Z₁ 2 μ) (h2 : MemLp Z₂ 2 μ) (hv1 : cov[Z₁, Z₁; μ] = σ2)
    (hv2 : cov[Z₂, Z₂; μ] = σ2) (h12 : cov[Z₁, Z₂; μ] = 0) (r s : ℤ) :
    acvf (cosProcess Z₁ Z₂ c) μ r s = σ2 * Real.cos (c * ((r : ℝ) - (s : ℝ))) :=
  cosProcess_acvf h1 h2 hv1 hv2 h12 r s

/-- **Problem 1.7(a)** (p.40): `Xₜ = a + bZₜ + cZₜ₋₂` is stationary with mean `a` and
autocovariance `γ(0) = (b²+c²)σ²`, `γ(±2) = bcσ²`, and `γ(h) = 0` for other lags `≠ 0, ±2`.
The library's `maProcess2`, `maProcess2_acvf_zero`/`_one`/`_two`/`_ge_three`. -/
theorem ex_1_7_a [IsProbabilityMeasure μ] {a b c σ2 : ℝ} {Zs : ℤ → Ω → ℝ}
    (hZ : ∀ i, MeasureTheory.MemLp (Zs i) 2 μ)
    (huc : ∀ i j, cov[Zs i, Zs j; μ] = if i = j then σ2 else 0) (s : ℤ) :
    cov[maProcess2 a b c Zs s, maProcess2 a b c Zs s; μ] = (b ^ 2 + c ^ 2) * σ2 ∧
      cov[maProcess2 a b c Zs (s + 2), maProcess2 a b c Zs s; μ] = b * c * σ2 ∧
      cov[maProcess2 a b c Zs (s + 1), maProcess2 a b c Zs s; μ] = 0 ∧
      (∀ h, 3 ≤ h → cov[maProcess2 a b c Zs (s + h), maProcess2 a b c Zs s; μ] = 0) :=
  ⟨maProcess2_acvf_zero hZ huc s, maProcess2_acvf_two hZ huc s, maProcess2_acvf_one hZ huc s,
    fun h hh => maProcess2_acvf_ge_three hZ huc s h hh⟩

/-- **Problem 1.7(e)** (p.40): `Xₜ = Z·cos(ct)` is **not** (covariance) stationary when
`cos²c ≠ 1` and `Var(Z) > 0`, since its variance `cos²(ct)·Var(Z)` is not constant in `t`.
The library's `cosScaleProcess`, `cosScaleProcess_not_stationary`. -/
theorem ex_1_7_e [IsProbabilityMeasure μ] {c : ℝ} {Z : Ω → ℝ}
    (hc : Real.cos c ^ 2 ≠ 1) (hpos : 0 < cov[Z, Z; μ]) :
    ¬ IsWeaklyStationary (cosScaleProcess c Z) μ :=
  cosScaleProcess_not_stationary hc hpos

/-- **Problem 1.7(d)** (p.40): `Xₜ = Zₜ cos(ct) + Zₜ₋₁ sin(ct)` is **not** (covariance)
stationary in general — although its mean (`0`) and variance (`σ²`) are constant, the lag-1
autocovariance depends on `t`: `Cov(X₁,X₀) = σ² sin c` but `Cov(X₂,X₁) = 2σ² sin c cos²c`,
which differ when `σ² > 0`, `sin c ≠ 0`, and `2 cos²c ≠ 1`. The library's `cosLagProcess`,
`cosLagProcess_not_stationary`. -/
theorem ex_1_7_d [IsProbabilityMeasure μ] {c σ2 : ℝ} {Zs : ℤ → Ω → ℝ}
    (hZ : ∀ i, MemLp (Zs i) 2 μ) (huc : ∀ i j, cov[Zs i, Zs j; μ] = if i = j then σ2 else 0)
    (hσ : 0 < σ2) (hsin : Real.sin c ≠ 0) (hcos : 2 * Real.cos c ^ 2 ≠ 1) :
    ¬ IsWeaklyStationary (cosLagProcess c Zs) μ :=
  cosLagProcess_not_stationary hZ huc hσ hsin hcos

/-! **Problem 1.7(f)** (p.40): `Xₜ = Zₜ·Zₜ₋₁` (the lag product of an iid mean-zero, variance-`σ²`
sequence) is weakly stationary, with mean `0` and autocovariance `γ(0) = σ⁴` and `γ(h) = 0` for
`h ≠ 0`. This is **tractable but deferred** as a laborious mini-project. Establishing the white
covariance `Cov(Xᵢ, Xⱼ) = σ⁴·[i = j]` for all integer lags needs a three-way case split on the
index multiset `{i, i−1, j, j−1}` (the cases `i = j`; one shared index when the lags differ by one;
and four distinct indices otherwise), each grouping the four factors into independent blocks via
`ProbabilityTheory.iIndepFun.indepFun_finset` composed with the product map and
`IndepFun.integral_mul_eq_mul_integral`, together with the `L²` membership of the products `ZₜZₜ₋₁`
(needed for `cov` to be defined). The supporting Mathlib tools all exist; the casework and the
product-integrability bookkeeping are the cost. -/

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

/-- **Problem 1.8(b)** (p.40): `∇_d²` annihilates a linearly modulated period-`d` seasonal
component: `∇_d(∇_d((a + b·t)·sₜ)) = 0` for `{sₜ}` of period `d`. (Hence for
`Xₜ = (a + b·t)·sₜ + Yₜ` with `{Yₜ}` stationary, `∇_d² Xₜ = ∇_d² Yₜ`.) The library's
`seasonalDifference_sq_linear_periodic`. -/
theorem ex_1_8_b {d : ℕ} (a b : ℝ) {s : ℤ → ℝ} (hper : ∀ t : ℤ, s (t + d) = s t) :
    seasonalDifference d (seasonalDifference d (fun t : ℤ => (a + b * (t : ℝ)) * s t)) = 0 :=
  seasonalDifference_sq_linear_periodic a b hper

/-- **Problem 1.11** (p.41): if `{Xₜ}` and `{Yₜ}` are uncorrelated stationary sequences
(`Cov(Xᵣ, Yₛ) = 0` for all `r, s`), then `{Xₜ + Yₜ}` is stationary with autocovariance equal
to the sum of the two autocovariance functions, `γ_{X+Y}(h) = γ_X(h) + γ_Y(h)`. The library's
`IsWeaklyStationary.add_of_uncorrelated`, `acvfStat_add_of_uncorrelated`. -/
theorem ex_1_11 [IsFiniteMeasure μ] {X Y : ℤ → Ω → ℝ}
    (hX : IsWeaklyStationary X μ) (hY : IsWeaklyStationary Y μ)
    (hXY : ∀ r s : ℤ, cov[X r, Y s; μ] = 0) :
    IsWeaklyStationary (fun t ω => X t ω + Y t ω) μ ∧
      ∀ h : ℤ, acvfStat (fun t ω => X t ω + Y t ω) μ h = acvfStat X μ h + acvfStat Y μ h :=
  ⟨hX.add_of_uncorrelated hY hXY,
    fun h => acvfStat_add_of_uncorrelated hX.memLp hY.memLp hXY h⟩

/-- **Problem 1.12(a)** (p.41): the function `κ(0) = 1`, `κ(h) = 1/h` (`h ≠ 0`) is **not** the
autocovariance function of any stationary time series — it is not even (`κ(-1) = -1 ≠ 1 =
κ(1)`), and autocovariance functions must be even (Theorem 1.5.1). The library's `lagRecip`,
`lagRecip_not_even`. -/
theorem ex_1_12_a :
    ¬ (∃ (ν : Measure (ℤ → ℝ)) (X : ℤ → (ℤ → ℝ) → ℝ), IsProbabilityMeasure ν ∧
        IsWeaklyStationary X ν ∧ ∀ h, acvfStat X ν h = lagRecip h) := fun hex =>
  lagRecip_not_even ((isACVF_iff_even_and_isNonnegDefinite lagRecip).mp hex).1

/-- **Problem 1.12(b)** (p.41): the function `κ(h) = (-1)^h` **is** the autocovariance function
of a stationary time series — it is even and non-negative definite (`∑ᵢⱼ aᵢaⱼ(-1)^(tᵢ-tⱼ) =
(∑ᵢ aᵢ(-1)^(tᵢ))² ≥ 0`), so Theorem 1.5.1 constructs a stationary process realizing it. The
library's `neg_one_zpow_even`, `isNonnegDefinite_neg_one_zpow`. -/
theorem ex_1_12_b :
    ∃ (ν : Measure (ℤ → ℝ)) (X : ℤ → (ℤ → ℝ) → ℝ), IsProbabilityMeasure ν ∧
      IsWeaklyStationary X ν ∧ ∀ h, acvfStat X ν h = (-1 : ℝ) ^ h :=
  (isACVF_iff_even_and_isNonnegDefinite (fun h => (-1 : ℝ) ^ h)).mpr
    ⟨neg_one_zpow_even, isNonnegDefinite_neg_one_zpow⟩

/-- **Problem 1.13** (p.41): for the random walk with constant drift `Sₜ = μt + ∑_{i≤t} Xᵢ`
(`S₀ = 0`) of iid increments `Xᵢ` with mean `a` and variance `b`, the **differenced** process
`∇Sₜ = Sₜ − Sₜ₋₁ = μ + Xₜ` is weakly stationary, with mean `μ + a` and autocovariance
`γ(h) = b·[h = 0]`. The increments are white noise (`isWeaklyStationary_of_whiteCov`), and adding
the drift constant `μ` preserves stationarity and the autocovariance (`IsWeaklyStationary.const_add`,
`acvfStat_const_add`). -/
theorem ex_1_13 [IsProbabilityMeasure μ] {Xs : ℤ → Ω → ℝ} {drift a b : ℝ}
    (hmem : ∀ t, MemLp (Xs t) 2 μ) (ha : ∀ t, mean Xs μ t = a)
    (hcov : ∀ i j, cov[Xs i, Xs j; μ] = if i = j then b else 0) :
    IsWeaklyStationary (fun t ω => drift + Xs t ω) μ ∧
      (∀ t, mean (fun t ω => drift + Xs t ω) μ t = drift + a) ∧
      (∀ h, acvfStat (fun t ω => drift + Xs t ω) μ h = if h = 0 then b else 0) := by
  have hstat : IsWeaklyStationary Xs μ :=
    isWeaklyStationary_of_whiteCov hmem (fun s t => (ha s).trans (ha t).symm) hcov
  refine ⟨hstat.const_add drift, fun t => ?_, fun h => ?_⟩
  · rw [mean_const_add hmem drift t, ha t]
  · rw [acvfStat_const_add hmem drift h, acvfStat_apply, hcov h 0]

/-- **Problem 1.15** (p.41): "Prove Proposition 1.6.3" — the spectral decomposition of a
symmetric matrix. This is exactly `prop_1_6_3` (Mathlib's
`Matrix.IsHermitian.spectral_theorem`). -/
alias ex_1_15 := Matrix.IsHermitian.spectral_theorem

/-- **Problem 1.18** (p.41): given any distribution function `F` — equivalently, a probability
law `ν` on `ℝ` — there exists a sequence of independent identically distributed random
variables with common distribution `F`, by Kolmogorov's theorem. The library's
`exists_iidProcess`. -/
theorem ex_1_18 (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℤ → Ω → ℝ),
      (∀ t, Measurable (X t)) ∧ (∀ t, HasLaw (X t) ν P) ∧ iIndepFun X P ∧
        IsProbabilityMeasure P :=
  exists_iidProcess ν

/-- **Problem 1.17** (p.41, forward direction): if the covariance matrix `Σ` of a random
vector `X = (X₁,…,Xₙ)` is singular (`det Σ = 0`), then there is a nonzero vector `b` with
`Var(bᵀX) = 0` — i.e. a nontrivial linear combination `∑ᵢ bᵢ Xᵢ` is almost surely constant
(`bᵀΣb = Var(∑ᵢ bᵢ Xᵢ)`). The converse (a degenerate combination forces `Σ` singular) needs the
fact that a positive-semidefinite quadratic form vanishes only on the matrix kernel — no direct
Mathlib lemma here, deferred. The library's `exists_variance_eq_zero_of_det_eq_zero`. -/
theorem ex_1_17 [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hdet : (covMatrix X μ).det = 0) :
    ∃ b : Fin n → ℝ, b ≠ 0 ∧ variance (fun ω => ∑ i, b i * X i ω) μ = 0 :=
  exists_variance_eq_zero_of_det_eq_zero hX hdet

end DeepWiki.Ts
