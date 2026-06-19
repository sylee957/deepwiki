import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic

/-! # Applications of Kolmogorov's theorem (§1.7)
Brownian motion with drift (Def 1.7.2) and the Poisson process (Def 1.7.3). Standard
Brownian motion (Def 1.7.1) is Mathlib's `ProbabilityTheory.IsBrownianReal`; the existence
of both processes follows from Kolmogorov's theorem (Thm 1.2.1). -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Definition 1.7.2**: Brownian motion with drift `μ`, scale `σ`, and initial level `x`:
`Y(t) = x + μ·t + σ·B(t)` for a standard Brownian motion `B`. -/
noncomputable def brownianWithDrift (x μ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => x + μ * (t : ℝ) + σ * B t ω

/-- **Definition 1.7.3**: a Poisson process with rate `λ` — `N(0) = 0`, with independent
increments over disjoint intervals, and `N(t) − N(s) ~ Poisson(λ(t−s))` for `s ≤ t`. -/
structure IsPoissonProcess (N : ℝ≥0 → Ω → ℕ) (lam : ℝ≥0) (P : Measure Ω) : Prop where
  /-- The process starts at `0`. -/
  zero : ∀ ω, N 0 ω = 0
  /-- The increment over `[s, t]` is Poisson with mean `λ(t − s)`. -/
  hasLaw_increment : ∀ s t : ℝ≥0, s ≤ t →
    HasLaw (fun ω => N t ω - N s ω) (poissonMeasure (lam * (t - s))) P
  /-- Increments over consecutive intervals of any time mesh are independent. -/
  indep_increments : ∀ {n : ℕ} (t : Fin (n + 1) → ℝ≥0), StrictMono t →
    iIndepFun (fun i : Fin n => fun ω => N (t i.succ) ω - N (t i.castSucc) ω) P

end DeepWiki.TimeSeries
