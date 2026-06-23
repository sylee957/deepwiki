import Mathlib.Probability.Independence.Basic

/-! # m-dependence (Brockwell–Davis Definition 6.4.3)
A process `{Xₜ}` is **m-dependent** if any two finite blocks of the series that are separated by more
than `m` time steps are independent — the past `(Xₛ)_{s ∈ S}` and future `(Xₜ)_{t ∈ T}` are
independent whenever every `s ∈ S` precedes every `t ∈ T` by more than `m`. Finite `MA(q)` processes
are `q`-dependent, and m-dependence is the hypothesis of the §6.4 central limit theorem for dependent
processes. -/

open MeasureTheory ProbabilityTheory

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **m-dependence** (Definition 6.4.3): the process `X` is `m`-dependent under `μ` if for any two
finite index sets `S`, `T` with every element of `S` more than `m` before every element of `T`, the
blocks `(Xₛ)_{s ∈ S}` and `(Xₜ)_{t ∈ T}` are independent. -/
def IsMDependent (m : ℕ) (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ S T : Finset ℤ, (∀ s ∈ S, ∀ t ∈ T, (s : ℤ) + m < t) →
    IndepFun (fun ω (i : S) => X (i : ℤ) ω) (fun ω (i : T) => X (i : ℤ) ω) μ

/-- **m-dependence is monotone in `m`:** an `m`-dependent process is `m'`-dependent for every
`m' ≥ m` (a larger separation requirement is weaker). -/
theorem IsMDependent.mono {m m' : ℕ} {X : ℤ → Ω → ℝ} {μ : Measure Ω} (h : IsMDependent m X μ)
    (hmm : m ≤ m') : IsMDependent m' X μ := by
  intro S T hST
  refine h S T fun s hs t ht => ?_
  have h1 := hST s hs t ht
  have h2 : (m : ℤ) ≤ (m' : ℤ) := by exact_mod_cast hmm
  omega

end DeepWiki.TimeSeries
