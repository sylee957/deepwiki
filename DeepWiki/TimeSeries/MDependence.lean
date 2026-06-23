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

/-- **An i.i.d. sequence is `0`-dependent**: a mutually independent family `Z` is `0`-dependent —
finite index blocks separated by more than `0` (i.e. disjoint) give independent tuples. The base case
of `m`-dependence (here `X = Z`, so the blocks are the `Z`-tuples and `iIndepFun.indepFun_finset`
applies directly). -/
theorem isMDependent_zero_of_iIndepFun {Z : ℤ → Ω → ℝ} {μ : Measure Ω} (hindep : iIndepFun Z μ)
    (hmeas : ∀ i, Measurable (Z i)) : IsMDependent 0 Z μ := by
  intro S T hST
  refine iIndepFun.indepFun_finset S T ?_ hindep hmeas
  rw [Finset.disjoint_left]
  intro a haS haT
  have h := hST a haS a haT
  omega

/-- **An i.i.d. sequence is `m`-dependent for every `m`**: from `0`-dependence
(`isMDependent_zero_of_iIndepFun`) and monotonicity (`IsMDependent.mono`). -/
theorem isMDependent_of_iIndepFun {Z : ℤ → Ω → ℝ} {μ : Measure Ω} (hindep : iIndepFun Z μ)
    (hmeas : ∀ i, Measurable (Z i)) (m : ℕ) : IsMDependent m Z μ :=
  (isMDependent_zero_of_iIndepFun hindep hmeas).mono (Nat.zero_le m)

/-- **m-dependence transports through a pointwise measurable map**: if `X` is `m`-dependent and
`g : ℝ → ℝ` is measurable, then the pointwise image `t ↦ g ∘ Xₜ` is `m`-dependent (each block composes
with `g` coordinatewise, preserving block independence). So `|X|`, `X²`, and centerings `X − c` of an
`m`-dependent process are again `m`-dependent. -/
theorem IsMDependent.comp {m : ℕ} {X : ℤ → Ω → ℝ} {μ : Measure Ω} (h : IsMDependent m X μ)
    {g : ℝ → ℝ} (hg : Measurable g) : IsMDependent m (fun t ω => g (X t ω)) μ := by
  intro S T hST
  exact (h S T hST).comp (φ := fun v i => g (v i)) (ψ := fun v i => g (v i))
    (measurable_pi_lambda _ fun i => by fun_prop) (measurable_pi_lambda _ fun i => by fun_prop)

/-- **m-dependence at the singleton level**: if `s + m < t` then `Xₛ` and `Xₜ` are independent
(the two-point case of `m`-dependence, extracting the values from the singleton blocks). -/
theorem IsMDependent.indepFun {m : ℕ} {X : ℤ → Ω → ℝ} {μ : Measure Ω} (h : IsMDependent m X μ)
    {s t : ℤ} (hst : s + (m : ℤ) < t) : IndepFun (X s) (X t) μ := by
  have hb := h {s} {t} (fun a ha b hb => by
    rw [Finset.mem_singleton] at ha hb; subst ha; subst hb; exact hst)
  exact hb.comp (measurable_pi_apply ⟨s, Finset.mem_singleton_self s⟩)
    (measurable_pi_apply ⟨t, Finset.mem_singleton_self t⟩)

end DeepWiki.TimeSeries
