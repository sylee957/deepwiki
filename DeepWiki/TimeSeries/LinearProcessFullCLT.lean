import DeepWiki.TimeSeries.GeneralLinearProcessCLT
import DeepWiki.TimeSeries.LinearProcessCLT
import DeepWiki.TimeSeries.DoubleLimitDistribution

/-! # Sample-mean CLT for the causal linear process under `∑ⱼ |ψⱼ| < ∞`
Assembling the full Theorem 7.1.2 (Brockwell–Davis): for a causal linear process
`Xₜ = ∑_{j≥0} ψⱼ Z_{t−j}` over centered iid `L²` noise with only `∑ⱼ |ψⱼ| < ∞`, the sample mean is
asymptotically normal, `√n X̄ₙ ⇒ (∑ψ) Y₀`. The route: finite `MA(m)` truncations converge
(`causalLinearProcess_sampleMean_clt`), their limits converge (scalars `sₘ → ∑ψ`), and the
truncation error is uniformly small in `L²` — `‖√n(X̄ₙ − X̄ₙ^{(m)})‖₂ ≤ σ·∑_{j>m}|ψⱼ| → 0` by iid
orthogonality — so the **double-limit theorem** `tendstoInDistribution_of_eventually_approx` applies. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **iid centered `L²` noise satisfies the white-noise moment condition** `∫ Zₐ·Z_b = σ²·[a=b]`
with `σ² = ∫ Z₀²`: off-diagonal terms vanish by independence (`∫ Zₐ Z_b = μ[Zₐ]·μ[Z_b] = 0`,
centered), diagonal terms are the common second moment (`IdentDistrib`). The hypothesis
`inner_toLpSeq` consumes to make the lagged `L²` vectors orthogonal. -/
theorem integral_mul_eq_iid [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hmem : ∀ t, MemLp (Z t) 2 μ) (hindep : iIndepFun Z μ)
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ) (hcenter : μ[Z 0] = 0) (a b : ℤ) :
    ∫ ω, Z a ω * Z b ω ∂μ = if a = b then (∫ ω, Z 0 ω * Z 0 ω ∂μ) else 0 := by
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl]
    exact ((hident a).comp (show Measurable (fun x : ℝ => x * x) by fun_prop)).integral_eq
  · rw [if_neg hab]
    rw [(hindep.indepFun hab).integral_fun_mul_eq_mul_integral (hmem a).1 (hmem b).1]
    have haz : ∫ ω, Z a ω ∂μ = 0 := (hident a).integral_eq.trans hcenter
    rw [haz, zero_mul]

end DeepWiki.TimeSeries
