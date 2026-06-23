import DeepWiki.TimeSeries.AsymptoticNormality
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! # The multivariate delta method (Brockwell–Davis Proposition 6.4.3) — assembly
The delta method `(g(Xₙ) − g(p))/cₙ ⇒ D·V` splits as `D((Xₙ − p)/cₙ) + Rₙ` where `Rₙ` is the Taylor
remainder `(g(Xₙ) − g(p) − D(Xₙ − p))/cₙ`. The linear part converges (continuous mapping), and once the
remainder vanishes in probability, Slutsky (`tendstoInDistribution_of_tendstoInMeasure_sub`) gives the
result. This file establishes the **assembly** with the remainder vanishing taken as a hypothesis; the
remaining ingredient (the remainder is `o_p` from differentiability + tightness) is the deep stochastic
step. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Delta-method assembly**: if the linearization `D((Xₙ − p)/cₙ)` converges in distribution to `Z` and
the Taylor remainder `(g(Xₙ) − g(p) − D(Xₙ − p))/cₙ` vanishes in probability, then the standardized image
`(g(Xₙ) − g(p))/cₙ` converges in distribution to `Z`. (Slutsky on the linearization.) -/
theorem tendstoInDistribution_smul_comp_of_tendstoInMeasure_remainder {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → E} {p : E} {g : E → F} {D : E →L[ℝ] F}
    {c : ℕ → ℝ} {Z : Ω' → F}
    (hlin : TendstoInDistribution (fun n ω => (c n)⁻¹ • D (X n ω - p)) atTop Z (fun _ => μ) P')
    (hrem : TendstoInMeasure μ (fun n ω => (c n)⁻¹ • (g (X n ω) - g p - D (X n ω - p))) atTop 0)
    (hg : ∀ n, AEMeasurable (fun ω => (c n)⁻¹ • (g (X n ω) - g p)) μ) :
    TendstoInDistribution (fun n ω => (c n)⁻¹ • (g (X n ω) - g p)) atTop Z (fun _ => μ) P' := by
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z hlin ?_ hg
  have hfun : ((fun n ω => (c n)⁻¹ • (g (X n ω) - g p)) - fun n ω => (c n)⁻¹ • D (X n ω - p))
      = fun n ω => (c n)⁻¹ • (g (X n ω) - g p - D (X n ω - p)) := by
    funext n ω
    simp only [Pi.sub_apply, ← smul_sub, sub_sub]
  rw [hfun]
  exact hrem

end DeepWiki.TimeSeries
