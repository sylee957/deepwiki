import DeepWiki.TimeSeries.MultivariateCLT
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # The delta method (Brockwell–Davis Example 6.4.2)
The one-dimensional delta method: if `√n (Xₙ − μ)` is asymptotically normal and `Xₙ →ᵖ μ`, then for
`g` differentiable at `μ`, `√n (g Xₙ − g μ)` is asymptotically normal with the derivative-scaled
limit `g'(μ) · Y₀`. Proved without tightness, via the slope decomposition
`√n (g Xₙ − g μ) = slope(Xₙ) · √n (Xₙ − μ)` (Slutsky's product theorem, the slope tending in measure
to `g'(μ)`). The §6.4 inference engine for smooth functionals of asymptotically normal estimators
(e.g. the sample autocorrelation `ρ̂ = γ̂(h)/γ̂(0)` in Bartlett's formula). -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Continuous mapping for convergence in measure to a constant:** if `fₙ →ᵖ c` and `h` is
continuous at `c`, then `h ∘ fₙ →ᵖ h c`. The set `{|h(fₙ) − h c| ≥ ε}` is contained in
`{|fₙ − c| ≥ δ}` for the continuity modulus `δ`, whose measure vanishes. -/
theorem tendstoInMeasure_comp_const {f : ℕ → Ω → ℝ} {c : ℝ} {h : ℝ → ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => c)) (hc : ContinuousAt h c) :
    TendstoInMeasure μ (fun n ω => h (f n ω)) atTop (fun _ => h c) := by
  intro ε hε
  rcases lt_or_ge ε ⊤ with hεlt | hεtop
  · obtain ⟨δ, hδ, hδh⟩ :=
      Metric.continuousAt_iff.mp hc ε.toReal (ENNReal.toReal_pos hε.ne' hεlt.ne)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hf (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)) (fun _ => zero_le) (fun n => measure_mono ?_)
    intro ω hω
    simp only [Set.mem_setOf_eq, edist_dist] at hω ⊢
    rw [ENNReal.ofReal_le_ofReal_iff dist_nonneg]
    by_contra hd
    rw [not_le] at hd
    have hcontr := hδh hd
    rw [← ENNReal.ofReal_toReal hεlt.ne, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hω
    linarith
  · have hεtop' : ε = ⊤ := top_le_iff.mp hεtop
    have hempty : ∀ n : ℕ, {ω | ε ≤ edist (h (f n ω)) (h c)} = ∅ := fun n => by
      ext ω; simp [hεtop', top_le_iff, edist_ne_top]
    simp only [hempty, measure_empty]
    exact tendsto_const_nhds

/-- **The (one-dimensional) delta method** (Brockwell–Davis Example 6.4.2): if `Xₙ →ᵖ a`, the
standardized `√n (Xₙ − a)` converges in distribution to `Y₀`, and `g` is (measurable and)
differentiable at `a` with derivative `g'`, then `√n (g Xₙ − g a) ⇒ g' · Y₀`. Via the slope
decomposition `√n (g Xₙ − g a) = s(Xₙ)·√n (Xₙ − a)` with `s` the derivative-patched difference
quotient (`s(Xₙ) →ᵖ g'` by `tendstoInMeasure_comp_const`), fed through Slutsky's product theorem.
With `Y₀ ~ N(0, σ²)` the limit `g' · Y₀ ~ N(0, g'² σ²)` (`gaussianReal_const_mul`). -/
theorem delta_method [IsProbabilityMeasure μ] {a g' : ℝ} {g : ℝ → ℝ} (hderiv : HasDerivAt g g' a)
    (hgm : Measurable g) {X : ℕ → Ω → ℝ} (hXm : ∀ n, AEMeasurable (X n) μ)
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Y₀ : Ω' → ℝ}
    (hcons : TendstoInMeasure μ X atTop (fun _ => a))
    (hnorm : TendstoInDistribution (fun (n : ℕ) ω => √n * (X n ω - a)) atTop Y₀ (fun _ => μ) μ') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (g (X n ω) - g a)) atTop (fun ω => g' * Y₀ ω)
      (fun _ => μ) μ' := by
  classical
  have hslope : Measurable (slope g a) := by
    rw [slope_fun_def_field]; exact (hgm.sub_const _).div (measurable_id.sub_const _)
  set s : ℝ → ℝ := Function.update (slope g a) a g' with hs
  have hsa : s a = g' := Function.update_self a g' (slope g a)
  have hsm : Measurable s := by
    have hse : s = fun x => if x = a then g' else slope g a x :=
      funext fun x => by rw [hs, Function.update_apply]
    rw [hse]
    exact Measurable.ite (measurableSet_singleton a) measurable_const hslope
  have hs_cont : ContinuousAt s a :=
    continuousAt_update_same.mpr (hasDerivAt_iff_tendsto_slope.mp hderiv)
  have hs_tendsto : TendstoInMeasure μ (fun n ω => s (X n ω)) atTop (fun _ => g') := by
    have h := tendstoInMeasure_comp_const hcons hs_cont
    rwa [hsa] at h
  have hs_aem : ∀ n, AEMeasurable (fun ω => s (X n ω)) μ := fun n => hsm.comp_aemeasurable (hXm n)
  have halg : ∀ (n : ℕ) (ω : Ω), √n * (g (X n ω) - g a) = s (X n ω) * (√n * (X n ω - a)) := by
    intro n ω
    by_cases h : X n ω = a
    · rw [h, hsa]; ring
    · rw [hs, Function.update_of_ne h, slope_def_field]; field_simp
  refine (TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
    (by fun_prop : Continuous fun p : ℝ × ℝ => p.2 * p.1) hnorm hs_tendsto hs_aem).congr
    (fun n => Filter.Eventually.of_forall fun ω => (halg n ω).symm)
    (Filter.Eventually.of_forall fun _ => rfl)

/-- **Slutsky's theorem for ratios:** if `Aₙ` converges in distribution to `Z` and `Bₙ →ᵖ b` with
`b ≠ 0`, then `Aₙ / Bₙ ⇒ Z / b`. Via `Bₙ⁻¹ →ᵖ b⁻¹` (continuous mapping of the inverse at `b ≠ 0`,
`tendstoInMeasure_comp_const`) and Slutsky's product theorem. The tool behind the asymptotic
distribution of the sample autocorrelation `ρ̂(h) = γ̂(h)/γ̂(0)` (Bartlett's formula). -/
theorem tendstoInDistribution_div_of_tendstoInMeasure_const [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {A B : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {b : ℝ} (hb : b ≠ 0)
    (hA : TendstoInDistribution A atTop Z (fun _ => μ) μ')
    (hB : TendstoInMeasure μ B atTop (fun _ => b)) (hBm : ∀ n, AEMeasurable (B n) μ) :
    TendstoInDistribution (fun n ω => A n ω / B n ω) atTop (fun ω => Z ω / b) (fun _ => μ) μ' := by
  have hinv : TendstoInMeasure μ (fun n ω => (B n ω)⁻¹) atTop (fun _ => b⁻¹) :=
    tendstoInMeasure_comp_const hB (continuousAt_inv₀ hb)
  refine (TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
    (by fun_prop : Continuous fun p : ℝ × ℝ => p.1 * p.2) hA hinv
    (fun n => (hBm n).inv)).congr
    (fun n => Filter.Eventually.of_forall fun ω => (div_eq_mul_inv _ _).symm)
    (Filter.Eventually.of_forall fun ω => (div_eq_mul_inv _ _).symm)

/-- **Scalar convergence lifts to convergence in distribution of the scaled variable:** if `cₙ → c₀`
then `cₙ • Y₀ ⇒ c₀ • Y₀` in distribution. The `Wₘ ⇒ Z` ingredient whenever a family of Gaussian (or
other) limits is a converging scalar multiple of one base variable — used in the double-limit CLT
assembly (the truncation limits `(∑_{j≤m} ψⱼ) Y₀ → (∑ψ) Y₀`) and scaling Slutsky arguments. -/
theorem tendstoInDistribution_const_smul_of_tendsto {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {c : ℕ → ℝ} {c₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) {Y₀ : Ω' → ℝ} (hY₀ : AEMeasurable Y₀ μ') :
    TendstoInDistribution (fun (n : ℕ) ω => c n • Y₀ ω) atTop (fun ω => c₀ • Y₀ ω)
      (fun _ => μ') μ' :=
  tendstoInDistribution_of_ae_tendsto (fun n => hY₀.const_smul (c n)) (hY₀.const_smul c₀)
    (Filter.Eventually.of_forall fun ω => hc.smul_const (Y₀ ω))

end DeepWiki.TimeSeries
