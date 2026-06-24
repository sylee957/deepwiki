import DeepWiki.TimeSeries.AsymptoticNormality
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-! # The multivariate delta method (Brockwell–Davis Proposition 6.4.3) — assembly
The delta method `(g(Xₙ) − g(p))/cₙ ⇒ D·V` splits as `D((Xₙ − p)/cₙ) + Rₙ` where `Rₙ` is the Taylor
remainder `(g(Xₙ) − g(p) − D(Xₙ − p))/cₙ`. The linear part converges (continuous mapping), and once the
remainder vanishes in probability, Slutsky (`tendstoInDistribution_of_tendstoInMeasure_sub`) gives the
result. This file establishes the **assembly** with the remainder vanishing taken as a hypothesis; the
remaining ingredient (the remainder is `o_p` from differentiability + tightness) is the deep stochastic
step. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

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

/-- **`o_p · O_p = o_p`**: if `aₙ → 0` in probability and `bₙ` is uniformly tight (for every `ε` there is
a bound `M` with `μ{|bₙ| ≥ M} ≤ ε` for all `n`), then `aₙ · bₙ → 0` in probability. The crux of the Taylor
remainder vanishing in the delta method. -/
theorem tendstoInMeasure_mul_zero_of_tight {a b : ℕ → Ω → ℝ}
    (ha : TendstoInMeasure μ a atTop 0)
    (hb : ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∀ n, μ {ω | M ≤ |b n ω|} ≤ ε) :
    TendstoInMeasure μ (fun n ω => a n ω * b n ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at ha ⊢
  intro η hη
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨M, hM, hMb⟩ := hb (ε / 2) (ENNReal.half_pos hε.ne')
  have hak := (ha (η / M) (by positivity))
  rw [ENNReal.tendsto_nhds_zero] at hak
  filter_upwards [hak (ε / 2) (ENNReal.half_pos hε.ne')] with n hn
  calc μ {ω | η ≤ ‖a n ω * b n ω - 0‖}
      ≤ μ ({ω | M ≤ |b n ω|} ∪ {ω | η / M ≤ ‖a n ω - 0‖}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs, Set.mem_union] at hω ⊢
        by_cases hbM : M ≤ |b n ω|
        · exact Or.inl hbM
        · refine Or.inr ?_
          replace hbM := not_le.mp hbM
          rw [abs_mul] at hω
          rw [div_le_iff₀ hM]
          nlinarith [hω, abs_nonneg (a n ω), abs_nonneg (b n ω),
            mul_nonneg (abs_nonneg (a n ω)) (sub_nonneg.mpr hbM.le)]
    _ ≤ μ {ω | M ≤ |b n ω|} + μ {ω | η / M ≤ ‖a n ω - 0‖} := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hMb n) hn
    _ = ε := ENNReal.add_halves ε

/-- **Continuous mapping in probability at a constant limit** (general metric codomain): if `fₙ → c` in
probability and `h` is continuous at `c`, then `h ∘ fₙ → h c` in probability. The vector-domain analogue of
`tendstoInMeasure_comp_const`. -/
theorem tendstoInMeasure_comp_continuousAt_const {E' F' : Type*} [PseudoMetricSpace E']
    [PseudoMetricSpace F'] {f : ℕ → Ω → E'} {d : E'} {h : E' → F'}
    (hf : TendstoInMeasure μ f atTop (fun _ => d)) (hc : ContinuousAt h d) :
    TendstoInMeasure μ (fun n ω => h (f n ω)) atTop (fun _ => h d) := by
  intro ε hε
  rcases lt_or_ge ε ⊤ with hεlt | hεtop
  · obtain ⟨δ, hδ, hδh⟩ :=
      Metric.continuousAt_iff.mp hc ε.toReal (ENNReal.toReal_pos hε.ne' hεlt.ne)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hf (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)) (fun _ => zero_le) (fun n => measure_mono ?_)
    intro ω hω
    simp only [Set.mem_setOf_eq, edist_dist] at hω ⊢
    rw [ENNReal.ofReal_le_ofReal_iff dist_nonneg]
    by_contra hdd
    rw [not_le] at hdd
    have hcontr := hδh hdd
    rw [← ENNReal.ofReal_toReal hεlt.ne, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hω
    linarith
  · have hεtop' : ε = ⊤ := top_le_iff.mp hεtop
    have hempty : ∀ n : ℕ, {ω | ε ≤ edist (h (f n ω)) (h d)} = ∅ := fun n => by
      ext ω; simp [hεtop', top_le_iff, edist_ne_top]
    simp only [hempty, measure_empty]
    exact tendsto_const_nhds

/-- **The delta-method Taylor remainder vanishes in probability**: if `g` is differentiable at `p` with
derivative `D`, `Xₙ → p` in probability, and the standardized `‖(Xₙ − p)/cₙ‖` is uniformly tight, then the
remainder `(g(Xₙ) − g(p) − D(Xₙ − p))/cₙ → 0` in probability. Indeed `‖remainder‖ = ψ(Xₙ)·‖(Xₙ − p)/cₙ‖`
with `ψ(x) = ‖x − p‖⁻¹·‖g x − g p − D(x − p)‖ →ᵖ 0` (differentiability) and `‖(Xₙ − p)/cₙ‖` tight, so the
`o_p · O_p` product vanishes. -/
theorem tendstoInMeasure_remainder_of_hasFDerivAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X : ℕ → Ω → E} {p : E} {g : E → F} {D : E →L[ℝ] F} {c : ℕ → ℝ}
    (hg : HasFDerivAt g D p) (hXp : TendstoInMeasure μ X atTop (fun _ => p))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∀ n,
      μ {ω | M ≤ |‖(c n)⁻¹ • (X n ω - p)‖|} ≤ ε) :
    TendstoInMeasure μ (fun n ω => (c n)⁻¹ • (g (X n ω) - g p - D (X n ω - p))) atTop 0 := by
  set ψ : E → ℝ := fun x => ‖x - p‖⁻¹ * ‖g x - g p - D (x - p)‖ with hψdef
  have hψp : ψ p = 0 := by simp [hψdef]
  have hψcont : ContinuousAt ψ p := by
    rw [ContinuousAt, hψp]; exact hasFDerivAt_iff_tendsto.mp hg
  have hψX : TendstoInMeasure μ (fun n ω => ψ (X n ω)) atTop (fun _ => (0 : ℝ)) := by
    have h := tendstoInMeasure_comp_continuousAt_const hXp hψcont
    rwa [hψp] at h
  have hprod := tendstoInMeasure_mul_zero_of_tight hψX htight
  rw [tendstoInMeasure_iff_norm] at hprod ⊢
  intro ε hε
  refine (hprod ε hε).congr fun n => ?_
  have halg : ∀ ω, ‖(c n)⁻¹ • (g (X n ω) - g p - D (X n ω - p))‖
      = |ψ (X n ω) * ‖(c n)⁻¹ • (X n ω - p)‖| := fun ω => by
    by_cases hd : X n ω = p
    · simp [hd, hψdef]
    · have hdne : ‖X n ω - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hd)
      simp only [hψdef, norm_smul]
      rw [abs_of_nonneg (by positivity)]
      field_simp
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs, halg ω]

/-- **The multivariate delta method** (Brockwell–Davis Proposition 6.4.3, convergence-in-distribution
form): if `g` is differentiable at `p` with derivative `D`, `Xₙ → p` in probability, the standardized
`(Xₙ − p)/cₙ` converges in distribution to `V`, and `‖(Xₙ − p)/cₙ‖` is uniformly tight, then
`(g(Xₙ) − g(p))/cₙ` converges in distribution to `D V`. The linear part `D((Xₙ − p)/cₙ) ⇒ D V` (continuous
mapping), the Taylor remainder vanishes in probability, and Slutsky combines them. (Tightness is the only
hypothesis not yet derivable from `(Xₙ − p)/cₙ ⇒ V` in Mathlib — Prokhorov.) -/
theorem tendstoInDistribution_smul_comp_of_hasFDerivAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → E}
    {p : E} {g : E → F} {D : E →L[ℝ] F} {c : ℕ → ℝ} {V : Ω' → E} (hg : HasFDerivAt g D p)
    (hXp : TendstoInMeasure μ X atTop (fun _ => p))
    (hconv : TendstoInDistribution (fun n ω => (c n)⁻¹ • (X n ω - p)) atTop V (fun _ => μ) P')
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∀ n,
      μ {ω | M ≤ |‖(c n)⁻¹ • (X n ω - p)‖|} ≤ ε)
    (hg' : ∀ n, AEMeasurable (fun ω => (c n)⁻¹ • (g (X n ω) - g p)) μ) :
    TendstoInDistribution (fun n ω => (c n)⁻¹ • (g (X n ω) - g p)) atTop (fun ω => D (V ω))
      (fun _ => μ) P' := by
  have hcomp := hconv.continuous_comp D.continuous
  simp only [Function.comp_def] at hcomp
  have heq : (fun n ω => D ((c n)⁻¹ • (X n ω - p))) = fun n ω => (c n)⁻¹ • D (X n ω - p) := by
    funext n ω; exact D.map_smul _ _
  rw [heq] at hcomp
  exact tendstoInDistribution_smul_comp_of_tendstoInMeasure_remainder hcomp
    (tendstoInMeasure_remainder_of_hasFDerivAt hg hXp htight) hg'

/-- **Convergence in distribution to a fixed law gives uniform tightness** (the Prokhorov direction, on a
finite-dimensional inner-product space): if `(Xₙ − p)/cₙ ⇒ V`, then `‖(Xₙ − p)/cₙ‖` is uniformly tight —
for every `ε > 0` there is `M > 0` with `μ {‖(Xₙ − p)/cₙ‖ ≥ M} ≤ ε` for all `n`. Via the characteristic-
function tightness criterion (`isTightMeasureSet_of_tendsto_charFun`, Lévy + `continuous_charFun`) and the
norm-tail reading `tendsto_measure_norm_gt_of_isTightMeasureSet`. This discharges the tightness hypothesis
of the multivariate delta method `tendstoInDistribution_smul_comp_of_hasFDerivAt`. -/
theorem tight_of_tendstoInDistribution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure μ] {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → E} {p : E}
    {c : ℕ → ℝ} {V : Ω' → E}
    (hconv : TendstoInDistribution (fun n ω => (c n)⁻¹ • (X n ω - p)) atTop V (fun _ => μ) P') :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∀ n,
      μ {ω | M ≤ |‖(c n)⁻¹ • (X n ω - p)‖|} ≤ ε := by
  set Y : ℕ → Ω → E := fun n ω => (c n)⁻¹ • (X n ω - p) with hY
  set ν : ℕ → Measure E := fun n => μ.map (Y n) with hν
  haveI : ∀ n, IsProbabilityMeasure (ν n) := fun n =>
    Measure.isProbabilityMeasure_map (hconv.forall_aemeasurable n)
  have hchar : ∀ t, Tendsto (fun n => charFun (ν n) t) atTop (𝓝 (charFun (P'.map V) t)) := fun t =>
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hconv.tendsto t
  have htight : IsTightMeasureSet (Set.range ν) :=
    isTightMeasureSet_of_tendsto_charFun continuous_charFun.continuousAt hchar
  have hnorm := tendsto_measure_norm_gt_of_isTightMeasureSet htight
  intro ε hε
  obtain ⟨r, hrε, hr0⟩ :=
    ((hnorm.eventually (gt_mem_nhds hε)).and (eventually_gt_atTop 0)).exists
  refine ⟨r + 1, by linarith, fun n => ?_⟩
  have hmeas : MeasurableSet {x : E | r < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  calc μ {ω | r + 1 ≤ |‖Y n ω‖|}
      ≤ ν n {x : E | r < ‖x‖} := by
        rw [hν, Measure.map_apply_of_aemeasurable (hconv.forall_aemeasurable n) hmeas]
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_setOf_eq, abs_of_nonneg (norm_nonneg _)] at hω
        exact Set.mem_preimage.mpr (by simp only [Set.mem_setOf_eq]; linarith)
    _ ≤ ⨆ ν' ∈ Set.range ν, ν' {x : E | r < ‖x‖} :=
        le_iSup₂ (f := fun ν' (_ : ν' ∈ Set.range ν) => ν' {x : E | r < ‖x‖}) (ν n)
          (Set.mem_range_self n)
    _ ≤ ε := hrε.le

end DeepWiki.TimeSeries
