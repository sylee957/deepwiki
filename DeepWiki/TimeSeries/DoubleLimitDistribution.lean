import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Lévy–Prokhorov bound from convergence in measure
The technical heart of the **double-limit theorem** for convergence in distribution
(Billingsley, *Convergence of Probability Measures*, Theorem 3.2): if two random variables are
close *in measure*, their laws are close in the **Lévy–Prokhorov metric**. Concretely
`levyProkhorovEDist (μ.map X) (μ.map Y) ≤ ofReal r ⊔ μ{ω | r ≤ dist (X ω) (Y ω)}`, from the set
inclusion `{X ∈ B} ⊆ {Y ∈ thickening_r B} ∪ {dist (X,Y) ≥ r}`. This is the estimate that lets a
sequence of approximating processes (e.g. the finite `MA(q)` truncations of a linear process)
control the law of the limiting process. -/

open MeasureTheory Filter Metric Set
open scoped Topology ENNReal NNReal

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **In-measure ⟹ Lévy–Prokhorov bound:** for measurable `X, Y` into a metric space and `r > 0`,
the Lévy–Prokhorov edistance of their laws is bounded by `ofReal r ⊔ μ{ω | r ≤ dist (X ω) (Y ω)}`.
The set inclusion `{X ∈ B} ⊆ {Y ∈ thickening_ε B} ∪ {dist (X,Y) ≥ r}` (with `r ≤ ε`) makes each
of the two Lévy–Prokhorov defining inequalities hold. -/
theorem levyProkhorovEDist_map_le {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y) {r : ℝ}
    (hr : 0 < r) :
    levyProkhorovEDist (μ.map X) (μ.map Y)
      ≤ ENNReal.ofReal r ⊔ μ {ω | r ≤ dist (X ω) (Y ω)} := by
  set p : ℝ≥0∞ := μ {ω | r ≤ dist (X ω) (Y ω)} with hp
  refine levyProkhorovEDist_le_of_forall _ _ _ (fun ε B hδε hεtop hB => ?_)
  have hrε : r ≤ ε.toReal := by
    have hofr : ENNReal.ofReal r ≤ ε := le_of_lt (lt_of_le_of_lt le_sup_left hδε)
    calc r = (ENNReal.ofReal r).toReal := (ENNReal.toReal_ofReal hr.le).symm
      _ ≤ ε.toReal := ENNReal.toReal_mono hεtop.ne hofr
  have hpε : p ≤ ε := le_of_lt (lt_of_le_of_lt le_sup_right hδε)
  -- generic one-sided bound: `μ(U⁻¹B) ≤ μ(V⁻¹ thickening) + μ{dist (U,V) ≥ r}`
  have one_side : ∀ (U V : Ω → E), Measurable U → Measurable V →
      (μ.map U) B ≤ (μ.map V) (thickening ε.toReal B) + μ {ω | r ≤ dist (U ω) (V ω)} := by
    intro U V hU hV
    rw [Measure.map_apply hU hB, Measure.map_apply hV isOpen_thickening.measurableSet]
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    rw [Set.mem_preimage] at hω
    by_cases hd : r ≤ dist (U ω) (V ω)
    · exact Or.inr hd
    · refine Or.inl ?_
      rw [Set.mem_preimage]
      refine mem_thickening_iff.mpr ⟨U ω, hω, ?_⟩
      rw [dist_comm]
      exact lt_of_lt_of_le (not_le.mp hd) hrε
  refine ⟨le_trans (one_side X Y hX hY) (add_le_add le_rfl hpε), ?_⟩
  refine le_trans (one_side Y X hY hX) ?_
  have hsymm : μ {ω | r ≤ dist (Y ω) (X ω)} = p := by
    rw [hp]; congr 1; ext ω; simp only [Set.mem_setOf_eq, dist_comm]
  rw [hsymm]
  exact add_le_add le_rfl hpε

/-- **Convergence in distribution ⟹ Lévy–Prokhorov distance of laws tends to `0`** (separable
codomain): the abstract weak convergence `TendstoInDistribution` of `X` to `Z` is, via the
metrization homeomorphism `probabilityMeasureHomeomorph`, the metric statement that
`levyProkhorovDist (law (X i)) (law Z) → 0`. The workable metric form of convergence in
distribution. -/
theorem tendsto_levyProkhorovDist_of_tendstoInDistribution
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E]
    {ι : Type*} {l : Filter ι} {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀}
    [IsProbabilityMeasure ν] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {X : ι → Ω₀ → E} {Z : Ω' → E}
    (h : TendstoInDistribution X l Z (fun _ => ν) μ') :
    Tendsto (fun i => levyProkhorovDist (ν.map (X i)) (μ'.map Z)) l (𝓝 0) := by
  have hc := ((LevyProkhorov.probabilityMeasureHomeomorph (Ω := E)).continuous.tendsto _).comp
    h.tendsto
  rw [tendsto_iff_dist_tendsto_zero] at hc
  refine hc.congr (fun i => ?_)
  rw [Function.comp_apply, LevyProkhorov.dist_probabilityMeasure_def]
  rfl

/-- **Lévy–Prokhorov distance of laws tends to `0` ⟹ convergence in distribution** (separable
codomain), the converse of `tendsto_levyProkhorovDist_of_tendstoInDistribution`. Given measurability
of the variables, `levyProkhorovDist (law (X i)) (law Z) → 0` rebuilds the abstract
`TendstoInDistribution`. The exit from the metric form back to weak convergence. -/
theorem tendstoInDistribution_of_tendsto_levyProkhorovDist
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E]
    {ι : Type*} {l : Filter ι} {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀}
    [IsProbabilityMeasure ν] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {X : ι → Ω₀ → E} {Z : Ω' → E}
    (hX : ∀ i, AEMeasurable (X i) ν) (hZ : AEMeasurable Z μ')
    (h : Tendsto (fun i => levyProkhorovDist (ν.map (X i)) (μ'.map Z)) l (𝓝 0)) :
    TendstoInDistribution X l Z (fun _ => ν) μ' := by
  refine ⟨hX, hZ, ?_⟩
  rw [(LevyProkhorov.probabilityMeasureHomeomorph (Ω := E)).isEmbedding.tendsto_nhds_iff,
    tendsto_iff_dist_tendsto_zero]
  refine h.congr (fun i => ?_)
  rw [Function.comp_apply, LevyProkhorov.dist_probabilityMeasure_def]
  rfl
