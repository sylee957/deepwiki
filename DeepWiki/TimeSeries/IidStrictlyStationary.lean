import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.IdentDistrib

/-! # An i.i.d. sequence is strictly stationary
A sequence of independent, identically distributed random variables is strictly stationary: its full
joint distribution is the infinite product of the (identical) marginal, which is invariant under the
index shift. This supplies the strict-stationarity hypothesis of the `m`-dependent CLT for genuinely
i.i.d. (rather than merely strictly-stationary) noise, closing the moving-average CLT for white noise. -/

open MeasureTheory ProbabilityTheory

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **An i.i.d. sequence is strictly stationary**: the process law `μ.map (ω ↦ (Zₐ ω)ₐ)` is the infinite
product `infinitePi` of the common marginal (`iIndepFun.map_fun_eq_infinitePi_map` + identical
distributions), which is invariant under the index shift `a ↦ a + h` (`infinitePi_map_piCongrLeft` for
the shift equiv, the constant marginals absorbing the reindex); evaluating at `t` resp. `t + h` then
gives equal finite joint laws (`Measure.map_map`). -/
theorem iIndepFun.isStrictlyStationary [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hindep : iIndepFun Z μ) (hmeas : ∀ t, Measurable (Z t))
    (hident : ∀ t, IdentDistrib (Z t) (Z 0) μ μ) : IsStrictlyStationary Z μ := by
  intro k t h
  have hPmeas : Measurable (fun ω a => Z a ω) := measurable_pi_lambda _ hmeas
  have hP : μ.map (fun ω a => Z a ω) = Measure.infinitePi (fun _ : ℤ => μ.map (Z 0)) := by
    rw [hindep.map_fun_eq_infinitePi_map hmeas]
    exact congrArg Measure.infinitePi (funext fun a => (hident a).map_eq)
  set e : ℤ ≃ ℤ := Equiv.addRight (-h) with he
  have hpc : Measurable (MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℝ) e) :=
    (MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℝ) e).measurable
  have hevt : Measurable (fun w : ℤ → ℝ => fun i : Fin k => w (t i)) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hpc_eq : ∀ (w : ℤ → ℝ) (a : ℤ),
      (MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℝ) e) w a = w (a + h) := by
    intro w a
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    simp [he, Equiv.addRight]
  haveI : IsProbabilityMeasure (μ.map (Z 0)) :=
    Measure.isProbabilityMeasure_map (hmeas 0).aemeasurable
  have hshift : (μ.map (fun ω a => Z a ω)).map (MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℝ) e)
      = μ.map (fun ω a => Z a ω) := by
    rw [hP]; exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : ℤ => μ.map (Z 0)) e
  have hL : μ.map (fun ω (i : Fin k) => Z (t i) ω)
      = (μ.map (fun ω a => Z a ω)).map (fun w : ℤ → ℝ => fun i : Fin k => w (t i)) :=
    (Measure.map_map hevt hPmeas).symm
  have hR : μ.map (fun ω (i : Fin k) => Z (t i + h) ω)
      = ((μ.map (fun ω a => Z a ω)).map (MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℝ) e)).map
        (fun w : ℤ → ℝ => fun i : Fin k => w (t i)) := by
    rw [Measure.map_map hevt hpc, Measure.map_map (hevt.comp hpc) hPmeas]
    congr 1
    funext ω i
    simp only [Function.comp_apply, hpc_eq]
  rw [hL, hR, hshift]

end DeepWiki.TimeSeries
