import DeepWiki.NetworkCalculus.ServersResidualFifo
import DeepWiki.NetworkCalculus.ArrivalCurvesOutput

/-! # Output arrival curve of a FIFO server (Corollary 7.2)
Composing the FIFO residual θ-family (Theorem 7.5, `minConv_fifoResidual_le_of_isFifo`) with the
deconvolution output bound (Theorem 5.3) per offset `θ`, and taking the infimum over `θ`
(Proposition 5.2, `isMaximalArrivalBound_iInf`): an arrival curve for the *departure* process of
flow `i` of a FIFO server is `⨅_{θ≥0} (α_i ⊘ β_i^θ)`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Deviation

/-- **Corollary 7.2** (arrival curve of the departure function of a FIFO server). A FIFO server
with non-decreasing left-continuous min-plus aggregate `β`, cross arrival curves `αⱼ`, tagged flow
`i` causal (`Dᵢ ≤ Aᵢ`) with input arrival curve `αi`, gives the departure process `Dᵢ` the maximal
arrival curve `⨅_{θ≥0} (αi ⊘ βᵢ^θ)`, where `βᵢ^θ` is the Theorem 7.5 residual. -/
theorem isMaximalArrivalBound_fifoOutput_iInf {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0∞} {α : ι → ℝ≥0 → ℝ≥0} {αi : ℝ≥0 → ℝ≥0∞}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hβmono : Monotone β) (hβlc : IsLeftContinuous β)
    (hserv : ∀ x, minConv (liftENN (fun y => ∑ j, (As j) y)) β x
      ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞))
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j))
    (hcausal : Ds i ≤ As i)
    (harri : IsMaximalArrivalBound (liftENN ⇑(As i)) αi) :
    IsMaximalArrivalBound (liftENN ⇑(Ds i))
      (fun d => ⨅ θ : ℝ≥0, minDeconv αi
        (fifoResidual β (fun v => ((∑ j ∈ Finset.univ.erase i, α j v : ℝ≥0) : ℝ≥0∞)) θ) d) := by
  -- per offset `θ`, the departure of flow `i` allows `αi ⊘ βᵢ^θ`
  have hperθ : ∀ θ : ℝ≥0, IsMaximalArrivalBound (liftENN ⇑(Ds i))
      (minDeconv αi (fifoResidual β
        (fun v => ((∑ j ∈ Finset.univ.erase i, α j v : ℝ≥0) : ℝ≥0∞)) θ)) := by
    intro θ
    set f : ℝ≥0 → ℝ≥0∞ :=
      fifoResidual β (fun v => ((∑ j ∈ Finset.univ.erase i, α j v : ℝ≥0) : ℝ≥0∞)) θ with hf
    set betam : ℝ≥0 → EReal := fun v => ((f v : ℝ≥0∞) : EReal) with hbetam
    have htoenn : toENN betam = f := by funext v; exact EReal.toENNReal_coe
    have hnnm : IsNonneg betam := fun v => EReal.coe_ennreal_nonneg _
    -- the singleton server relating `Aᵢ` to `Dᵢ`
    set S : Curve → Curve → Prop := fun A' D' => A' = As i ∧ D' = Ds i with hS
    have hc : IsCausal S := by rintro A' D' ⟨rfl, rfl⟩; exact hcausal
    have hβm : IsMinimalServiceCurve betam S := by
      rintro A' D' ⟨rfl, rfl⟩ t
      rw [← coe_minConv_toENN (As i) hnnm t, htoenn]
      have hb : minConv (liftENN ⇑(As i)) f t ≤ ((Ds i) t : ℝ≥0∞) := by
        rw [hf]
        exact minConv_fifoResidual_le_of_isFifo hfifo hβmono hβlc hserv harr θ t
      calc ((minConv (liftENN ⇑(As i)) f t : ℝ≥0∞) : EReal)
          ≤ (((Ds i) t : ℝ≥0∞) : EReal) := by exact_mod_cast hb
        _ = curveEReal (Ds i) t := by rw [curveEReal]; rfl
    have hout := isMaximalArrivalBound_output_of_isMinimalServiceCurve hc hβm hnnm
      (A := As i) (D := Ds i) ⟨rfl, rfl⟩ harri
    rwa [htoenn] at hout
  exact isMaximalArrivalBound_iInf hperθ

end DeepWiki
