import Book.ServersResidualFifoPmoo
import Book.ServersConcatenationChain

/-! # FIFO-PMOO over a tandem
The FIFO-PMOO residual is derived from the FIFO single-server residual
and concatenation: a flow crossing a tandem
of FIFO servers, constrained by `α`, leaves the other flows the residual
`[∗ₕ β^(h) − α ∗ δ_θ]⁺ ∧ δ_θ`. This wires the `n`-server concatenation
(`IsMinimalServiceCurve.concatComp`, the aggregate input/output flowing
through the server chain offers `∗ₕ β^(h)`) into the FIFO-group residual
(`minConv_fifoResidual_le_of_isFifo_group`), realizing the FIFO-PMOO
multiplexing step with the aggregate service curve `β = ∗ₕ β^(h)` made
explicit rather than supplied separately. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Finset

/-- **FIFO-PMOO residual over a tandem**: the flows
of a FIFO tandem cross servers offering min-plus service curves `βE h`,
the aggregate traffic flowing through the server chain `concatComp Sserv
path`. With the tagged flow `k` constrained by `α`, the `m − 1` other
flows together receive the FIFO residual of the concatenation,
`[∗ₕ β^(h) − α ∗ δ_θ]⁺ ∧ δ_θ = fifoResidual (∗ₕ β^(h)) α θ`. -/
theorem minConv_fifoResidual_concatConv_le {ι κ : Type*} [Fintype ι]
    {As Ds : ι → Curve} {Sserv : κ → Curve → Curve → Prop}
    {βE : κ → ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hnn : ∀ h, IsNonneg (βE h)) (path : List κ)
    (hSβ : ∀ h, IsMinimalServiceCurve (βE h) (Sserv h))
    (hagg : concatComp Sserv path (∑ j, As j) (∑ j, Ds j))
    (hβmono : Monotone (Deviation.toENN (concatConv βE path)))
    (hβlc : IsLeftContinuous (Deviation.toENN (concatConv βE path)))
    {k : ι} (harr : IsMaximalArrivalBound ⇑(As k) α) (θ t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(∑ j ∈ univ.erase k, As j))
        (fifoResidual (Deviation.toENN (concatConv βE path))
          (fun v => ((α v : ℝ≥0) : ℝ≥0∞)) θ) t
      ≤ (((∑ j ∈ univ.erase k, Ds j) t : ℝ≥0) : ℝ≥0∞) := by
  have hsc : IsMinimalServiceCurve (concatConv βE path) (concatComp Sserv path) :=
    IsMinimalServiceCurve.concatComp (fun h => (hnn h).isBddBelowReal) hSβ path
  have hserv : ∀ x, minConv (Deviation.liftENN (fun y => ∑ j, (As j) y))
      (Deviation.toENN (concatConv βE path)) x
      ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞) := by
    intro x
    have h := Deviation.minConv_toENN_le_of_isMinimalServiceCurve hsc
      (isNonneg_concatConv hnn path) hagg x
    rwa [Curve.coe_sum, Curve.sum_apply] at h
  exact minConv_fifoResidual_le_of_isFifo_group hfifo hβmono hβlc hserv harr θ t

/-! ## Book restatement (FIFO-PMOO residual)
A sequence of FIFO servers offering min-plus service curves `β^(h)`,
crossed by `m` flows with the tagged flow `k` constrained by the arrival
curve `α`: the aggregate traffic flowing through the concatenation
`concatComp Sserv path` (which offers `∗ₕ β^(h)` by
`IsMinimalServiceCurve.concatComp`), the `m − 1` other flows together
receive the min-plus service curve `[∗ₕ β^(h) − α ∗ δ_θ]⁺ ∧ δ_θ` for
every `θ`. -/
example {ι κ : Type*} [Fintype ι]
    {As Ds : ι → Curve} {Sserv : κ → Curve → Curve → Prop}
    {βE : κ → ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hnn : ∀ h, IsNonneg (βE h)) (path : List κ)
    (hSβ : ∀ h, IsMinimalServiceCurve (βE h) (Sserv h))
    (hagg : concatComp Sserv path (∑ j, As j) (∑ j, Ds j))
    (hβmono : Monotone (Deviation.toENN (concatConv βE path)))
    (hβlc : IsLeftContinuous (Deviation.toENN (concatConv βE path)))
    {k : ι} (harr : IsMaximalArrivalBound ⇑(As k) α) (θ t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(∑ j ∈ univ.erase k, As j))
        (fifoResidual (Deviation.toENN (concatConv βE path))
          (fun v => ((α v : ℝ≥0) : ℝ≥0∞)) θ) t
      ≤ (((∑ j ∈ univ.erase k, Ds j) t : ℝ≥0) : ℝ≥0∞) :=
  minConv_fifoResidual_concatConv_le hfifo hnn path hSβ hagg hβmono hβlc
    harr θ t

end DeepWiki
