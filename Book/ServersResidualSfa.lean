import Book.ServersConcatenationChain
import Book.ServersResidual

/-! # Separated-flow analysis (SFA)
SFA computes an end-to-end min-plus service curve for one flow `i`
crossing a path of servers. At each server `h` on the path it isolates a
residual service curve `β_i^(h) = [β^(h) − ∑_{j≠i} α_j^(h)]⁺` by blind
multiplexing (`isMinimalServiceCurve_residualServer`), where `α_j^(h)` is
flow `j`'s arrival curve at `h`; the flow then crosses the chain of these
residual servers, so by the `n`-server concatenation
(`IsMinimalServiceCurve.concatComp`) it is offered the convolution
`β̃_i = ∗_{h∈p_i} β_i^(h)`. This is the global service curve of the SFA
pseudocode's line 9, assembled from the per-server residuals of lines 6-7. -/

namespace DeepWiki

open scoped Classical NNReal

/-- **SFA end-to-end service curve**: flow `i` crosses the path of
servers `path`; each server `h` offers its aggregate the strict service
curve `β h`, and flow `i` sees its blind-multiplexing residual against
the other flows' arrival curves `α h j`. The chain of these residual
servers offers flow `i` the convolution of the per-server residuals,
`β̃_i = ∗_{h∈path} [β^(h) − ∑_{j≠i} α_j^(h)]⁺↑`. -/
theorem isMinimalServiceCurve_concatConv_residualServer
    {ι κ : Type*} [Fintype ι]
    {S : κ → (ι → Curve) → (ι → Curve) → Prop} {β : κ → ℝ≥0 → ℝ≥0}
    {α : κ → ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (β h) (aggregateServer (S h)))
    (path : List κ) :
    IsMinimalServiceCurve
      (concatConv (fun h => liftEReal (residualCurve (β h)
        (fun v => ∑ j ∈ Finset.univ.erase i, α h j v))) path)
      (concatComp (fun h => residualServer (fun A D => S h A D ∧
        ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(A j) (α h j)) i) path) :=
  IsMinimalServiceCurve.concatComp
    (fun _ => (isNonneg_liftEReal _).isBddBelowReal)
    (fun h => isMinimalServiceCurve_residualServer (hcaus h) (hβ h)) path

/-! ## Book restatement (separated flow analysis)
For a flow `i` crossing a path of servers, each offering a strict service
curve `β^(h)` to its aggregate and seeing flow `i`'s blind-multiplexing
residual against the other flows' arrival curves `α_j^(h)`, SFA computes
the end-to-end min-plus service curve
`β̃_i = ∗_{h∈p_i} [β^(h) − ∑_{j≠i} α_j^(h)]⁺` — the convolution of the
per-server residual service curves along the path. -/
example {ι κ : Type*} [Fintype ι]
    {S : κ → (ι → Curve) → (ι → Curve) → Prop} {β : κ → ℝ≥0 → ℝ≥0}
    {α : κ → ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (β h) (aggregateServer (S h)))
    (path : List κ) :
    IsMinimalServiceCurve
      (concatConv (fun h => liftEReal (residualCurve (β h)
        (fun v => ∑ j ∈ Finset.univ.erase i, α h j v))) path)
      (concatComp (fun h => residualServer (fun A D => S h A D ∧
        ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(A j) (α h j)) i) path) :=
  isMinimalServiceCurve_concatConv_residualServer hcaus hβ path

end DeepWiki
