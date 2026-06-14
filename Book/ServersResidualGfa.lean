import Book.ServersResidualSfa
import Book.ServiceCurveStrictMinimal

/-! # Group-flow analysis (Algorithm 7)
GFA generalizes separated-flow analysis (`Book.ServersResidualSfa`) by
grouping the cross-traffic: at each server `h` on flow `i`'s path it
subtracts not the flat per-flow sum `∑_{j≠i} α_j` but a *grouped*
aggregate `η^(h)` that bounds the other flows' departures — computed
tightly by partitioning flows along the network arcs and exploiting the
servers' shapers (the backward exploration of lines 2-6, and the
shaper-capped output arrival `α_f^(h) = (η_f ⊘ β_f) ∧ σ^(h)` of line 13,
which is exactly `isMaximalArrivalBound_output`). The end-to-end service
curve (line 15) is again the convolution of the per-server blind-mux
residuals `β̃_i = ∗_{h∈p_i} [β^(h) − η^(h)]⁺`, here for an arbitrary valid
grouped aggregate `η`. -/

namespace DeepWiki

open scoped Classical NNReal

/-- **GFA end-to-end service curve**: flow `i` crosses the path of
servers `path`; each server `h` offers its aggregate the strict service
curve `β h`, and flow `i` sees its blind-multiplexing residual against a
grouped cross-traffic aggregate `η h` (any curve bounding the other
flows' departure sum at `h`). The chain of these residual servers offers
flow `i` the convolution `β̃_i = ∗_{h∈path} [β^(h) − η^(h)]⁺↑`. With
`η h = ∑_{j≠i} α_j^(h)` this is separated-flow analysis; a tighter
grouped `η h` is group-flow analysis. -/
theorem isMinimalServiceCurve_concatConv_groupResidual
    {ι κ : Type*} [Fintype ι]
    {S : κ → (ι → Curve) → (ι → Curve) → Prop} {β η : κ → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (β h) (aggregateServer (S h)))
    (path : List κ) :
    IsMinimalServiceCurve
      (concatConv (fun h => liftEReal (residualCurve (β h) (η h))) path)
      (concatComp (fun h => residualServer (fun A D => S h A D ∧
        IsMaximalArrivalBound (fun x => ∑ j ∈ Finset.univ.erase i, (D j) x)
          (η h)) i) path) := by
  apply IsMinimalServiceCurve.concatComp
  · intro _; exact (isNonneg_liftEReal _).isBddBelowReal
  · intro h
    refine (isStrictMinimalServiceCurve_residualServer (hcaus h)
      (hβ h)).isMinimalServiceCurve ?_
    rintro Ai Di ⟨As, Ds, ⟨hp, _⟩, rfl, rfl⟩
    exact hcaus h As Ds hp i

/-! ## Book restatement (group flow analysis)
For a flow `i` crossing a path of servers, each offering a strict service
curve `β^(h)` and seeing flow `i`'s blind-multiplexing residual against a
grouped cross-traffic aggregate `η^(h)`, GFA computes the end-to-end
min-plus service curve `β̃_i = ∗_{h∈p_i} [β^(h) − η^(h)]⁺` — the
convolution of the per-server group residuals. The grouping refines
separated-flow analysis: `η^(h)` is the arrival curve of the *group* of
other flows at `h`, computed by the arc-wise partition (lines 2-6) and
the shaper-capped output arrival `(η ⊘ β) ∧ σ`
(`isMaximalArrivalBound_output`), giving a smaller aggregate than the
flat `∑_{j≠i} α_j` and hence a larger residual. -/
example {ι κ : Type*} [Fintype ι]
    {S : κ → (ι → Curve) → (ι → Curve) → Prop} {β η : κ → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (β h) (aggregateServer (S h)))
    (path : List κ) :
    IsMinimalServiceCurve
      (concatConv (fun h => liftEReal (residualCurve (β h) (η h))) path)
      (concatComp (fun h => residualServer (fun A D => S h A D ∧
        IsMaximalArrivalBound (fun x => ∑ j ∈ Finset.univ.erase i, (D j) x)
          (η h)) i) path) :=
  isMinimalServiceCurve_concatConv_groupResidual hcaus hβ path

end DeepWiki
