import Book.ServersResidualGfa

/-! # GFA dominates SFA (the tightness hierarchy)
Separated-flow analysis (`Book.ServersResidualSfa`) subtracts the flat
per-flow sum `∑_{j≠i} α_j` at each server; group-flow analysis
(`Book.ServersResidualGfa`) subtracts a *grouped* aggregate `η` that
bounds the same cross-traffic more tightly, `η^(h) ≤ ∑_{j≠i} α_j^(h)`.
A smaller subtracted aggregate leaves a larger residual at each server
(`residualCurve_le_residualCurve_of_le`), and the convolution fold is
monotone in the per-server curves (`concatConv_mono`), so the GFA
end-to-end service curve dominates the SFA one. This is the curve-level
`SFA ≤ GFA` comparison — the service-curve leg of the book's tightness
ordering: a tighter cross-traffic grouping never weakens — and generally
sharpens — the end-to-end guarantee. (The `TOA ≤ SFA` leg is a delay-bound
fact, the pay-bursts-only-once chain, not a service-curve statement.) -/

namespace DeepWiki

open scoped Classical NNReal

/-- **GFA dominates SFA**: if at every server `h` the grouped aggregate
`η h` bounds the flat cross-traffic sum `∑_{j≠i} α_j^(h)` from below, then
the SFA end-to-end convolution `∗_h [β^(h) − ∑_{j≠i} α_j^(h)]⁺` is
pointwise below the GFA end-to-end convolution `∗_h [β^(h) − η^(h)]⁺` —
the tighter grouping yields the larger (better) service curve. -/
theorem concatConv_residualCurve_sfa_le_gfa
    {ι κ : Type*} [Fintype ι]
    {β : κ → ℝ≥0 → ℝ≥0} {α : κ → ι → ℝ≥0 → ℝ≥0} {η : κ → ℝ≥0 → ℝ≥0} {i : ι}
    (hβ : ∀ h, Monotone (β h))
    (hη : ∀ h v, η h v ≤ ∑ j ∈ Finset.univ.erase i, α h j v)
    (path : List κ) (t : ℝ≥0) :
    concatConv (fun h => liftEReal (residualCurve (β h)
        (fun v => ∑ j ∈ Finset.univ.erase i, α h j v))) path t
      ≤ concatConv (fun h => liftEReal (residualCurve (β h) (η h))) path t := by
  refine concatConv_mono (fun h s => ?_) path t
  exact liftEReal_le_liftEReal
    (fun u => residualCurve_le_residualCurve_of_le (hβ h) (hη h) u) s

/-! ## Book restatement (SFA ≤ GFA service-curve tightness)
Group-flow analysis refines separated-flow analysis: whenever the grouped
cross-traffic aggregate `η^(h)` bounds the flat per-flow sum
`∑_{j≠i} α_j^(h)` from below at every server `h` on flow `i`'s path, the
GFA end-to-end service curve `∗_{h∈p_i} [β^(h) − η^(h)]⁺` dominates the
SFA end-to-end service curve `∗_{h∈p_i} [β^(h) − ∑_{j≠i} α_j^(h)]⁺`. The
residual is antitone in the subtracted aggregate and the path convolution
is monotone in its factors, so a tighter grouping never weakens the
guarantee — the curve-level `SFA ≤ GFA` leg of the book's tightness
ordering. -/
example {ι κ : Type*} [Fintype ι]
    {β : κ → ℝ≥0 → ℝ≥0} {α : κ → ι → ℝ≥0 → ℝ≥0} {η : κ → ℝ≥0 → ℝ≥0} {i : ι}
    (hβ : ∀ h, Monotone (β h))
    (hη : ∀ h v, η h v ≤ ∑ j ∈ Finset.univ.erase i, α h j v)
    (path : List κ) (t : ℝ≥0) :
    concatConv (fun h => liftEReal (residualCurve (β h)
        (fun v => ∑ j ∈ Finset.univ.erase i, α h j v))) path t
      ≤ concatConv (fun h => liftEReal (residualCurve (β h) (η h))) path t :=
  concatConv_residualCurve_sfa_le_gfa hβ hη path t

end DeepWiki
