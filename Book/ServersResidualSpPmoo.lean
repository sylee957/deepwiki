import Book.ServersResidualGfa
import Book.ServersResidualPriority

/-! # Static-priority PMOO
For static-priority multiplexing, flow `i`'s residual at a server is the
priority residual `[β^(h) − ∑_{j<i} α_j^(h)]⁺` — only the higher-priority
flows `j < i` preempt it (`isStrictMinimalServiceCurve_residualServer_of_isStaticPriority`).
Concatenating these per-server residuals along flow `i`'s path gives the
end-to-end service curve `β̃_i = ∗_{h∈p_i} [β^(h) − ∑_{j<i} α_j^(h)]⁺`
(`IsMinimalServiceCurve.concatComp`). The full SP-PMOO algorithm sharpens
this on *nested* tandems by paying the multiplexing only once — the
recursion `β̃_i = (∗_{h∈N(i)} β^(h)) ∗ (∗_{j∈PF(i)} [β̃_j − α_j]⁺)` over the
nesting order — whose correctness is proof-external in the book [BOU 09];
the per-server-residual concatenation formalized here is its building block
(and the exact result when the paths are not nested). -/

namespace DeepWiki

open scoped Classical NNReal

/-- **Static-priority PMOO end-to-end service curve**: flow `i` crosses
the path of servers `path`; each server `h` offers its aggregate the
left-continuous strict service curve `β h` under a static-priority policy,
and flow `i` sees the priority residual against the higher-priority flows
`j < i`. The chain of these residual servers offers flow `i` the
convolution `β̃_i = ∗_{h∈path} [β^(h) − ∑_{j<i} α_j^(h)]⁺↑`. -/
theorem isMinimalServiceCurve_concatConv_spResidual
    {ι κ : Type*} [Fintype ι] [LinearOrder ι]
    {S : κ → (ι → Curve) → (ι → Curve) → Prop} {β : κ → ℝ≥0 → ℝ≥0}
    {α : κ → ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβlc : ∀ h, IsLeftContinuous (β h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (β h) (aggregateServer (S h)))
    (hSP : ∀ h, IsStaticPriorityServerN (S h))
    (path : List κ) :
    IsMinimalServiceCurve
      (concatConv (fun h => liftEReal (residualCurve (β h)
        (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α h j v))) path)
      (concatComp (fun h => residualServer (fun As Ds => S h As Ds ∧
        ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α h j)) i) path) := by
  apply IsMinimalServiceCurve.concatComp
  · intro _; exact (isNonneg_liftEReal _).isBddBelowReal
  · intro h
    refine (isStrictMinimalServiceCurve_residualServer_of_isStaticPriority
      (hcaus h) (hβlc h) (hβ h) (hSP h)).isMinimalServiceCurve ?_
    rintro Ai Di ⟨As, Ds, ⟨hp, _⟩, rfl, rfl⟩
    exact hcaus h As Ds hp i

/-! ## Book restatement (static-priority PMOO)
A flow `i` crossing a path of preemptive static-priority servers, each
offering a left-continuous strict service curve `β^(h)` with the
higher-priority flows `j < i` arrival-constrained by `α_j^(h)`, is offered
the end-to-end min-plus service curve `β̃_i = ∗_{h∈p_i} [β^(h) − ∑_{j<i}
α_j^(h)]⁺` — the convolution of the per-server priority residuals.
(The SP-PMOO nested-tandem sharpening, paying the multiplexing only
once, is correctness-external [BOU 09].) -/
example {ι κ : Type*} [Fintype ι] [LinearOrder ι]
    {S : κ → (ι → Curve) → (ι → Curve) → Prop} {β : κ → ℝ≥0 → ℝ≥0}
    {α : κ → ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβlc : ∀ h, IsLeftContinuous (β h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (β h) (aggregateServer (S h)))
    (hSP : ∀ h, IsStaticPriorityServerN (S h))
    (path : List κ) :
    IsMinimalServiceCurve
      (concatConv (fun h => liftEReal (residualCurve (β h)
        (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α h j v))) path)
      (concatComp (fun h => residualServer (fun As Ds => S h As Ds ∧
        ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α h j)) i) path) :=
  isMinimalServiceCurve_concatConv_spResidual hcaus hβlc hβ hSP path

end DeepWiki
