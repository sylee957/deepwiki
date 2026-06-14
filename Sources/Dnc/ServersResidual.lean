import Book.ServersResidualFifoPmooConcat
import Sources.Dnc.Source

/-! # DNC catalog — residual service under multiplexing
Catalog entries for the source's residual-service results, each a
`SourceRef` (carrying the book's own numbering) paired with a
restatement discharged by the `DeepWiki` library. The restatement
typechecks only if the book-faithful statement really follows from the
library declaration, so the catalog cannot drift from the theory.

(The library import path is `Book.…` until the topic rename to
`DeepWiki.NetworkCalculus.…`; this is the only change the rename makes
to a catalog file.) -/

namespace DeepWiki.Dnc

open DeepWiki DeepWiki.Catalog
open scoped Classical NNReal ENNReal
open Finset

/-- FIFO-PMOO residual over a tandem. -/
def prop_10_1 : SourceRef :=
  { doi := doi, location := "§10.3.4.2", label := "Proposition 10.1",
    kind := .prop, page := some 242 }

/-- Restatement of `prop_10_1`, discharged by the library theorem
`minConv_fifoResidual_concatConv_le`: a sequence of FIFO servers offering
min-plus service curves `β^(h)`, crossed by `m` flows with the tagged
flow `k` constrained by the arrival curve `α`, leaves the `m − 1` other
flows the min-plus service curve `[∗ₕ β^(h) − α ∗ δ_θ]⁺ ∧ δ_θ`. -/
theorem prop_10_1_statement {ι κ : Type*} [Fintype ι]
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

/-- The residual-service portion of the DNC catalog. -/
def residualCatalog : List SourceRef := [prop_10_1]

end DeepWiki.Dnc
