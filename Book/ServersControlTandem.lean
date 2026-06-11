import Book.Deconvolution
import Book.ServersConcatenation

/-! # Tandem control
Designing a filter in front of a server: the server offers the min-plus
service curve `β`, and the controlled network `A → [βc] → A' → [β] → D`
must reach a reference behavior `βref`. By the concatenation theorem the
controlled network is guaranteed `βc ∗ β` — at the relation level, any
admissible controller makes `Smp(β) ∘ Smp(βc)` offer `βref` — so the
admissible controllers are `{βc | βref ≤ βc ∗ β}`, and by residuation the
smallest one is the deconvolution `β̂c = βref ⊘ β`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The admissible tandem controllers for a server curve `β` and a
reference `βref`: the curves `βc` whose controlled-network guarantee
dominates the reference, `βref ≤ βc ∗ β`. -/
def tandemControlSet (β βref : ℝ≥0 → ℝ≥0∞) : Set (ℝ≥0 → ℝ≥0∞) :=
  {βc | βref ≤ minConv βc β}

/-- `βc` is an admissible tandem controller iff `βref ≤ βc ∗ β`. -/
theorem mem_tandemControlSet_iff {β βref βc : ℝ≥0 → ℝ≥0∞} :
    βc ∈ tandemControlSet β βref ↔ βref ≤ minConv βc β :=
  Iff.rfl

/-- **Tandem control**: the smallest service curve `βc` with
`βc ∗ β ≥ βref` is the deconvolution `βref ⊘ β` — it is itself admissible
and lies below every admissible controller (residuation). -/
theorem isLeast_tandemControlSet (β βref : ℝ≥0 → ℝ≥0∞) :
    IsLeast (tandemControlSet β βref) (minDeconv βref β) :=
  ⟨minDeconv_le_iff_le_minConv.mp le_rfl,
    fun _ hβc => minDeconv_le_iff_le_minConv.mpr hβc⟩

/-- The infimum form of tandem control:
`β̂c = ⋀{βc | βc ∗ β ≥ βref} = βref ⊘ β`. -/
theorem sInf_tandemControlSet (β βref : ℝ≥0 → ℝ≥0∞) :
    sInf (tandemControlSet β βref) = minDeconv βref β :=
  (isLeast_tandemControlSet β βref).csInf_eq

/-- **The controlled network reaches the reference**: a filter curve `βc`
with `βref ≤ βc ∗ β` in front of the server makes the tandem
`Smp(β) ∘ Smp(βc)` offer `βref` (bounded-below curves). -/
theorem comp_minimalServiceRel_le_of_le_minConv
    {β βref βc : ℝ≥0 → EReal}
    (hbc : IsBddBelowReal βc) (hb : IsBddBelowReal β)
    (h : βref ≤ minConv βc β) :
    Relation.Comp (minimalServiceRel βc) (minimalServiceRel β)
      ≤ minimalServiceRel βref :=
  le_trans (comp_minimalServiceRel_le hbc hb) (minimalServiceRel_mono h)

/-! ## Book restatement (tandem control)
Let `βref` be the min-plus service curve the controlled network has to
reach. The smallest service curve `βc`, such that `βc ∗ β ≥ βref`, is
`β̂c = ⋀{βc | βc ∗ β ≥ βref} = βref ⊘ β`. This is a direct application of
the residuation `f ⊘ g ≤ h ↔ f ≤ h ∗ g` (`minDeconv_le_iff_le_minConv`). -/
example (β βref : ℝ≥0 → ℝ≥0∞) :
    sInf {βc : ℝ≥0 → ℝ≥0∞ | βref ≤ minConv βc β} = minDeconv βref β :=
  sInf_tandemControlSet β βref

/-! The infimum is attained: `β̂c` is itself an admissible controller, so
the controlled network designed with `β̂c = βref ⊘ β` reaches `βref`. -/
example (β βref : ℝ≥0 → ℝ≥0∞) :
    βref ≤ minConv (minDeconv βref β) β :=
  (isLeast_tandemControlSet β βref).1

end DeepWiki
