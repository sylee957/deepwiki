import DeepWiki.NetworkCalculus.ArrivalCurves
import Mathlib.Order.LiminfLimsup

/-! # Stability primitives
The self-contained building blocks of the stability theory: the long-term
arrival/service rates (`limsup`/`liminf` of `f(t)/t`), the scaling of a flow
by a constant, and the fact that scaling preserves an arrival constraint.
(Local/global stability as network predicates, the fix-point sufficient
condition, and the universally-stable policies build a network model on top
of these and are not formalized here.) -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Filter

/-- The long-term arrival rate of a flow, `limsup_{t→∞} α(t)/t`
(Definition 12.1). -/
noncomputable def longTermArrivalRate (α : ℝ≥0 → ℝ≥0) : ℝ≥0∞ :=
  limsup (fun t => (α t : ℝ≥0∞) / (t : ℝ≥0∞)) atTop

/-- The long-term service rate of a server, `liminf_{t→∞} β(t)/t`
(Definition 12.1). -/
noncomputable def longTermServiceRate (β : ℝ≥0 → ℝ≥0) : ℝ≥0∞ :=
  liminf (fun t => (β t : ℝ≥0∞) / (t : ℝ≥0∞)) atTop

/-- A flow scaled by a constant `m ∈ ℝ≥0`: `(m · A)(t) = m · A t`
(Definition 12.4). -/
def scaledFlow (m : ℝ≥0) (A : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 := fun t => m * A t

/-- `scaledFlow m A t = m * A t`. -/
@[simp] theorem scaledFlow_apply (m : ℝ≥0) (A : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    scaledFlow m A t = m * A t := rfl

/-- Scaling preserves a maximal arrival bound: if `α` upper-bounds the flow
`A`, then `m·α` upper-bounds the scaled flow `m·A` (Lemma 12.6). -/
theorem isMaximalArrivalBound_scaledFlow {A α : ℝ≥0 → ℝ≥0} (m : ℝ≥0)
    (h : IsMaximalArrivalBound A α) :
    IsMaximalArrivalBound (scaledFlow m A) (scaledFlow m α) := by
  rw [isMaximalArrivalBound_iff_increment] at h ⊢
  intro t d
  calc scaledFlow m A (t + d) = m * A (t + d) := rfl
    _ ≤ m * (A t + α d) := by have := h t d; gcongr
    _ = m * A t + m * α d := mul_add m (A t) (α d)
    _ = scaledFlow m A t + scaledFlow m α d := rfl

end DeepWiki
