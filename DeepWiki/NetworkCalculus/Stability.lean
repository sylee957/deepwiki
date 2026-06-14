import DeepWiki.NetworkCalculus.ArrivalCurves
import Mathlib.Order.LiminfLimsup

/-! # Stability primitives
The self-contained building blocks of the stability theory: the long-term
arrival/service rates (`limsup`/`liminf` of `f(t)/t`), the per-server local
stability condition (arrival rate below service rate) and its central
consequence — eventually the arrival curve drops below the service curve, so
the first crossing (hence the maximal backlogged-period length `ℓmax`) is
finite. Also the scaling of a flow by a constant and the fact that scaling
preserves an arrival constraint. (Global stability as a network predicate, the
fix-point sufficient condition, and the universally-stable policies build a
network model on top of these and are not formalized here.) -/

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

/-- A single server is **locally stable** when the long-term arrival rate of
its (aggregate) input flow is strictly below its long-term service rate
(Definition 12.2, per-server form: `∑ rᵢ < R` for the aggregate `α`). -/
def IsLocallyStableServer (α β : ℝ≥0 → ℝ≥0) : Prop :=
  longTermArrivalRate α < longTermServiceRate β

/-- **The analytic heart of local stability**: if the long-term arrival rate
of `α` is strictly below the long-term service rate of `β`, then eventually
(for all large `t`) the arrival curve drops to or below the service curve,
`α t ≤ β t`. Proof: pick a rate `c` strictly between the `limsup` and the
`liminf`; then eventually `α t / t < c < β t / t`, and dividing out the common
`t` (monotonicity of `·/t`) gives `α t ≤ β t`. -/
theorem eventually_le_of_longTermArrivalRate_lt {α β : ℝ≥0 → ℝ≥0}
    (h : longTermArrivalRate α < longTermServiceRate β) :
    ∀ᶠ t in atTop, α t ≤ β t := by
  obtain ⟨c, hac, hcb⟩ := exists_between h
  have h1 : ∀ᶠ t in atTop, (α t : ℝ≥0∞) / (t : ℝ≥0∞) < c :=
    eventually_lt_of_limsup_lt hac
  have h2 : ∀ᶠ t in atTop, c < (β t : ℝ≥0∞) / (t : ℝ≥0∞) :=
    eventually_lt_of_lt_liminf hcb
  filter_upwards [h1, h2] with t ht1 ht2
  have hlt : (α t : ℝ≥0∞) / (t : ℝ≥0∞) < (β t : ℝ≥0∞) / (t : ℝ≥0∞) := ht1.trans ht2
  rw [← ENNReal.coe_le_coe]
  by_contra hcon
  rw [not_le] at hcon
  have hle : (β t : ℝ≥0∞) ≤ (α t : ℝ≥0∞) := hcon.le
  have hdiv : (β t : ℝ≥0∞) / (t : ℝ≥0∞) ≤ (α t : ℝ≥0∞) / (t : ℝ≥0∞) := by gcongr
  exact lt_irrefl _ (hdiv.trans_lt hlt)

/-- The crossing set of a locally stable server is nonempty: eventually
`α t ≤ β t`, so some positive time witnesses the crossing. -/
theorem crossingSet_nonempty_of_isLocallyStableServer {α β : ℝ≥0 → ℝ≥0}
    (h : IsLocallyStableServer α β) : (crossingSet α β).Nonempty := by
  obtain ⟨x, hx0, hxle⟩ :=
    ((eventually_gt_atTop 0).and (eventually_le_of_longTermArrivalRate_lt h)).exists
  exact ⟨x, hx0, hxle⟩

/-- **Lemma 12.1** (local stability ⟹ finite backlogged period): a locally
stable server has a *finite* first crossing `firstCrossing α β < ⊤`. Since the
maximal backlogged-period length `ℓmax` is bounded by this first crossing
(Theorem 5.5, `maxBackloggedLength_le_firstCrossing`), `ℓmax < ∞`. -/
theorem firstCrossing_lt_top_of_isLocallyStableServer {α β : ℝ≥0 → ℝ≥0}
    (h : IsLocallyStableServer α β) : firstCrossing α β < ⊤ := by
  obtain ⟨x, hx0, hxle⟩ := crossingSet_nonempty_of_isLocallyStableServer h
  calc firstCrossing α β ≤ (x : ℝ≥0∞) := iInf₂_le x ⟨hx0, hxle⟩
    _ < ⊤ := ENNReal.coe_lt_top

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
