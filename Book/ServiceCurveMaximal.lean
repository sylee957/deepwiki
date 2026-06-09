import Book.RealCurves
import Book.ServiceCurveMinPlus

/-! # Maximal service curves
A maximal service curve `β` upper-bounds a server's output by the convolution:
`D ≤ A ∗ β` on every served pair — the order dual of the min-plus service
curve. Largest relation `maximalServiceRelation β`; universal curve `δ₀`. -/

namespace DeepWiki

open scoped Classical NNReal

/-- `S` offers maximal service curve `beta`: every served pair satisfies
`D ≤ A ∗ beta`, the curve pair lifted into `EReal` via `curveE`. -/
def IsMaximalServiceCurve (beta : ℝ≥0 → EReal)
    (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → curveE D ≤ minConv (curveE A) beta

/-- The maximal-service relation of `beta`: all curve pairs with
`D ≤ A ∗ beta`. For `beta 0 ≤ 0` no causality conjunct is needed — see
`isCausal_maximalServiceRelation`. -/
def maximalServiceRelation (beta : ℝ≥0 → EReal) :
    Curve → Curve → Prop :=
  fun A D => curveE D ≤ minConv (curveE A) beta

/-- A relation offers maximal service `beta` iff all its pairs lie in
`maximalServiceRelation beta` — for `beta` in `F₀` (see
`isServer_maximalServiceRelation`), the largest server offering `beta`. -/
theorem isMaximalServiceCurve_iff_subset {beta : ℝ≥0 → EReal}
    {S : Curve → Curve → Prop} :
    IsMaximalServiceCurve beta S ↔
      ∀ A D, S A D → maximalServiceRelation beta A D :=
  Iff.rfl

/-- `maximalServiceRelation beta` itself offers maximal service `beta`. -/
theorem isMaximalServiceCurve_maximalServiceRelation (beta : ℝ≥0 → EReal) :
    IsMaximalServiceCurve beta (maximalServiceRelation beta) :=
  fun _ _ h => h

/-- Causality is automatic: when `beta 0 ≤ 0`, `A ∗ beta ≤ A`
(`minConv_self_le`), so `D ≤ A ∗ beta` already forces `D ≤ A`. -/
theorem isCausal_maximalServiceRelation {beta : ℝ≥0 → EReal}
    (h0 : beta 0 ≤ 0) :
    IsCausal (maximalServiceRelation beta) := by
  intro A D hp
  exact curveE_le_iff.mp (le_trans hp (minConv_self_le h0 A))

/-- `curveE zeroCurve t = 0`. -/
theorem curveE_zeroCurve (t : ℝ≥0) : curveE zeroCurve t = 0 := by
  simp [curveE]

/-- For nonnegative `beta`, `0 ≤ A ∗ beta` (`minConv_isNonneg`), so `zeroCurve`
is a valid output for every arrival: `maximalServiceRelation beta` is
left-total. -/
theorem isLeftTotal_maximalServiceRelation {beta : ℝ≥0 → EReal}
    (hnn : IsNonneg beta) :
    IsLeftTotal (maximalServiceRelation beta) := by
  intro A
  refine ⟨zeroCurve, fun t => ?_⟩
  rw [curveE_zeroCurve]
  exact minConv_isNonneg (curveE_nonneg A) hnn t

/-- For `beta` in `F₀` — null at the origin and nonnegative —
`maximalServiceRelation beta` is a server. -/
theorem isServer_maximalServiceRelation {beta : ℝ≥0 → EReal}
    (h0 : beta 0 ≤ 0) (hnn : IsNonneg beta) :
    IsServer (maximalServiceRelation beta) :=
  ⟨isCausal_maximalServiceRelation h0,
    isLeftTotal_maximalServiceRelation hnn⟩

/-- The `EReal`-valued pure-delay curve on `ℝ≥0`: `0` up to `d`, `⊤` after
(the `delayNN`/`delayE` sibling for `EReal` values). -/
noncomputable abbrev delayEReal (d : ℝ≥0) : ℝ≥0 → EReal := delay d

/-- `δ₀` agrees with the convolution unit: `delayEReal 0 = convUnitEReal`
(on `ℝ≥0`, `t ≤ 0 ↔ t = 0`). -/
theorem delayEReal_zero_eq_convUnitEReal :
    delayEReal 0 = convUnitEReal := by
  funext t
  simp [convUnitEReal]

/-- `δ₀` is a unit on curves: `A ∗ δ₀ = A`, via `minConv_convUnitEReal_right`
(`curveE A` is real-valued, hence `NeverBot`). -/
theorem minConv_delayEReal_zero (A : Curve) :
    minConv (curveE A) (delayEReal 0) = curveE A := by
  rw [delayEReal_zero_eq_convUnitEReal]
  exact minConv_convUnitEReal_right (fun _ => EReal.coe_ne_bot _)

/-- Every causal relation — in particular every server — offers the maximal
service curve `δ₀`: causality gives `D ≤ A = A ∗ δ₀`. -/
theorem isMaximalServiceCurve_delayEReal_zero {S : Curve → Curve → Prop}
    (hc : IsCausal S) :
    IsMaximalServiceCurve (delayEReal 0) S := by
  intro A D hp
  rw [minConv_delayEReal_zero]
  exact curveE_mono (hc _ _ hp)

end DeepWiki
