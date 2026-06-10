import Book.RealCurves
import Book.ServiceCurveMinimal

/-! # Maximal service curves
A maximal service curve `β` upper-bounds a server's output by the convolution:
`D ≤ A ∗ β` on every served pair — the order dual of the min-plus service
curve. Largest relation `maximalServiceRel β`; the universal curve `δ₀`;
monotony in `β`, and replacement by the non-decreasing closure `ndClosure β`. -/

namespace DeepWiki

open scoped Classical NNReal

/-- `S` offers maximal service curve `beta`: every served pair satisfies
`D ≤ A ∗ beta`, the curve pair lifted into `EReal` via `curveE`. -/
def IsMaximalServiceCurve (beta : ℝ≥0 → EReal)
    (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → curveE D ≤ minConv (curveE A) beta

/-- The maximal-service relation of `beta`: all curve pairs with
`D ≤ A ∗ beta`. For `beta 0 ≤ 0` no causality conjunct is needed — see
`isCausal_maximalServiceRel`. -/
def maximalServiceRel (beta : ℝ≥0 → EReal) :
    Curve → Curve → Prop :=
  fun A D => curveE D ≤ minConv (curveE A) beta

/-- A relation offers maximal service `beta` iff all its pairs lie in
`maximalServiceRel beta` — for `beta` in `F₀` (see
`isServer_maximalServiceRel`), the largest server offering `beta`. -/
theorem isMaximalServiceCurve_iff_subset {beta : ℝ≥0 → EReal}
    {S : Curve → Curve → Prop} :
    IsMaximalServiceCurve beta S ↔
      ∀ A D, S A D → maximalServiceRel beta A D :=
  Iff.rfl

/-- `maximalServiceRel beta` itself offers maximal service `beta`. -/
theorem isMaximalServiceCurve_maximalServiceRel (beta : ℝ≥0 → EReal) :
    IsMaximalServiceCurve beta (maximalServiceRel beta) :=
  fun _ _ h => h

/-- Causality is automatic: when `beta 0 ≤ 0`, `A ∗ beta ≤ A`
(`minConv_self_le`), so `D ≤ A ∗ beta` already forces `D ≤ A`. -/
theorem isCausal_maximalServiceRel {beta : ℝ≥0 → EReal}
    (h0 : beta 0 ≤ 0) :
    IsCausal (maximalServiceRel beta) := by
  intro A D hp
  exact curveE_le_iff.mp (le_trans hp (minConv_self_le h0 A))

/-- `curveE zeroCurve t = 0`. -/
theorem curveE_zeroCurve (t : ℝ≥0) : curveE zeroCurve t = 0 := by
  simp [curveE]

/-- For nonnegative `beta`, `0 ≤ A ∗ beta` (`IsNonneg.conv`), so `zeroCurve`
is a valid output for every arrival: `maximalServiceRel beta` is
left-total. -/
theorem isLeftTotal_maximalServiceRel {beta : ℝ≥0 → EReal}
    (hnn : IsNonneg beta) :
    IsLeftTotal (maximalServiceRel beta) := by
  intro A
  refine ⟨zeroCurve, fun t => ?_⟩
  rw [curveE_zeroCurve]
  exact IsNonneg.conv (curveE_nonneg A) hnn t

/-- For `beta` in `F₀` — null at the origin and nonnegative —
`maximalServiceRel beta` is a server. -/
theorem isServer_maximalServiceRel {beta : ℝ≥0 → EReal}
    (h0 : beta 0 ≤ 0) (hnn : IsNonneg beta) :
    IsServer (maximalServiceRel beta) :=
  ⟨isCausal_maximalServiceRel h0,
    isLeftTotal_maximalServiceRel hnn⟩

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
  exact minConv_convUnitEReal_right (curveE_neverBot A)

/-- Every causal relation — in particular every server — offers the maximal
service curve `δ₀`: causality gives `D ≤ A = A ∗ δ₀`. -/
theorem isMaximalServiceCurve_delayEReal_zero {S : Curve → Curve → Prop}
    (hc : IsCausal S) :
    IsMaximalServiceCurve (delayEReal 0) S := by
  intro A D hp
  rw [minConv_delayEReal_zero]
  exact curveE_mono (hc _ _ hp)

/-! ## Monotony of maximal service curves -/

/-- Monotony of maximal service curves: a relation offering `beta ≤ beta'`
also offers `beta'`, since `A ∗ beta ≤ A ∗ beta'`. -/
theorem IsMaximalServiceCurve.mono {S : Curve → Curve → Prop}
    {beta beta' : ℝ≥0 → EReal} (h : beta ≤ beta')
    (hS : IsMaximalServiceCurve beta S) :
    IsMaximalServiceCurve beta' S :=
  fun A D hp =>
    le_trans (hS A D hp) (fun t => minConv_le_minConv (fun _ => le_rfl) h t)

/-- Equivalently, `maximalServiceRel` is monotone in the curve:
`beta ≤ beta'` gives the containment of relations. -/
theorem maximalServiceRel_mono {beta beta' : ℝ≥0 → EReal}
    (h : beta ≤ beta') :
    maximalServiceRel beta ≤ maximalServiceRel beta' :=
  (isMaximalServiceCurve_maximalServiceRel beta).mono h

example (beta : ℝ≥0 → EReal) : ndClosure beta = maxConv beta 0 :=
  ndClosure_eq_maxConv beta

/-- A maximal service curve may be replaced by its non-decreasing closure:
offering `beta` gives offering `ndClosure beta`, the least monotone majorant
of `beta` (equal to `maxConv beta 0` by `ndClosure_eq_maxConv`). -/
theorem isMaximalServiceCurve_ndClosure {S : Curve → Curve → Prop}
    {beta : ℝ≥0 → EReal} (hS : IsMaximalServiceCurve beta S) :
    IsMaximalServiceCurve (ndClosure beta) S :=
  hS.mono (le_ndClosure_ereal beta)

end DeepWiki
