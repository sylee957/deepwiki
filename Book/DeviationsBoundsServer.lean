import Book.DeviationsBounds
import Book.ServiceCurveMinPlus

/-! # Delay and backlog bounds for servers
Theorem-level form of the deviation bounds: a served pair of a server
offering a nonnegative min-plus service curve `β` (the `EReal` stack), with
maximal arrival curve `α`, has delay at most `hDev` and backlog at most
`vDev`. The bridge reads `β` on `ℝ≥0∞` through `EReal.toENNReal`, the upper
adjoint of the coercion. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- `EReal.toENNReal` and the `ℝ≥0∞ → EReal` coercion form a Galois
connection. -/
theorem gc_toENNReal_coe :
    GaloisConnection EReal.toENNReal (fun y : ℝ≥0∞ => (y : EReal)) := by
  intro x y
  constructor
  · intro h
    calc x ≤ (x.toENNReal : EReal) := by
          rw [EReal.coe_toENNReal_eq_max]
          exact le_max_right _ _
      _ ≤ (y : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
  · intro h
    have h2 := EReal.toENNReal_le_toENNReal h
    rwa [EReal.toENNReal_coe] at h2

/-- The `ℝ≥0∞ → EReal` coercion preserves infima (it is an upper adjoint). -/
theorem coe_ennreal_iInf {ι : Sort*} (f : ι → ℝ≥0∞) :
    ((⨅ i, f i : ℝ≥0∞) : EReal) = ⨅ i, (f i : EReal) :=
  gc_toENNReal_coe.u_iInf

/-- The `ℝ≥0∞` reading of an `EReal`-valued service curve (the identity on
nonnegative values, `0` below). -/
noncomputable def toENN (beta : ℝ≥0 → EReal) : ℝ≥0 → ℝ≥0∞ :=
  fun s => (beta s).toENNReal

namespace Deviation

/-- For nonnegative `beta`, the `ℝ≥0∞` convolution of a curve with the
reading `toENN beta` coerces to the `EReal` convolution. -/
theorem coe_minConv_toENN (A : Curve) {beta : ℝ≥0 → EReal}
    (hnn : IsNonneg beta) (t : ℝ≥0) :
    ((minConv (toE ⇑A) (toENN beta) t : ℝ≥0∞) : EReal)
      = minConv (curveE A) beta t := by
  show ((⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      toE ⇑A p.1.1 + toENN beta p.1.2 : ℝ≥0∞) : EReal)
    = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        curveE A p.1.1 + beta p.1.2
  rw [coe_ennreal_iInf]
  refine iInf_congr ?_
  rintro ⟨⟨u, s⟩, _⟩
  show ((toE ⇑A u + toENN beta s : ℝ≥0∞) : EReal) = curveE A u + beta s
  rw [EReal.coe_ennreal_add]
  congr 1
  exact EReal.coe_toENNReal (hnn s)

/-- A pair served with nonnegative min-plus service `beta` satisfies the
`ℝ≥0∞` convolution inequality consumed by the deviation bounds. -/
theorem minConv_toENN_le_of_isMinPlusServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal}
    (hβ : IsMinPlusServiceCurve beta S) (hnn : IsNonneg beta)
    {A D : Curve} (hp : S A D) (t : ℝ≥0) :
    minConv (toE ⇑A) (toENN beta) t ≤ (D t : ℝ≥0∞) := by
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff, coe_minConv_toENN A hnn t]
  calc minConv (curveE A) beta t
      ≤ curveE D t := hβ A D hp t
    _ = (((D t : ℝ≥0) : ℝ≥0∞) : EReal) :=
        (EReal.coe_nnreal_eq_coe_real (D t)).symm

/-- **Delay bound for servers.** A pair served with nonnegative nondecreasing
min-plus service `beta`, the arrival having maximal arrival curve `α`, has
delay at most the horizontal deviation `hDev α (toENN beta)`. -/
theorem delay_le_hDev_of_isMinPlusServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsMinPlusServiceCurve beta S) (hp : S A D)
    (hnn : IsNonneg beta) (hmono : Monotone beta)
    (harr : IsMaximalArrivalCurve (toE ⇑A) α) :
    delay ⇑A ⇑D ≤ (hDev α (toENN beta) : ℝ≥0∞) :=
  delay_le_hDev A.mono
    (fun _ _ hab => EReal.toENNReal_le_toENNReal (hmono hab))
    harr (minConv_toENN_le_of_isMinPlusServiceCurve hβ hnn hp)

/-- **Backlog bound for servers** (pointwise): the backlog of a served pair
is bounded by the vertical deviation `vDev α (toENN beta)`. -/
theorem coe_backlogAt_le_vDev_of_isMinPlusServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsMinPlusServiceCurve beta S) (hp : S A D)
    (hnn : IsNonneg beta)
    (harr : IsMaximalArrivalCurve (toE ⇑A) α) (t : ℝ≥0) :
    (backlogAt ⇑A ⇑D t : ℝ≥0∞) ≤ vDev α (toENN beta) :=
  coe_backlogAt_le_vDev harr
    (minConv_toENN_le_of_isMinPlusServiceCurve hβ hnn hp) t

/-- **Backlog bound for servers** (sup form): `b(A, D) ≤ vDev α (toENN beta)`. -/
theorem iSup_backlogAt_le_vDev_of_isMinPlusServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {A D : Curve} (hβ : IsMinPlusServiceCurve beta S) (hp : S A D)
    (hnn : IsNonneg beta)
    (harr : IsMaximalArrivalCurve (toE ⇑A) α) :
    (⨆ t : ℝ≥0, (backlogAt ⇑A ⇑D t : ℝ≥0∞)) ≤ vDev α (toENN beta) :=
  iSup_backlogAt_le_vDev harr
    (minConv_toENN_le_of_isMinPlusServiceCurve hβ hnn hp)

end Deviation

end DeepWiki
