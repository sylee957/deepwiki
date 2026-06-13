import Book.ServiceCurveMinimal
import Book.ClosuresEReal

/-! # Extended cumulative curves (`ℝ≥0∞`-valued)
The `Curve` type is `ℝ≥0 → ℝ≥0` everywhere, so it cannot carry the `+∞`-valued
cumulative processes the book uses as witnesses in several `⇏` statements — most
notably `δ_0` as an *arrival* (an instantaneous infinite burst) for the refined
monotony/family theorems (Thm 9.3 item 3/8, Thm 9.4 item 1). `CurveENN` is the
extended analogue: a non-decreasing, null-at-origin, piecewise- and left-continuous
function `ℝ≥0 → ℝ≥0∞`. It lifts to `ℝ≥0 → EReal` (via `coe_ennreal`) so the generic
`minimalServicePair` and the convolution machinery apply unchanged. -/

namespace DeepWiki

open Set Topology Filter
open scoped Classical NNReal ENNReal

/-- An extended cumulative curve: non-decreasing, `f 0 = 0`, piecewise-continuous,
left-continuous, valued in `ℝ≥0∞` (so it may take the value `+∞`). -/
structure CurveENN where
  /-- The underlying function `ℝ≥0 → ℝ≥0∞`. -/
  toFun : ℝ≥0 → ℝ≥0∞
  /-- Non-decreasing. -/
  mono : Monotone toFun
  /-- Null at the origin: `f 0 = 0`. -/
  zero : IsNullAtOrigin toFun
  /-- Piecewise-continuous. -/
  pwc : IsPiecewiseContinuous toFun
  /-- Left-continuous. -/
  leftCont : IsLeftContinuous toFun

/-- A `CurveENN` is callable as its underlying function. -/
instance : FunLike CurveENN ℝ≥0 ℝ≥0∞ where
  coe := CurveENN.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- Two extended curves are equal when equal as functions. -/
@[ext] theorem CurveENN.ext {A B : CurveENN} (h : ∀ t, A t = B t) : A = B :=
  DFunLike.ext A B h

/-- Pointwise order on extended curves. -/
instance : LE CurveENN where
  le D A := ∀ t, D t ≤ A t

/-- `D ≤ A` on extended curves unfolds to the pointwise order. -/
theorem CurveENN.le_def {D A : CurveENN} : D ≤ A ↔ ∀ t, D t ≤ A t := Iff.rfl

/-- The `EReal` view of an extended curve, `t ↦ (A t : EReal)`, feeding the generic
`minimalServicePair`/convolution machinery. -/
noncomputable def curveENNEReal (A : CurveENN) : ℝ≥0 → EReal :=
  fun t => (A t : EReal)

/-- `curveENNEReal A t = (A t : EReal)`. -/
@[simp] theorem curveENNEReal_apply (A : CurveENN) (t : ℝ≥0) :
    curveENNEReal A t = (A t : EReal) := rfl

/-! ## The instantaneous infinite burst `δ_0` as an arrival
`δ_0` (`0` at the origin, `+∞` afterwards) is the cumulative process of an
instantaneous infinite burst — a genuine arrival only over the extended carrier. It
is the witness the book uses for the `⇏`/forcing parts of the refined
monotony/family theorems. -/

/-- The extended arrival `δ_0`: `0` at the origin, `+∞` at every positive time. -/
noncomputable def delay0ENN : CurveENN where
  toFun t := if t = 0 then 0 else ⊤
  mono := by
    intro a b hab
    by_cases ha : a = 0
    · simp [ha]
    · have hb : b ≠ 0 := fun h => ha (le_antisymm (h ▸ hab) zero_le')
      simp [if_neg ha, if_neg hb]
  zero := if_pos rfl
  pwc := by
    intro T
    refine Set.Finite.subset (Set.finite_singleton (0 : ℝ≥0)) ?_
    intro t ht
    by_contra htne
    have htne' : t ≠ 0 := by simpa using htne
    refine ht.1 ?_
    have hev : (fun s => if s = 0 then (0 : ℝ≥0∞) else ⊤) =ᶠ[𝓝 t] (fun _ => ⊤) := by
      filter_upwards [Ioi_mem_nhds (pos_of_ne_zero htne')] with s hs
      exact if_neg (ne_of_gt hs)
    exact (continuousAt_congr hev).mpr continuousAt_const
  leftCont := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · exact isLeftContinuousAt_zero _
    · refine continuousWithinAt_const.congr_of_eventuallyEq ?_ (if_neg ht)
      filter_upwards [Ioo_mem_nhdsLT (pos_of_ne_zero ht)] with s hs
      exact if_neg (ne_of_gt hs.1)

/-- `delay0ENN t = ⊤` for positive `t`. -/
theorem delay0ENN_apply_pos {t : ℝ≥0} (ht : t ≠ 0) : delay0ENN t = ⊤ := if_neg ht

/-- `delay0ENN 0 = 0`. -/
@[simp] theorem delay0ENN_zero_eq : delay0ENN 0 = 0 := if_pos rfl

/-- The min-plus service relation over extended arrivals/departures: a pair of
`CurveENN`s with `A ≥ D ≥ A ∗ beta`, read through `curveENNEReal`. -/
def minimalServiceRelExt (beta : ℝ≥0 → EReal) : CurveENN → CurveENN → Prop :=
  fun A D => minimalServicePair beta (curveENNEReal A) (curveENNEReal D)

/-- `minimalServiceRelExt beta A D` unfolds to `D ≤ A` and `A ∗ beta ≤ D` (in the
`EReal` view). -/
theorem mem_minimalServiceRelExt_iff {beta : ℝ≥0 → EReal} {A D : CurveENN} :
    minimalServiceRelExt beta A D ↔
      curveENNEReal D ≤ curveENNEReal A ∧ minConv (curveENNEReal A) beta ≤ curveENNEReal D :=
  Iff.rfl

/-- `δ_0` is the convolution unit, also as an `EReal` arrival:
`curveENNEReal delay0ENN = convUnitEReal`. -/
theorem curveENNEReal_delay0ENN : curveENNEReal delay0ENN = convUnitEReal := by
  funext t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [curveENNEReal_apply, delay0ENN_zero_eq, convUnitEReal, if_pos rfl,
      EReal.coe_ennreal_zero]
  · rw [curveENNEReal_apply, delay0ENN_apply_pos ht, convUnitEReal, if_neg ht,
      EReal.coe_ennreal_top]

/-- **Feeding `δ_0` recovers the service curve**: if the instantaneous infinite burst
`δ_0` is min-plus served by `beta` (with `beta` never `−∞`), the departure dominates
`beta` — `beta ≤ D` (in the `EReal` view). This is the book's `δ_0`-probing technique
(e.g. the Thm 9.6 step `(δ_0, β') ∈ S(β) ⟹ β' ≥ β`), now expressible with an extended
arrival. Since `δ_0 ∗ beta = beta`, the min-plus lower bound `δ_0 ∗ beta ≤ D` is exactly
`beta ≤ D`. -/
theorem le_curveENNEReal_of_minimalServiceRelExt_delay0 {beta : ℝ≥0 → EReal}
    (hbeta : IsNeverBot beta) {D : CurveENN} (h : minimalServiceRelExt beta delay0ENN D) :
    beta ≤ curveENNEReal D := by
  have hD := (mem_minimalServiceRelExt_iff.mp h).2
  rwa [curveENNEReal_delay0ENN, minConv_convUnitEReal_left beta hbeta] at hD

/-- The `EReal` view of an extended curve never takes `−∞`. -/
theorem isNeverBot_curveENNEReal (A : CurveENN) : IsNeverBot (curveENNEReal A) :=
  fun t => by rw [curveENNEReal_apply]; exact EReal.coe_ennreal_ne_bot _

/-- Every extended curve is dominated by `δ_0`. -/
theorem le_delay0ENN (A : CurveENN) : A ≤ delay0ENN := by
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [show A 0 = 0 from A.zero, delay0ENN_zero_eq]
  · rw [delay0ENN_apply_pos ht]; exact le_top

/-- `curveENNEReal` is monotone in the curve. -/
theorem curveENNEReal_mono {A B : CurveENN} (h : A ≤ B) :
    curveENNEReal A ≤ curveENNEReal B :=
  fun t => by
    rw [curveENNEReal_apply, curveENNEReal_apply]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (h t)

/-- Under its own service curve, `δ_0` is min-plus served by the curve itself:
`(δ_0, A) ∈ S_mp^ext(A)` (since `δ_0 ∗ A = A` and `A ≤ δ_0`). -/
theorem minimalServiceRelExt_delay0_self (A : CurveENN) :
    minimalServiceRelExt (curveENNEReal A) delay0ENN A := by
  refine ⟨curveENNEReal_mono (le_delay0ENN A), ?_⟩
  rw [curveENNEReal_delay0ENN]
  exact le_of_eq (minConv_convUnitEReal_left _ (isNeverBot_curveENNEReal A))

/-- **Converse min-plus monotony, with extended arrivals**: if every extended pair
min-plus served by `β'` is also served by `β`, then `β ≤ β'`. Over `Curve` (finite
arrivals) the converse of `β ≤ β' ⟹ S_mp(β) ⊇ S_mp(β')` *fails*; the instantaneous
infinite burst `δ_0` is exactly the arrival that makes it hold — probing the `β'`-server
with `δ_0` recovers `β'`, which must then dominate `β`. -/
theorem le_of_minimalServiceRelExt_le {β β' : CurveENN}
    (h : minimalServiceRelExt (curveENNEReal β') ≤ minimalServiceRelExt (curveENNEReal β)) :
    β ≤ β' := by
  have hmem : minimalServiceRelExt (curveENNEReal β) delay0ENN β' :=
    h delay0ENN β' (minimalServiceRelExt_delay0_self β')
  have hle := le_curveENNEReal_of_minimalServiceRelExt_delay0 (isNeverBot_curveENNEReal β) hmem
  intro t
  have ht := hle t
  rw [curveENNEReal_apply, curveENNEReal_apply] at ht
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mp ht

end DeepWiki
