import Book.Servers
import Book.ConvolutionReal
import Book.CurveDioidEReal
import Book.ConvolutionMinimumExt

/-! # Min-plus service curves
The `EReal` curve view `curveEReal`; `IsMinimalServiceCurve β S` — `A ∗ β ≤ D` on
served pairs, `β : ℝ≥0 → EReal` — and the largest such relation
`minimalServiceRel β`: a server when `β 0 ≤ 0`, empty when `β 0 > 0`, and
every server offers the zero curve `betaZero`. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- The exact `EReal` lift of an `ℝ≥0`-valued cumulative function:
`t ↦ ((f t : ℝ) : EReal)`. -/
noncomputable abbrev liftEReal (f : ℝ≥0 → ℝ≥0) : ℝ≥0 → EReal :=
  fun t => ((f t : ℝ) : EReal)

/-- `liftEReal f` is nonnegative. -/
theorem isNonneg_liftEReal (f : ℝ≥0 → ℝ≥0) : IsNonneg (liftEReal f) :=
  fun t => EReal.coe_nonneg.mpr (f t).coe_nonneg

/-- `liftEReal` transports monotonicity: `liftEReal f` is monotone when `f`
is. -/
theorem monotone_liftEReal {f : ℝ≥0 → ℝ≥0} (hmono : Monotone f) :
    Monotone (liftEReal f) :=
  fun _ _ hab => by exact_mod_cast hmono hab

/-- A curve viewed in `EReal`: the lift `liftEReal ⇑A`. -/
noncomputable def curveEReal (A : Curve) : ℝ≥0 → EReal :=
  liftEReal ⇑A

/-- `curveEReal A t = ((A t : ℝ) : EReal)`: the pointwise value of the `EReal`
view. -/
@[simp] theorem curveEReal_apply (A : Curve) (t : ℝ≥0) :
    curveEReal A t = ((A t : ℝ) : EReal) := rfl

/-- `curveEReal A` is the `EReal` lift of the underlying function:
`curveEReal A = liftEReal ⇑A`. -/
theorem curveEReal_eq_liftEReal (A : Curve) : curveEReal A = liftEReal ⇑A := rfl

/-- `curveEReal A` is nonnegative: `0 ≤ curveEReal A t`. -/
theorem curveEReal_nonneg (A : Curve) (t : ℝ≥0) : (0 : EReal) ≤ curveEReal A t :=
  isNonneg_liftEReal ⇑A t

/-- `curveEReal A` is never `⊥`: each value is a real coercion. -/
theorem curveEReal_neverBot (A : Curve) : NeverBot (curveEReal A) :=
  fun _ => EReal.coe_ne_bot _

/-- `curveEReal A 0 = 0`. -/
theorem curveEReal_zero (A : Curve) : curveEReal A 0 = 0 := by
  have h0 : A 0 = 0 := A.zero
  simp [h0]

/-- Curve order matches the `EReal` view: `D ≤ A ↔ curveEReal D ≤ curveEReal A`. -/
theorem curveEReal_le_iff {D A : Curve} : curveEReal D ≤ curveEReal A ↔ D ≤ A := by
  constructor
  · intro h t
    have ht := h t
    simp only [curveEReal_apply] at ht
    exact_mod_cast ht
  · intro h t
    simp only [curveEReal_apply]
    exact_mod_cast h t

/-- Curve order transfers to the `EReal` view: `D ≤ A → curveEReal D ≤ curveEReal A`. -/
theorem curveEReal_mono {D A : Curve} (h : D ≤ A) : curveEReal D ≤ curveEReal A :=
  curveEReal_le_iff.mpr h

/-- `curveEReal A` is monotone in time (contrast `curveEReal_mono`: monotonicity in
the curve argument). -/
theorem monotone_curveEReal (A : Curve) : Monotone (curveEReal A) :=
  monotone_liftEReal A.mono

/-- `curveEReal A` is left-continuous. -/
theorem isLeftContinuous_curveEReal (A : Curve) :
    IsLeftContinuous (curveEReal A) := fun t =>
  ((continuous_coe_real_ereal.comp NNReal.continuous_coe).continuousAt
    ).comp_continuousWithinAt (A.leftCont t)

/-- `curveEReal` values are real coercions, so they are `AddDefined` with
anything. -/
theorem addDefined_curveEReal (A : Curve) (u : ℝ≥0) (x : EReal) :
    AddDefined (curveEReal A u) x :=
  ⟨Or.inl (EReal.coe_ne_top _), Or.inl (EReal.coe_ne_bot _)⟩

/-- `S` offers `EReal`-valued min-plus service curve `beta`: every served pair
satisfies `A ∗ beta ≤ D` (i.e. `D ≥ A ∗ beta`), the curve pair lifted into
`EReal` via `curveEReal`. -/
def IsMinimalServiceCurve (beta : ℝ≥0 → EReal) (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → minConv (curveEReal A) beta ≤ curveEReal D

/-- When `beta 0 ≤ 0`, each input is its own output: `A` serves itself, since the
`(t, 0)` split gives `A ∗ beta ≤ A`. The left-total witness for the relation. -/
theorem minConv_self_le {beta : ℝ≥0 → EReal} (h0 : beta 0 ≤ 0) (A : Curve) :
    minConv (curveEReal A) beta ≤ curveEReal A := by
  refine fun t => le_trans (minConv_le_add _ _ (add_zero t)) ?_
  calc curveEReal A t + beta 0 ≤ curveEReal A t + 0 := by gcongr
    _ = curveEReal A t := add_zero _

/-- `(A, D)` is a min-plus service pair of `beta`: `A ≥ D ≥ A ∗ beta`, on
`T`-valued cumulative functions (the value-type-generic core of
`minimalServiceRel`). -/
def minimalServicePair {T : Type*} [Add T] [InfSet T] [LE T]
    (beta : ℝ≥0 → T) (A D : ℝ≥0 → T) : Prop :=
  D ≤ A ∧ minConv A beta ≤ D

/-- The min-plus service relation of `beta`: the causal pairs meeting
`A ∗ beta ≤ D`, i.e. `A ≥ D ≥ A ∗ beta`, read through `curveEReal`. Depends on
`beta` alone. -/
def minimalServiceRel (beta : ℝ≥0 → EReal) : Curve → Curve → Prop :=
  fun A D => minimalServicePair beta (curveEReal A) (curveEReal D)

/-- `minimalServiceRel beta A D` unfolds to `A ≥ D` and `A ∗ beta ≤ D`. -/
theorem mem_minimalServiceRel_iff {beta : ℝ≥0 → EReal} {A D : Curve} :
    minimalServiceRel beta A D ↔
      D ≤ A ∧ minConv (curveEReal A) beta ≤ curveEReal D := by
  rw [show (minimalServiceRel beta A D) ↔
        (curveEReal D ≤ curveEReal A ∧ minConv (curveEReal A) beta ≤ curveEReal D) from Iff.rfl,
    curveEReal_le_iff]

/-- The relation `minimalServiceRel beta` offers its own service curve. -/
theorem isMinimalServiceCurve_minimalServiceRel (beta : ℝ≥0 → EReal) :
    IsMinimalServiceCurve beta (minimalServiceRel beta) :=
  fun _ _ hp => hp.2

/-- When `beta 0 ≤ 0`, `minimalServiceRel beta` is a server: causality is the first
conjunct, and left-totality holds since each input serves itself. -/
theorem isServer_minimalServiceRel {beta : ℝ≥0 → EReal} (h0 : beta 0 ≤ 0) :
    IsServer (minimalServiceRel beta) :=
  ⟨fun _ _ hp => curveEReal_le_iff.mp hp.1,
    fun A => ⟨A, le_refl _, minConv_self_le h0 A⟩⟩

/-- The largest server offering `beta` (for `beta 0 ≤ 0`) is the relation
`minimalServiceRel beta`; any server `S` offering `beta` is contained in it. -/
theorem subset_minimalServiceRel {beta : ℝ≥0 → EReal} {S : Curve → Curve → Prop}
    (hS : IsMinimalServiceCurve beta S) (hSrv : IsServer S) :
    ∀ A D, S A D → minimalServiceRel beta A D := by
  intro A D hp
  exact ⟨curveEReal_mono (hSrv.1 _ _ hp), hS A D hp⟩

/-- A server offers `beta` iff its pairs all lie in `minimalServiceRel beta`. -/
theorem isMinimalServiceCurve_iff_subset {beta : ℝ≥0 → EReal}
    {S : Curve → Curve → Prop} (hSrv : IsServer S) :
    IsMinimalServiceCurve beta S ↔
      ∀ A D, S A D → minimalServiceRel beta A D := by
  refine ⟨fun hS => subset_minimalServiceRel hS hSrv, fun h A D hp => ?_⟩
  exact (mem_minimalServiceRel_iff.mp (h A D hp)).2

/-- Min-plus service curves are antitone: a smaller `beta` is still offered, since
`minConv` is monotone in its right argument. -/
theorem IsMinimalServiceCurve.mono
    {S : Curve → Curve → Prop} {beta beta' : ℝ≥0 → EReal}
    (h : beta ≤ beta') (hS : IsMinimalServiceCurve beta' S) :
    IsMinimalServiceCurve beta S :=
  fun A D hp t =>
    le_trans (minConv_le_minConv (fun _ => le_rfl) h t) (hS A D hp t)

/-- The min-plus service relation is antitone in the curve: `beta ≤ beta'`
gives `minimalServiceRel beta' ≤ minimalServiceRel beta`. -/
theorem minimalServiceRel_mono {beta beta' : ℝ≥0 → EReal}
    (h : beta ≤ beta') :
    minimalServiceRel beta' ≤ minimalServiceRel beta := by
  intro A D hp
  exact ⟨hp.1,
    ((isMinimalServiceCurve_minimalServiceRel beta').mono h) A D hp⟩

/-- The trivial zero service curve `beta ≡ 0` (`EReal`-valued). -/
noncomputable def betaZero : ℝ≥0 → EReal := fun _ => 0

/-- `beta ⊘̄ 0 ≤ beta`: the `s = 0` term of the defining infimum is `beta t`. -/
theorem maxDeconv_betaZero_le (beta : ℝ≥0 → EReal) :
    maxDeconv beta betaZero ≤ beta := by
  intro t
  refine le_trans (ciInf_le (OrderBot.bddBelow _) 0) ?_
  show beta (t + 0) - betaZero 0 ≤ beta t
  simp [betaZero]

/-- `beta ⊘̄ 0` is non-decreasing: shifting the input only enlarges the index set
of the defining infimum. -/
theorem monotone_maxDeconv_betaZero (beta : ℝ≥0 → EReal) :
    Monotone (maxDeconv beta betaZero) := by
  intro t t' htt
  refine le_iInf (fun s => ?_)
  refine le_trans (ciInf_le (OrderBot.bddBelow _) ((t' - t) + s)) ?_
  show beta (t + ((t' - t) + s)) - betaZero _ ≤ beta (t' + s) - betaZero s
  rw [show t + ((t' - t) + s) = t' + s by
    rw [← add_assoc, add_tsub_cancel_of_le htt]]
  simp [betaZero]

/-- `beta` can be replaced by the non-decreasing `beta ⊘̄ 0`: a server offering
`beta` also offers `beta ⊘̄ 0`, since `beta ⊘̄ 0 ≤ beta`. -/
theorem isMinimalServiceCurve_maxDeconv_betaZero {S : Curve → Curve → Prop}
    {beta : ℝ≥0 → EReal}
    (hS : IsMinimalServiceCurve beta S) :
    IsMinimalServiceCurve (maxDeconv beta betaZero) S :=
  hS.mono (maxDeconv_betaZero_le beta)

/-- `A ∗ beta₀ = beta₀` for any curve: the `(0, t)` split gives `curveEReal A 0 = 0`,
and every other term `curveEReal A u + 0 = curveEReal A u ≥ 0`, so the infimum is `0`. -/
theorem minConv_betaZero (A : Curve) :
    minConv (curveEReal A) betaZero = betaZero := by
  funext t
  refine le_antisymm ?_ ?_
  · refine le_trans
      (ciInf_le_of_le (OrderBot.bddBelow _) ⟨(0, t), by simp⟩ (le_refl _)) ?_
    show curveEReal A 0 + betaZero t ≤ betaZero t
    rw [curveEReal_zero]; show (0 : EReal) + 0 ≤ betaZero t; simp [betaZero]
  · refine le_iInf (fun p => ?_)
    show betaZero t ≤ curveEReal A p.1.1 + betaZero p.1.2
    show (0 : EReal) ≤ curveEReal A p.1.1 + 0
    rw [add_zero]; exact curveEReal_nonneg A p.1.1

/-- `A ∗ beta₀ ≤ D` for any curves: `A ∗ beta₀ = beta₀ = 0 ≤ curveEReal D`. -/
theorem minConv_betaZero_le (A D : Curve) :
    minConv (curveEReal A) betaZero ≤ curveEReal D := by
  rw [minConv_betaZero]; exact fun t => curveEReal_nonneg D t

/-- The zero-service chain on any server: `S A D` gives
`A ≥ D ≥ A ∗ beta₀ = beta₀`. -/
theorem betaZero_chain {S : Curve → Curve → Prop} (hSrv : IsServer S)
    {A D : Curve} (hp : S A D) :
    D ≤ A ∧ minConv (curveEReal A) betaZero ≤ curveEReal D ∧
      minConv (curveEReal A) betaZero = betaZero :=
  ⟨hSrv.1 _ _ hp, minConv_betaZero_le A D, minConv_betaZero A⟩

/-- Every server offers the zero service curve: `A ≥ D ≥ A ∗ beta₀ = beta₀`. -/
theorem isMinimalServiceCurve_betaZero (S : Curve → Curve → Prop) :
    IsMinimalServiceCurve betaZero S :=
  fun A D _ => minConv_betaZero_le A D

/-- Every server's pairs lie in `minimalServiceRel betaZero`: since each server
offers the zero service curve, `S ≤ minimalServiceRel betaZero`. -/
theorem subset_minimalServiceRel_betaZero {S : Curve → Curve → Prop}
    (hSrv : IsServer S) :
    ∀ A D, S A D → minimalServiceRel betaZero A D :=
  subset_minimalServiceRel (isMinimalServiceCurve_betaZero S) hSrv

/-- If `beta 0 > 0`, no curve pair can satisfy `A ≥ D ≥ A ∗ beta`. The `(0,0)`
split forces `D 0 ≥ A 0 + beta 0 > A 0 ≥ D 0`, a contradiction. -/
theorem not_serviceCurve_of_pos {beta : ℝ≥0 → EReal} (h0 : (0 : EReal) < beta 0)
    (A D : Curve) (hcaus : curveEReal D ≤ curveEReal A)
    (hconv : minConv (curveEReal A) beta ≤ curveEReal D) : False := by
  have hconv0 : minConv (curveEReal A) beta 0 ≤ curveEReal D 0 := hconv 0
  have hcaus0 : curveEReal D 0 ≤ curveEReal A 0 := hcaus 0
  have hsplit : minConv (curveEReal A) beta 0 = curveEReal A 0 + beta 0 :=
    minConv_apply_zero (curveEReal A) beta
  rw [hsplit] at hconv0
  have hchain : ((A 0 : ℝ) : EReal) + beta 0 ≤ ((A 0 : ℝ) : EReal) + 0 := by
    rw [add_zero]; exact le_trans hconv0 hcaus0
  have : beta 0 ≤ 0 :=
    (EReal.addLECancellable_coe (A 0 : ℝ)).add_le_add_iff_left.mp hchain
  exact absurd this (not_le.mpr h0)

/-- If `beta 0 > 0` the min-plus service relation is empty: no curve pair meets
`A ≥ D ≥ A ∗ beta`. With `beta 0 ≤ 0` assumable, this is why it is no loss. -/
theorem minimalServiceRel_eq_empty_of_pos {beta : ℝ≥0 → EReal}
    (h0 : (0 : EReal) < beta 0) (A D : Curve) :
    ¬ minimalServiceRel beta A D := by
  rintro ⟨hcaus, hconv⟩
  exact not_serviceCurve_of_pos h0 A D hcaus hconv

end DeepWiki
