import Book.Servers
import Book.RealConvolution
import Book.ECurveDioid

/-! # Min-plus service curves
The `EReal` curve view `curveE`; `IsMinimalServiceCurve β S` — `A ∗ β ≤ D` on
served pairs, `β : ℝ≥0 → EReal` — and the largest such relation
`minimalServiceRel β`: a server when `β 0 ≤ 0`, empty when `β 0 > 0`, and
every server offers the zero curve `betaZero`. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- A curve viewed in `EReal`: `t ↦ ((A t : ℝ) : EReal)`. -/
noncomputable def curveE (A : Curve) : ℝ≥0 → EReal :=
  fun t => ((A t : ℝ) : EReal)

/-- `curveE A` is nonnegative: `0 ≤ curveE A t`. -/
theorem curveE_nonneg (A : Curve) (t : ℝ≥0) : (0 : EReal) ≤ curveE A t := by
  show (0 : EReal) ≤ ((A t : ℝ) : EReal); positivity

/-- `curveE A` is never `⊥`: each value is a real coercion. -/
theorem curveE_neverBot (A : Curve) : NeverBot (curveE A) :=
  fun _ => EReal.coe_ne_bot _

/-- `curveE A 0 = 0`. -/
theorem curveE_zero (A : Curve) : curveE A 0 = 0 := by
  show ((A 0 : ℝ) : EReal) = 0
  have : A 0 = 0 := A.zero
  rw [this]; norm_num

/-- Curve order matches the `EReal` view: `D ≤ A ↔ curveE D ≤ curveE A`. -/
theorem curveE_le_iff {D A : Curve} : curveE D ≤ curveE A ↔ D ≤ A := by
  constructor
  · intro h t
    have := h t
    show D t ≤ A t
    have : ((D t : ℝ) : EReal) ≤ ((A t : ℝ) : EReal) := this
    exact_mod_cast this
  · intro h t
    show ((D t : ℝ) : EReal) ≤ ((A t : ℝ) : EReal)
    exact_mod_cast h t

/-- Curve order transfers to the `EReal` view: `D ≤ A → curveE D ≤ curveE A`. -/
theorem curveE_mono {D A : Curve} (h : D ≤ A) : curveE D ≤ curveE A :=
  curveE_le_iff.mpr h

/-- `curveE A` is monotone in time (contrast `curveE_mono`: monotonicity in
the curve argument). -/
theorem monotone_curveE (A : Curve) : Monotone (curveE A) := by
  intro a b hab
  show ((A a : ℝ) : EReal) ≤ ((A b : ℝ) : EReal)
  exact_mod_cast A.mono hab

/-- `curveE A` is left-continuous. -/
theorem isLeftContinuous_curveE (A : Curve) :
    IsLeftContinuous (curveE A) := fun t =>
  ((continuous_coe_real_ereal.comp NNReal.continuous_coe).continuousAt
    ).comp_continuousWithinAt (A.leftCont t)

/-- `curveE` values are real coercions, so they are `AddDefined` with
anything. -/
theorem addDefined_curveE (A : Curve) (u : ℝ≥0) (x : EReal) :
    AddDefined (curveE A u) x :=
  ⟨Or.inl (EReal.coe_ne_top _), Or.inl (EReal.coe_ne_bot _)⟩

/-- `S` offers `EReal`-valued min-plus service curve `beta`: every served pair
satisfies `A ∗ beta ≤ D` (i.e. `D ≥ A ∗ beta`), the curve pair lifted into
`EReal` via `curveE`. -/
def IsMinimalServiceCurve (beta : ℝ≥0 → EReal) (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → minConv (curveE A) beta ≤ curveE D

/-- When `beta 0 ≤ 0`, each input is its own output: `A` serves itself, since the
`(t, 0)` split gives `A ∗ beta ≤ A`. The left-total witness for the relation. -/
theorem minConv_self_le {beta : ℝ≥0 → EReal} (h0 : beta 0 ≤ 0) (A : Curve) :
    minConv (curveE A) beta ≤ curveE A := by
  refine fun t => le_trans (minConv_le_add _ _ (add_zero t)) ?_
  calc curveE A t + beta 0 ≤ curveE A t + 0 := by gcongr
    _ = curveE A t := add_zero _

/-- `(A, D)` is a min-plus service pair of `beta`: `A ≥ D ≥ A ∗ beta`, on
`T`-valued cumulative functions (the value-type-generic core of
`minimalServiceRel`). -/
def minimalServicePair {T : Type*} [Add T] [InfSet T] [LE T]
    (beta : ℝ≥0 → T) (A D : ℝ≥0 → T) : Prop :=
  D ≤ A ∧ minConv A beta ≤ D

/-- The min-plus service relation of `beta`: the causal pairs meeting
`A ∗ beta ≤ D`, i.e. `A ≥ D ≥ A ∗ beta`, read through `curveE`. Depends on
`beta` alone. -/
def minimalServiceRel (beta : ℝ≥0 → EReal) : Curve → Curve → Prop :=
  fun A D => minimalServicePair beta (curveE A) (curveE D)

/-- `minimalServiceRel beta A D` unfolds to `A ≥ D` and `A ∗ beta ≤ D`. -/
theorem mem_minimalServiceRel_iff {beta : ℝ≥0 → EReal} {A D : Curve} :
    minimalServiceRel beta A D ↔
      D ≤ A ∧ minConv (curveE A) beta ≤ curveE D := by
  rw [show (minimalServiceRel beta A D) ↔
        (curveE D ≤ curveE A ∧ minConv (curveE A) beta ≤ curveE D) from Iff.rfl,
    curveE_le_iff]

/-- When `beta 0 ≤ 0`, `minimalServiceRel beta` is a server: causality is the first
conjunct, and left-totality holds since each input serves itself. -/
theorem isServer_minimalServiceRel {beta : ℝ≥0 → EReal} (h0 : beta 0 ≤ 0) :
    IsServer (minimalServiceRel beta) :=
  ⟨fun _ _ hp => curveE_le_iff.mp hp.1,
    fun A => ⟨A, le_refl _, minConv_self_le h0 A⟩⟩

/-- The largest server offering `beta` (for `beta 0 ≤ 0`) is the relation
`minimalServiceRel beta`; any server `S` offering `beta` is contained in it. -/
theorem subset_minimalServiceRel {beta : ℝ≥0 → EReal} {S : Curve → Curve → Prop}
    (hS : IsMinimalServiceCurve beta S) (hSrv : IsServer S) :
    ∀ A D, S A D → minimalServiceRel beta A D := by
  intro A D hp
  exact ⟨curveE_mono (hSrv.1 _ _ hp), hS A D hp⟩

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

/-- `A ∗ beta₀ = beta₀` for any curve: the `(0, t)` split gives `curveE A 0 = 0`,
and every other term `curveE A u + 0 = curveE A u ≥ 0`, so the infimum is `0`. -/
theorem minConv_betaZero (A : Curve) :
    minConv (curveE A) betaZero = betaZero := by
  funext t
  refine le_antisymm ?_ ?_
  · refine le_trans
      (ciInf_le_of_le (OrderBot.bddBelow _) ⟨(0, t), by simp⟩ (le_refl _)) ?_
    show curveE A 0 + betaZero t ≤ betaZero t
    rw [curveE_zero]; show (0 : EReal) + 0 ≤ betaZero t; simp [betaZero]
  · refine le_iInf (fun p => ?_)
    show betaZero t ≤ curveE A p.1.1 + betaZero p.1.2
    show (0 : EReal) ≤ curveE A p.1.1 + 0
    rw [add_zero]; exact curveE_nonneg A p.1.1

/-- `A ∗ beta₀ ≤ D` for any curves: `A ∗ beta₀ = beta₀ = 0 ≤ curveE D`. -/
theorem minConv_betaZero_le (A D : Curve) :
    minConv (curveE A) betaZero ≤ curveE D := by
  rw [minConv_betaZero]; exact fun t => curveE_nonneg D t

/-- The zero-service chain on any server: `S A D` gives
`A ≥ D ≥ A ∗ beta₀ = beta₀`. -/
theorem betaZero_chain {S : Curve → Curve → Prop} (hSrv : IsServer S)
    {A D : Curve} (h : S A D) :
    D ≤ A ∧ minConv (curveE A) betaZero ≤ curveE D ∧
      minConv (curveE A) betaZero = betaZero :=
  ⟨hSrv.1 _ _ h, minConv_betaZero_le A D, minConv_betaZero A⟩

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
    (A D : Curve) (hcaus : curveE D ≤ curveE A)
    (hconv : minConv (curveE A) beta ≤ curveE D) : False := by
  have hconv0 : minConv (curveE A) beta 0 ≤ curveE D 0 := hconv 0
  have hcaus0 : curveE D 0 ≤ curveE A 0 := hcaus 0
  have hsplit : minConv (curveE A) beta 0 = curveE A 0 + beta 0 := by
    unfold minConv
    refine le_antisymm
      (ciInf_le_of_le (OrderBot.bddBelow _) ⟨(0, 0), by simp⟩ (le_refl _)) ?_
    refine le_iInf ?_
    rintro ⟨⟨u, s⟩, hus⟩
    obtain ⟨rfl, rfl⟩ : u = 0 ∧ s = 0 := by constructor <;> simp_all
    simp
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
