import Book.Servers
import Book.RealConvolution
import Book.ECurveDioid

/-! # Min-plus service curves
Min-plus service curves `β : ℝ≥0 → EReal`: the convolution bound `D ≥ A ∗ β` on a
server's pairs, and the largest server `MinPlusServer β` offering a given `β`.
`β` may take negative (and `±∞`) values, so it is `EReal`-valued. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- A curve viewed in `EReal`: `t ↦ ((A t : ℝ) : EReal)`. -/
noncomputable def curveE (A : Curve) : ℝ≥0 → EReal :=
  fun t => ((A t : ℝ) : EReal)

/-- `curveE A` is nonnegative: `0 ≤ curveE A t`. -/
theorem curveE_nonneg (A : Curve) (t : ℝ≥0) : (0 : EReal) ≤ curveE A t := by
  show (0 : EReal) ≤ ((A t : ℝ) : EReal); positivity

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

/-- `S` offers `EReal`-valued min-plus service curve `beta`: every served pair
satisfies `A ∗ beta ≤ D` (i.e. `D ≥ A ∗ beta`), the curve pair lifted into
`EReal` via `curveE`. -/
def IsMinPlusServiceCurve (beta : ℝ≥0 → EReal) (S : Server) : Prop :=
  ∀ A D : Curve, (A, D) ∈ S → minConv (curveE A) beta ≤ curveE D

/-- When `beta 0 ≤ 0`, each input is its own output: `A` serves itself, since the
`(t, 0)` split gives `A ∗ beta ≤ A`. The left-total witness for `MinPlusServer`. -/
theorem minConv_self_le {beta : ℝ≥0 → EReal} (h0 : beta 0 ≤ 0) (A : Curve) :
    minConv (curveE A) beta ≤ curveE A := by
  refine fun t => le_trans
    (ciInf_le_of_le (OrderBot.bddBelow _) ⟨(t, 0), by simp⟩ (le_refl _)) ?_
  show curveE A t + beta 0 ≤ curveE A t
  calc curveE A t + beta 0 ≤ curveE A t + 0 := by gcongr
    _ = curveE A t := add_zero _

/-- The largest server offering min-plus service curve `beta` (with `beta 0 ≤ 0`):
the causal pairs meeting `A ∗ beta ≤ D`, i.e. `{(A, D) | A ≥ D ≥ A ∗ beta}`.
Causality is the first conjunct; left-totality holds as each input serves
itself. -/
def MinPlusServer (beta : ℝ≥0 → EReal) (h0 : beta 0 ≤ 0) : Server :=
  ⟨{ (A, D) | curveE D ≤ curveE A ∧ minConv (curveE A) beta ≤ curveE D },
    fun _ hp => curveE_le_iff.mp hp.1,
    fun A => ⟨A, le_refl _, minConv_self_le h0 A⟩⟩

/-- Membership in `MinPlusServer beta h0`: `A ≥ D` and `A ∗ beta ≤ D`. -/
theorem mem_MinPlusServer_iff {beta : ℝ≥0 → EReal} (h0 : beta 0 ≤ 0)
    {A D : Curve} :
    (A, D) ∈ MinPlusServer beta h0 ↔
      D ≤ A ∧ minConv (curveE A) beta ≤ curveE D := by
  rw [show ((A, D) ∈ MinPlusServer beta h0) ↔
        (curveE D ≤ curveE A ∧ minConv (curveE A) beta ≤ curveE D) from Iff.rfl,
    curveE_le_iff]

/-- `MinPlusServer beta h0` is the largest server offering `beta`: any server `S`
offering `beta` is contained in it. -/
theorem le_MinPlusServer {beta : ℝ≥0 → EReal} (h0 : beta 0 ≤ 0) {S : Server}
    (hS : IsMinPlusServiceCurve beta S) : S ≤ MinPlusServer beta h0 := by
  rintro ⟨A, D⟩ hp
  exact ⟨curveE_mono (S.causal hp), hS A D hp⟩

/-- A server offers `beta` iff it is contained in `MinPlusServer beta h0`. -/
theorem isMinPlusServiceCurve_iff_le {beta : ℝ≥0 → EReal} (h0 : beta 0 ≤ 0)
    {S : Server} :
    IsMinPlusServiceCurve beta S ↔ S ≤ MinPlusServer beta h0 := by
  refine ⟨le_MinPlusServer h0, fun h A D hp => ?_⟩
  exact ((mem_MinPlusServer_iff h0).mp (h hp)).2

/-- Min-plus service curves are antitone: a smaller `beta` is still offered, since
`minConv` is monotone in its right argument. -/
theorem IsMinPlusServiceCurve.mono
    {S : Server} {beta beta' : ℝ≥0 → EReal}
    (h : beta ≤ beta') (hS : IsMinPlusServiceCurve beta' S) :
    IsMinPlusServiceCurve beta S := by
  intro A D hp t
  refine le_trans ?_ (hS A D hp t)
  refine le_iInf (fun p => ?_)
  exact le_trans (ciInf_le (OrderBot.bddBelow _) p) (by gcongr; exact h p.1.2)

/-- The trivial zero service curve `beta ≡ 0` (`EReal`-valued). -/
noncomputable def betaZero : ℝ≥0 → EReal := fun _ => 0

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

/-- The zero-service chain on any server: `(A, D) ∈ S` gives
`A ≥ D ≥ A ∗ beta₀ = beta₀`. -/
theorem betaZero_chain (S : Server) {A D : Curve} (h : (A, D) ∈ S) :
    D ≤ A ∧ minConv (curveE A) betaZero ≤ curveE D ∧
      minConv (curveE A) betaZero = betaZero :=
  ⟨S.causal h, minConv_betaZero_le A D, minConv_betaZero A⟩

/-- Every server offers the zero service curve: `A ≥ D ≥ A ∗ beta₀ = beta₀`. -/
theorem isMinPlusServiceCurve_betaZero (S : Server) :
    IsMinPlusServiceCurve betaZero S :=
  fun A D _ => minConv_betaZero_le A D

/-- Every server is contained in `MinPlusServer betaZero`: since each server
offers the zero service curve, `S ≤ MinPlusServer betaZero`. -/
theorem le_MinPlusServer_betaZero (S : Server) :
    S ≤ MinPlusServer betaZero (le_refl 0) :=
  le_MinPlusServer (le_refl 0) (isMinPlusServiceCurve_betaZero S)

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
theorem serviceRel_eq_empty_of_pos {beta : ℝ≥0 → EReal}
    (h0 : (0 : EReal) < beta 0) :
    { (A, D) : Curve × Curve |
        curveE D ≤ curveE A ∧
          minConv (curveE A) beta ≤ curveE D } = ∅ := by
  ext ⟨A, D⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hcaus hconv => not_serviceCurve_of_pos h0 A D hcaus hconv

end DeepWiki
