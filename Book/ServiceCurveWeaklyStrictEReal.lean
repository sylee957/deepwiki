import Book.ServiceCurveWeaklyStrict
import Book.ClosuresEReal
import Book.CurveDioidEReal

/-! # Weakly strict service curves over extended (`EReal`) curves
Mirrors `strictServiceRelEReal`: the weakly-strict relation lifted to `ℝ≥0 → EReal`
service curves — the start-anchored bound `D(Start) + β(t − Start) ≤ D(t)` read through
`curveEReal` — so it can express `δ_0` (`= convUnitEReal`, `+∞` past the origin). The
`δ_0` case is the `wstrict = mp ⟺ β↑ = δ_0` forward step: both `S_wstrict(δ_0)` and
`S_mp(δ_0)` collapse to the causal-equality relation `D = A` (a `δ_0`-server passes its
input through unchanged, in both senses). -/

namespace DeepWiki

open Set
open scoped Classical NNReal ENNReal

/-- Largest causal relation offering the `EReal` weakly-strict service curve `beta`: the
start-anchored bound `D(Start t) + beta(t − Start t) ≤ D(t)` (read through `curveEReal`),
where `Start t = start ⇑A ⇑D t`. A `beta` value of `⊤` past the origin forbids any proper
backlogged period. -/
def weaklyStrictServiceRelEReal (beta : ℝ≥0 → EReal) : Curve → Curve → Prop :=
  fun A D => D ≤ A ∧ ∀ t,
    curveEReal D (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ curveEReal D t

/-- `weaklyStrictServiceRelEReal beta A D` unfolds to causality plus the start-anchored
`EReal` bound. -/
theorem mem_weaklyStrictServiceRelEReal_iff {beta : ℝ≥0 → EReal} {A D : Curve} :
    weaklyStrictServiceRelEReal beta A D ↔
      D ≤ A ∧ ∀ t,
        curveEReal D (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ curveEReal D t :=
  Iff.rfl

/-- `S_mp(δ_0)` is the causal-equality relation: `δ_0 ∗ A = A`, so `A ≥ D ≥ A` forces
`D = A`. -/
theorem minimalServiceRel_convUnitEReal_iff {A D : Curve} :
    minimalServiceRel convUnitEReal A D ↔ ∀ t, D t = A t := by
  rw [mem_minimalServiceRel_iff, minConv_convUnitEReal_right (isNeverBot_curveEReal A)]
  constructor
  · rintro ⟨hDA, hAD⟩ t
    refine le_antisymm (hDA t) ?_
    have h := hAD t
    rw [curveEReal_apply, curveEReal_apply] at h
    exact NNReal.coe_le_coe.mp (EReal.coe_le_coe_iff.mp h)
  · intro h
    refine ⟨fun t => (h t).le, fun t => ?_⟩
    rw [curveEReal_apply, curveEReal_apply]
    exact EReal.coe_le_coe_iff.mpr (NNReal.coe_le_coe.mpr (h t).ge)

/-- `S_wstrict(δ_0)` is the causal-equality relation: a proper backlogged period would
force `D(Start) + ⊤ ≤ D(t)`, impossible for a finite departure, so `D = A`. -/
theorem weaklyStrictServiceRelEReal_convUnitEReal_iff {A D : Curve} :
    weaklyStrictServiceRelEReal convUnitEReal A D ↔ ∀ t, D t = A t := by
  constructor
  · rintro ⟨hDA, hbound⟩ t
    refine le_antisymm (hDA t) ?_
    by_contra hcon
    rw [not_le] at hcon
    have hσlt : start ⇑A ⇑D t < t := by
      rcases (start_le ⇑A ⇑D t).lt_or_eq with hlt | heq
      · exact hlt
      · have hAD : (⇑A : ℝ≥0 → ℝ≥0) (start ⇑A ⇑D t) = (⇑D : ℝ≥0 → ℝ≥0) (start ⇑A ⇑D t) :=
          apply_start_eq A.leftCont D.leftCont (A.zero.trans D.zero.symm) (fun x => hDA x) t
        rw [heq] at hAD
        exact absurd hAD.symm (ne_of_lt hcon)
    have hb := hbound t
    rw [show convUnitEReal (t - start ⇑A ⇑D t) = ⊤ from
        if_neg (tsub_pos_of_lt hσlt).ne',
      EReal.add_top_of_ne_bot (by rw [curveEReal_apply]; exact EReal.coe_ne_bot _)] at hb
    exact absurd hb (not_le.mpr (by rw [curveEReal_apply]; exact EReal.coe_lt_top _))
  · intro h
    obtain rfl : D = A := Curve.ext h
    refine ⟨fun _ => le_refl _, fun t => ?_⟩
    rw [start_self, tsub_self]
    simp [convUnitEReal]

/-- **`wstrict = mp` at `δ_0`** (the forward step of `S_wstrict(β) = S_mp(β) ⟺ β↑ = δ_0`):
`S_wstrict(δ_0) = S_mp(δ_0)`, both being the causal-equality relation. -/
theorem weaklyStrictServiceRelEReal_convUnitEReal_eq :
    weaklyStrictServiceRelEReal convUnitEReal = minimalServiceRel convUnitEReal := by
  funext A D
  rw [propext (weaklyStrictServiceRelEReal_convUnitEReal_iff),
    propext (minimalServiceRel_convUnitEReal_iff)]

end DeepWiki
