import DeepWiki.NetworkCalculus.ServiceCurveWeaklyStrict
import DeepWiki.NetworkCalculus.ServiceCurveStrictEReal
import DeepWiki.NetworkCalculus.ClosuresEReal
import DeepWiki.NetworkCalculus.CurveDioidEReal

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

/-! ## `strict = wstrict` at the pure-delay curve `δ_T`
For the pure-delay curve `δ_T`, the strict and weakly-strict notions coincide:
both relations collapse to the single backlog bound "every backlogged period has
length at most `T`". The weakly-strict relation only constrains the *maximal*
period `(Start t, t]`, but `δ_T`'s `⊤`-past-`T` value propagates that bound to
*every* sub-period — so the apparently weaker start-anchored condition recovers
the full strict one. (For a general `β` the two differ; the pure-delay curve is
exactly where they agree.) -/

/-- **`δ_T` weakly-strict service is a backlog bound**: a pair is weakly-strictly
served by `δ_T` iff it is causal and the maximal backlogged period of every `t`
has length at most `T` — `δ_T`'s `⊤` past `T` forbids a longer `t − Start t`,
while up to `T` the bound is just monotonicity of `D`. -/
theorem mem_weaklyStrictServiceRelEReal_delay_iff {T : ℝ≥0} {A D : Curve} :
    weaklyStrictServiceRelEReal (delayEReal T) A D ↔
      D ≤ A ∧ ∀ t, t - start ⇑A ⇑D t ≤ T := by
  rw [mem_weaklyStrictServiceRelEReal_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hb t
    by_contra hcon
    rw [not_le] at hcon
    have hbnd := hb t
    simp only [delayEReal] at hbnd
    rw [delay_eq_top T hcon, curveEReal_apply, curveEReal_apply,
      EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at hbnd
    exact absurd hbnd (not_le.mpr (EReal.coe_lt_top _))
  · intro hb t
    simp only [delayEReal]
    rw [delay_eq_zero T (hb t), add_zero]
    exact monotone_curveEReal D (start_le ⇑A ⇑D t)

/-- **`strict = wstrict` at `δ_T`**: `S_strict(δ_T) = S_wstrict(δ_T)`. Both reduce
to the same backlog bound. `strict ⟹ wstrict` reads the bound on the maximal
period `(Start t, t]` (`isBacklogged_Ioc_start`); `wstrict ⟹ strict` lifts it to
an arbitrary period `(s, t]` since its start lies at or before `s`
(`start_le_of_isBacklogged`), so `t − s ≤ t − Start t ≤ T`. -/
theorem strictServiceRelEReal_delay_eq_weaklyStrictServiceRelEReal_delay {T : ℝ≥0} :
    strictServiceRelEReal (delayEReal T) = weaklyStrictServiceRelEReal (delayEReal T) := by
  funext A D
  apply propext
  rw [mem_strictServiceRelEReal_delay_iff, mem_weaklyStrictServiceRelEReal_delay_iff]
  refine and_congr_right fun hDA => ?_
  have hc : ∀ x, D x ≤ A x := fun x => hDA x
  constructor
  · intro hb t
    exact hb (start ⇑A ⇑D t) t (start_le ⇑A ⇑D t) (isBacklogged_Ioc_start hc t)
  · intro hb s t hst hbl
    exact le_trans (tsub_le_tsub_left (start_le_of_isBacklogged hbl) t) (hb t)

/-! ## The hierarchy collapses at `δ_0`
At the strongest pure-delay curve `δ_0` (`= convUnitEReal`, the min-plus unit) the three
extended service notions coincide: `S_strict(δ_0) = S_wstrict(δ_0) = S_mp(δ_0)`, all equal
to the causal-equality relation `D = A` — a `δ_0`-server forbids every proper backlogged
period, in each sense. This is the top of the `vcn ⊆ strict ⊆ wstrict ⊆ mp` hierarchy
pinching shut, combining `strict = wstrict @ δ_T` (at `T = 0`) with `wstrict = mp @ δ_0`. -/

/-- `δ_0` (`= delayEReal 0`) is the min-plus unit `convUnitEReal` (on `ℝ≥0`, `t ≤ 0 ↔
t = 0`); mirrors the catalog `delayEReal_zero_eq_convUnitEReal` for import-DAG reasons. -/
theorem delayEReal_zero_eq_convUnitEReal' :
    (delayEReal 0 : ℝ≥0 → EReal) = convUnitEReal := by
  funext t; simp [convUnitEReal]

/-- `S_strict(δ_0) = S_wstrict(δ_0)`: the `T = 0` case of `strict = wstrict @ δ_T`, read
through `δ_0 = delayEReal 0 = convUnitEReal`. -/
theorem strictServiceRelEReal_convUnitEReal_eq_weaklyStrict :
    strictServiceRelEReal convUnitEReal = weaklyStrictServiceRelEReal convUnitEReal := by
  rw [← delayEReal_zero_eq_convUnitEReal']
  exact strictServiceRelEReal_delay_eq_weaklyStrictServiceRelEReal_delay

/-- **The hierarchy collapses at `δ_0`**: `S_strict(δ_0) = S_mp(δ_0)`, both the
causal-equality relation. With `weaklyStrictServiceRelEReal_convUnitEReal_eq`, the three
notions `strict`, `wstrict`, `mp` all coincide at `δ_0`. -/
theorem strictServiceRelEReal_convUnitEReal_eq :
    strictServiceRelEReal convUnitEReal = minimalServiceRel convUnitEReal := by
  rw [strictServiceRelEReal_convUnitEReal_eq_weaklyStrict,
    weaklyStrictServiceRelEReal_convUnitEReal_eq]

end DeepWiki
