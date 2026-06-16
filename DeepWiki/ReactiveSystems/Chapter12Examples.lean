import DeepWiki.ReactiveSystems.TimedBisimulationUntimedStrict
import DeepWiki.ReactiveSystems.TimedHennessyMilnerClocks

/-! # Untimed bisimilarity does not preserve timed-HML (Exercise 12.13)
Theorem 12.3 (timed-bisimilar states satisfy the same `Mt` formulae) would *fail*
if we only assumed *untimed* bisimilarity. The `√`-free witness is the §11.2 TLTS
(`witnessTLTS`): `A` and `B` are untimed bisimilar, but the formula
`y in ∃∃(y > 1 ∧ ⟨a⟩tt)` holds at `A` (delay `2`, then act) and fails at `B`
(which can only delay `≤ 1`). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The distinguishing formula `y in ∃∃(y > 1 ∧ ⟨a⟩tt)`. -/
def mt1213 : Mt Unit Unit :=
  .reset () (.existsDelay (.and (.guard (.atom () .gt 1)) (.dia () .tt)))

/-- `A` satisfies `y in ∃∃(y > 1 ∧ ⟨a⟩tt)`: delay `2` (reaching `A` with `y = 2`),
then perform the action to `Stop`. -/
theorem witnessTLTS_A_sat_mt1213 : TLTS.MtSatState witnessTLTS .A mt1213 := by
  have hv : ((Valuation.reset {()} (fun _ => (0 : ℝ≥0))).add 2) () = 2 := by
    rw [Valuation.add_apply, Valuation.reset_mem (show () ∈ ({()} : Set Unit) from rfl), zero_add]
  refine ⟨2, .A, trivial, ?_, .Stop, trivial, trivial⟩
  show satisfies _ (ClockConstraint.atom () Cmp.gt 1)
  simp only [satisfies, Cmp.holds, hv]
  norm_num

/-- `B` does *not* satisfy it: its only delay successor `B` requires `d ≤ 1`, so the
guard `y > 1` can never hold. -/
theorem witnessTLTS_B_unsat_mt1213 : ¬ TLTS.MtSatState witnessTLTS .B mt1213 := by
  rintro ⟨d, p', hdelay, hguard, -⟩
  cases p' with
  | A => exact hdelay
  | Stop => exact hdelay
  | B =>
    have hv : ((Valuation.reset {()} (fun _ => (0 : ℝ≥0))).add d) () = d := by
      rw [Valuation.add_apply, Valuation.reset_mem (show () ∈ ({()} : Set Unit) from rfl), zero_add]
    change satisfies _ (ClockConstraint.atom () Cmp.gt 1) at hguard
    simp only [satisfies, Cmp.holds, hv, Nat.cast_one] at hguard
    exact absurd hguard (not_lt.mpr hdelay)

/-- **Exercise 12.13** (§12.3, p.234). Theorem 12.3 fails for merely *untimed*
bisimilar states: there is a TLTS with untimed-bisimilar `p, q` and an `Mt` formula
satisfied by one but not the other. -/
theorem ex_12_13 :
    ∃ (Q : Type) (T : TLTS Q Unit) (p q : Q),
      T.UntimedBisimilar p q ∧
      ∃ F : Mt Unit Unit, T.MtSatState p F ∧ ¬ T.MtSatState q F :=
  ⟨ThreeState, witnessTLTS, .A, .B, A_untimedBisimilar_B,
   mt1213, witnessTLTS_A_sat_mt1213, witnessTLTS_B_unsat_mt1213⟩

end DeepWiki.ReactiveSystems
