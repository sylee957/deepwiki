import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Book.ServersResidual
import Book.ServiceCurvePackets

/-! # Min-plus aggregates leave no residual
The strict aggregate hypothesis of blind multiplexing is essential: a
merely min-plus aggregate service curve admits a server that starves a
flow forever — the backlogged period never ends, and the service can be
assigned entirely to the cross-traffic. The witness: a rate-`1` flow
and a unit burst served greedily through `β_{2,2}`, with the whole
output assigned to the rate flow; the burst flow receives nothing,
while the residual formula promises it eventual service. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The rate-`1` arrival `t ↦ t` as a curve. -/
noncomputable def mpWitnessRate : Curve :=
  afterCurve 0 id monotone_id continuous_id

/-- `mpWitnessRate u = u`. -/
theorem mpWitnessRate_apply (u : ℝ≥0) : mpWitnessRate u = u := by
  rw [mpWitnessRate, afterCurve_apply]
  rcases eq_zero_or_pos u with rfl | hu
  · rw [if_neg (lt_irrefl 0)]
  · rw [if_pos hu]
    rfl

/-- The greedy output of the aggregate through `β_{2,2}`: nothing up to
`2`, rate `2` on `[2, 3]`, then `t − 1`. -/
noncomputable def mpWitnessD : Curve :=
  afterCurve 2 (fun w => min (2 * (w - 2)) (w - 1))
    (fun _ _ hab => min_le_min
      (mul_le_mul_right (tsub_le_tsub_right hab 2) 2)
      (tsub_le_tsub_right hab 1))
    ((continuous_const.mul
        (continuous_sub.comp (continuous_id.prodMk continuous_const))).min
      (continuous_sub.comp (continuous_id.prodMk continuous_const)))

/-- `mpWitnessD` reads off as the clamped two-piece minimum. -/
theorem mpWitnessD_apply (u : ℝ≥0) :
    mpWitnessD u = if 2 < u then min (2 * (u - 2)) (u - 1) else 0 := rfl

/-- **A min-plus aggregate does not yield the blind-multiplexing
residual**: the statement of the strict theorem with the aggregate
hypothesis weakened to the min-plus service inequality is false. -/
theorem not_forall_minConv_residualCurve_le_of_minPlus_aggregate :
    ¬ ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (As Ds : ι → Curve) (β : ℝ≥0 → ℝ≥0) (α : ι → ℝ≥0 → ℝ≥0),
      (∀ j, Ds j ≤ As j) →
      (∀ x, minConv (Deviation.liftENN (fun y => ∑ j, (As j) y))
          (Deviation.liftENN β) x ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞)) →
      ∀ i, (∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j)) →
      ∀ t, minConv (Deviation.liftENN ⇑(As i))
          (Deviation.liftENN (residualCurve β
            (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
        ≤ (((Ds i) t : ℝ≥0) : ℝ≥0∞) := by
  intro h
  -- the witness family: a rate flow and a burst, all service to the rate
  have hβmono : Monotone (rateLatency (2 : ℝ≥0) 2) :=
    fun a b hab => mul_le_mul_right (tsub_le_tsub_right hab 2) 2
  have hbad := h (Fin 2) ![mpWitnessRate, stepCurve 0 1]
    ![mpWitnessD, zeroCurve] (rateLatency 2 2) (fun _ v => v)
    -- per-flow causality
    (by
      intro j
      fin_cases j
      · intro u
        show mpWitnessD u ≤ mpWitnessRate u
        rw [mpWitnessD_apply, mpWitnessRate_apply]
        by_cases h2 : 2 < u
        · rw [if_pos h2]
          exact le_trans (min_le_right _ _) tsub_le_self
        · rw [if_neg h2]
          exact zero_le'
      · intro u
        show zeroCurve u ≤ stepCurve 0 1 u
        rw [zeroCurve_apply]
        exact zero_le')
    -- the min-plus aggregate service inequality, by exhibiting splits
    (by
      intro x
      have hagg : ∀ y : ℝ≥0, (∑ j, (![mpWitnessRate, stepCurve 0 1] j) y)
          = mpWitnessRate y + stepCurve 0 1 y := fun y => Fin.sum_univ_two _
      have haggD : (∑ j, (![mpWitnessD, zeroCurve] j) x)
          = mpWitnessD x := by
        rw [Fin.sum_univ_two]
        show mpWitnessD x + zeroCurve x = mpWitnessD x
        rw [zeroCurve_apply, add_zero]
      rw [haggD]
      by_cases h3 : 3 < x
      · -- split `(x − 2, 2)`: the caught-up regime serves `x − 1`
        have hsplit : (x - 2) + 2 = x :=
          tsub_add_cancel_of_le (le_trans (by norm_num) h3.le)
        refine le_trans (minConv_le_add _ _ hsplit) ?_
        show (((∑ j, (![mpWitnessRate, stepCurve 0 1] j) (x - 2) : ℝ≥0))
              : ℝ≥0∞)
            + (((rateLatency (2:ℝ≥0) 2) 2 : ℝ≥0) : ℝ≥0∞)
          ≤ ((mpWitnessD x : ℝ≥0) : ℝ≥0∞)
        rw [hagg, mpWitnessRate_apply, ← ENNReal.coe_add,
          ENNReal.coe_le_coe]
        have h21 : (1 : ℝ≥0) < x - 2 := by
          have h32 : (3 : ℝ≥0) - 2 < x - 2 :=
            tsub_lt_tsub_right_of_le (by norm_num) h3
          rwa [show (3 : ℝ≥0) - 2 = 1 from tsub_eq_of_eq_add (by norm_num)]
            at h32
        rw [show stepCurve 0 1 (x - 2) = 1 from by
            rw [stepCurve_apply, if_pos (lt_trans one_pos h21)],
          show (rateLatency (2:ℝ≥0) 2) 2 = 0 from by
            show (2 : ℝ≥0) * (2 - 2) = 0
            rw [tsub_self, mul_zero],
          add_zero, mpWitnessD_apply,
          if_pos (lt_trans (by norm_num) h3)]
        refine le_min ?_ ?_
        · -- `x − 2 + 1 ≤ 2(x − 2)`, i.e. `1 ≤ x − 2` doubles
          rw [two_mul]
          exact add_le_add le_rfl h21.le
        · -- `x − 2 + 1 ≤ x − 1`
          have h2x : (2 : ℝ≥0) ≤ x := le_trans (by norm_num) h3.le
          have h1x : (1 : ℝ≥0) ≤ x := le_trans (by norm_num) h3.le
          rw [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_sub h2x,
            NNReal.coe_sub h1x, NNReal.coe_one]
          push_cast
          linarith
      · -- split `(0, x)`: the latency regime serves `2(x − 2)`
        refine le_trans (minConv_le_add _ _ (zero_add x)) ?_
        show (((∑ j, (![mpWitnessRate, stepCurve 0 1] j) 0 : ℝ≥0)) : ℝ≥0∞)
            + (((rateLatency (2:ℝ≥0) 2) x : ℝ≥0) : ℝ≥0∞)
          ≤ ((mpWitnessD x : ℝ≥0) : ℝ≥0∞)
        rw [hagg, mpWitnessRate_apply,
          show stepCurve 0 1 0 = 0 from by
            rw [stepCurve_apply, if_neg (lt_irrefl 0)],
          add_zero, ← ENNReal.coe_add, ENNReal.coe_le_coe, zero_add]
        show (2 : ℝ≥0) * (x - 2) ≤ mpWitnessD x
        rw [mpWitnessD_apply]
        by_cases h2 : 2 < x
        · rw [if_pos h2]
          refine le_min le_rfl ?_
          -- `2(x − 2) ≤ x − 1` on `(2, 3]`
          have h1x : (1 : ℝ≥0) ≤ x :=
            le_trans (by norm_num) h2.le
          rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub h2.le,
            NNReal.coe_sub h1x, NNReal.coe_one]
          have hx3 : (x : ℝ) ≤ 3 := by exact_mod_cast not_lt.mp h3
          push_cast
          linarith
        · rw [if_neg h2, tsub_eq_zero_of_le (not_lt.mp h2), mul_zero])
    1
    -- the rate flow is `id`-constrained
    (by
      intro j hj
      fin_cases j
      · rw [isMaximalArrivalBound_iff_increment]
        intro t d
        show mpWitnessRate (t + d) ≤ mpWitnessRate t + d
        rw [mpWitnessRate_apply, mpWitnessRate_apply]
      · exact absurd rfl hj)
    6
  -- the burst flow was promised service it never receives
  have hone : (1 : ℝ≥0∞) ≤ minConv (Deviation.liftENN ⇑(stepCurve 0 1))
      (Deviation.liftENN (residualCurve (rateLatency 2 2)
        (fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 1,
          (fun _ v => v) j v))) 6 := by
    refine le_minConv fun u v huv => ?_
    rcases eq_zero_or_pos u with rfl | hu
    · -- the empty split must pay the residual at `6`: at least `2`
      rw [zero_add] at huv
      subst huv
      refine le_trans ?_ le_add_self
      show (1 : ℝ≥0∞) ≤ ((residualCurve (rateLatency 2 2) _ 6 : ℝ≥0) : ℝ≥0∞)
      rw [show ((1 : ℝ≥0∞)) = ((1 : ℝ≥0) : ℝ≥0∞) from rfl,
        ENNReal.coe_le_coe]
      have hres := tsub_le_residualCurve
        (β := rateLatency 2 2)
        (α := fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 1,
          (fun _ v => v) j v)
        (closureBddAbove_tsub_of_monotone hβmono)
        (le_refl (6 : ℝ≥0))
      refine le_trans ?_ hres
      show (1 : ℝ≥0) ≤ (2 : ℝ≥0) * (6 - 2)
        - (∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 1, (6 : ℝ≥0))
      rw [show ((Finset.univ : Finset (Fin 2)).erase 1) = {0} from by decide,
        Finset.sum_singleton,
        show (6 : ℝ≥0) - 2 = 4 from tsub_eq_of_eq_add (by norm_num),
        show (2 : ℝ≥0) * 4 = 8 from by norm_num,
        show (8 : ℝ≥0) - 6 = 2 from tsub_eq_of_eq_add (by norm_num)]
      norm_num
    · -- any positive split already carries the burst
      refine le_trans ?_ le_self_add
      show (1 : ℝ≥0∞) ≤ ((stepCurve 0 1 u : ℝ≥0) : ℝ≥0∞)
      rw [stepCurve_apply, if_pos hu]
      norm_num
  have hzero := le_trans hone hbad
  rw [show ((![mpWitnessD, zeroCurve] : Fin 2 → Curve) 1) = zeroCurve
      from rfl, zeroCurve_apply] at hzero
  exact absurd hzero (by norm_num)

end DeepWiki
