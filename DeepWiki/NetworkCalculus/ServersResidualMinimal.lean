import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import DeepWiki.NetworkCalculus.ServersResidual
import DeepWiki.NetworkCalculus.ServiceCurvePackets

/-! # Min-plus aggregates leave no residual
The strict aggregate hypothesis of blind multiplexing is essential: a
merely min-plus aggregate service curve admits a server that starves a
flow forever — the backlogged period never ends, and the service can be
assigned entirely to the cross-traffic. The witness: a rate-`1` flow
and a unit burst served greedily through `β_{2,2}`, with the whole
output assigned to the rate flow; the burst flow receives nothing,
while the residual formula promises it eventual service.

What does survive a min-plus aggregate is only the *raw* difference
`β − ∑_{j≠i} αⱼ` (`residualCurveEReal`, `EReal`-valued): a min-plus
residual service curve that may take negative values, hence cannot feed
performance bounds — the book's warning theorem. -/

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

/-- The witness pairs are causal. -/
theorem mpWitness_causal :
    ∀ j : Fin 2, (![mpWitnessD, zeroCurve] j)
      ≤ (![mpWitnessRate, stepCurve 0 1] j) := by
  intro j
  fin_cases j
  · intro u
    show mpWitnessD u ≤ mpWitnessRate u
    rw [mpWitnessD_apply, mpWitnessRate_apply]
    by_cases h2 : 2 < u
    · rw [if_pos h2]
      exact le_trans (min_le_right _ _) tsub_le_self
    · rw [if_neg h2]
      exact zero_le
  · intro u
    show zeroCurve u ≤ stepCurve 0 1 u
    rw [zeroCurve_apply]
    exact zero_le

/-- The rate flow is constrained by the identity arrival curve. -/
theorem mpWitnessRate_arrivalBound :
    IsMaximalArrivalBound ⇑mpWitnessRate (fun v => v) := by
  rw [isMaximalArrivalBound_iff_increment]
  intro t d
  show mpWitnessRate (t + d) ≤ mpWitnessRate t + d
  rw [mpWitnessRate_apply, mpWitnessRate_apply]

/-- The witness aggregate is served at the min-plus `β_{2,2}`: the
greedy output realizes an optimal split in each regime. -/
theorem mpWitness_minimal_aggregate :
    ∀ x, minConv (Deviation.liftENN
        (fun y => ∑ j, ((![mpWitnessRate, stepCurve 0 1] : Fin 2 → Curve) j) y))
      (Deviation.liftENN (rateLatency 2 2)) x
      ≤ ((∑ j, ((![mpWitnessD, zeroCurve] : Fin 2 → Curve) j) x : ℝ≥0) : ℝ≥0∞) := by
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
    · rw [if_neg h2, tsub_eq_zero_of_le (not_lt.mp h2), mul_zero]

/-- The violation: the burst flow is promised at least one unit by time
`6` while it is served nothing. -/
theorem one_le_minConv_residualCurve_mpWitness :
    (1 : ℝ≥0∞) ≤ minConv (Deviation.liftENN ⇑(stepCurve 0 1))
      (Deviation.liftENN (residualCurve (rateLatency 2 2)
        (fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 1,
          (fun _ v => v) j v))) 6 := by
  have hβmono : Monotone (rateLatency (2 : ℝ≥0) 2) :=
    fun a b hab => mul_le_mul_right (tsub_le_tsub_right hab 2) 2
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

/-- **A min-plus aggregate does not yield the blind-multiplexing
residual**: the statement of the strict theorem with the aggregate
hypothesis weakened to the min-plus service inequality is false. -/
theorem not_forall_minConv_residualCurve_le_of_minimal_aggregate :
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
    mpWitness_causal
    -- the min-plus aggregate service inequality, by exhibiting splits
    mpWitness_minimal_aggregate
    1
    (by
      intro j hj
      fin_cases j
      · exact mpWitnessRate_arrivalBound
      · exact absurd rfl hj)
    6
  have hzero := le_trans one_le_minConv_residualCurve_mpWitness hbad
  rw [show ((![mpWitnessD, zeroCurve] : Fin 2 → Curve) 1) = zeroCurve
      from rfl, zeroCurve_apply] at hzero
  exact absurd hzero (by norm_num)

/-! ## The raw min-plus residual
The residual that *does* survive a min-plus aggregate: the raw
`EReal`-valued difference `β − α`, with no truncation and no closure.
It may be negative, so it cannot feed performance bounds. -/

/-- The raw min-plus residual `v ↦ β v − α v` (`EReal`-valued: no
truncation, no closure); it may take negative values. -/
noncomputable def residualCurveEReal (β : ℝ≥0 → EReal) (α : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → EReal :=
  fun v => β v - ((α v : ℝ) : EReal)

/-- `residualCurveEReal β α v = β v − α v`: the pointwise reading. -/
@[simp] theorem residualCurveEReal_apply (β : ℝ≥0 → EReal)
    (α : ℝ≥0 → ℝ≥0) (v : ℝ≥0) :
    residualCurveEReal β α v = β v - ((α v : ℝ) : EReal) := rfl

/-- `residualCurveEReal β α 0 = 0` when both curves are null at the
origin. -/
theorem residualCurveEReal_zero_eq {β : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0}
    (hβ0 : β 0 = 0) (hα0 : α 0 = 0) :
    residualCurveEReal β α 0 = 0 := by
  rw [residualCurveEReal_apply, hβ0, hα0]
  simp

/-- The raw residual is dominated by the truncated-closed residual of
blind multiplexing: `β − α ≤ [β − α]⁺↑` pointwise through `liftEReal`
(monotonicity of `β` prefix-bounds the closure). -/
theorem residualCurveEReal_le_liftEReal_residualCurve {β α : ℝ≥0 → ℝ≥0}
    (hβmono : Monotone β) (v : ℝ≥0) :
    residualCurveEReal (liftEReal β) α v
      ≤ liftEReal (residualCurve β α) v := by
  rw [residualCurveEReal_apply,
    show liftEReal β v - ((α v : ℝ) : EReal)
        = ((((β v : ℝ) - (α v : ℝ)) : ℝ) : EReal) from
      (EReal.coe_sub _ _).symm]
  by_cases hle : α v ≤ β v
  · rw [show ((β v : ℝ) - (α v : ℝ)) = ((β v - α v : ℝ≥0) : ℝ) from
        (NNReal.coe_sub hle).symm]
    have h := tsub_le_residualCurve (α := α)
      (closureBddAbove_tsub_of_monotone hβmono) (le_refl v)
    exact_mod_cast h
  · refine le_trans ?_ (isNonneg_liftEReal (residualCurve β α) v)
    have hlt : (β v : ℝ) - (α v : ℝ) ≤ 0 := by
      have h := (not_le.mp hle).le
      have : (β v : ℝ) ≤ (α v : ℝ) := by exact_mod_cast h
      linarith
    exact_mod_cast hlt

/-- **The raw residual can be negative**: against the rate-latency
aggregate `β_{2,2}` and rate-`1` cross-traffic, the residual at `1` is
`−1 < 0` — the warning that bars it from performance bounds. -/
theorem residualCurveEReal_rateLatency_neg :
    residualCurveEReal (liftEReal (rateLatency 2 2)) (fun v => v) 1 < 0 := by
  have h1 : (rateLatency (2 : ℝ≥0) 2) 1 = 0 := by
    show (2 : ℝ≥0) * (1 - 2) = 0
    rw [tsub_eq_zero_of_le (by norm_num), mul_zero]
  show ((((rateLatency 2 2) 1 : ℝ≥0) : ℝ) : EReal)
      - (((1 : ℝ≥0) : ℝ) : EReal) < 0
  rw [h1, ← EReal.coe_sub]
  exact EReal.coe_neg'.mpr (by norm_num)

/-- **Blind multiplexing from a min-plus aggregate** (the warning
theorem, pair level): an aggregate served at a min-plus `β` with
`αⱼ`-bounded cross-traffic serves flow `i` at the raw residual
`β − ∑_{j≠i} αⱼ`. The book assumes `β` left-continuous to attain the
aggregate split; an `ε`-approximate split makes the hypothesis
unnecessary. The residual may be negative, so — unlike the
strict-aggregate residual — this cannot feed performance bounds. -/
theorem minConv_residualCurveEReal_le_of_minimal_aggregate {ι : Type*}
    [Fintype ι] {As Ds : ι → Curve} {β : ℝ≥0 → EReal}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hserv : minConv (liftEReal (fun x => ∑ j, (As j) x)) β
      ≤ liftEReal (fun x => ∑ j, (Ds j) x))
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (curveEReal (As i))
        (residualCurveEReal β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v)) t
      ≤ curveEReal (Ds i) t := by
  by_contra hcon
  rw [not_le] at hcon
  -- a real level strictly between the target and the convolution
  obtain ⟨c, hc1, hc2⟩ := EReal.exists_between_coe_real hcon
  set ε : ℝ := c - ((Ds i) t : ℝ) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    refine sub_pos.mpr ?_
    have hc1' : ((((Ds i) t : ℝ)) : EReal) < (c : EReal) := hc1
    exact_mod_cast hc1'
  -- `ε`-room: some split of the aggregate convolution undershoots
  have hex : ∃ u v : ℝ≥0, u + v = t
      ∧ liftEReal (fun x => ∑ j, (As j) x) u + β v
        < liftEReal (fun x => ∑ j, (Ds j) x) t + (ε : EReal) := by
    by_contra hall
    push Not at hall
    have hle : liftEReal (fun x => ∑ j, (Ds j) x) t + (ε : EReal)
        ≤ minConv (liftEReal (fun x => ∑ j, (As j) x)) β t :=
      le_minConv fun u v huv => hall u v huv
    have hch := le_trans hle (hserv t)
    have : ((∑ j, (Ds j) t : ℝ≥0) : ℝ) + ε
        ≤ ((∑ j, (Ds j) t : ℝ≥0) : ℝ) := by exact_mod_cast hch
    linarith
  obtain ⟨u, v, huv, hsplit⟩ := hex
  -- flow `i`'s convolution at the same split exceeds `c`
  have hqlt : (c : EReal) < curveEReal (As i) u
      + residualCurveEReal β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v) v :=
    lt_of_lt_of_le hc2 (minConv_le_add _ _ huv)
  by_cases hbot : β v = ⊥
  · rw [residualCurveEReal_apply, hbot, EReal.bot_sub, EReal.add_bot]
      at hqlt
    exact absurd hqlt (not_lt.mpr bot_le)
  · have htop : β v ≠ ⊤ := by
      intro htop
      rw [htop, EReal.coe_add_top] at hsplit
      exact absurd hsplit (not_lt.mpr le_top)
    obtain ⟨b, hb⟩ : ∃ b : ℝ, β v = (b : EReal) :=
      ⟨(β v).toReal, (EReal.coe_toReal htop hbot).symm⟩
    -- the split inequality, decomposed over flow `i` and the rest
    have hsplitR : (((As i) u : ℝ)
          + ∑ j ∈ Finset.univ.erase i, ((As j) u : ℝ)) + b
        < (((Ds i) t : ℝ)
          + ∑ j ∈ Finset.univ.erase i, ((Ds j) t : ℝ)) + ε := by
      rw [hb] at hsplit
      have h' : ((∑ j, (As j) u : ℝ≥0) : ℝ) + b
          < ((∑ j, (Ds j) t : ℝ≥0) : ℝ) + ε := by exact_mod_cast hsplit
      rw [← Finset.add_sum_erase Finset.univ (fun j => (As j) u)
            (Finset.mem_univ i),
        ← Finset.add_sum_erase Finset.univ (fun j => (Ds j) t)
            (Finset.mem_univ i)] at h'
      push_cast at h'
      linarith
    -- causality + the arrival bounds control the cross-traffic
    have hcross : ∑ j ∈ Finset.univ.erase i, ((Ds j) t : ℝ)
        ≤ (∑ j ∈ Finset.univ.erase i, ((As j) u : ℝ))
          + ∑ j ∈ Finset.univ.erase i, ((α j v : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j hj => ?_
      have hinc : (As j) t ≤ (As j) u + α j v := by
        have h := (isMaximalArrivalBound_iff_increment _ _).mp
          (harr j (Finset.ne_of_mem_erase hj)) u v
        rwa [huv] at h
      exact_mod_cast le_trans (hc j t) hinc
    -- the flow-`i` reading of the gap
    have hqltR : c < ((As i) u : ℝ)
        + (b - ((∑ j ∈ Finset.univ.erase i, α j v : ℝ≥0) : ℝ)) := by
      rw [residualCurveEReal_apply, hb, curveEReal_apply,
        ← EReal.coe_sub, ← EReal.coe_add] at hqlt
      exact_mod_cast hqlt
    push_cast at hqltR
    linarith

/-- **The residual server from a min-plus aggregate** (relation form):
restricting an `n`-server whose aggregate is served at a min-plus `β`
to pairs with `αⱼ`-constrained cross-traffic, the residual server for
flow `i` offers the raw `EReal`-valued residual `β − ∑_{j≠i} αⱼ` as a
min-plus service curve. -/
theorem isMinimalServiceCurve_residualServer_of_minimal_aggregate
    {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → EReal}
    {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsMinimalServiceCurve β (aggregateServer S)) :
    IsMinimalServiceCurve
      (residualCurveEReal β (fun v => ∑ j ∈ Finset.univ.erase i, α j v))
      (residualServer (fun A D => S A D ∧
        ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(A j) (α j)) i) := by
  rintro Ai Di ⟨As, Ds, ⟨hp, harr⟩, rfl, rfl⟩
  intro t
  exact minConv_residualCurveEReal_le_of_minimal_aggregate
    (fun j => hcaus As Ds hp j) (hβ.sum_minConv_le hp) harr t

/-! ## Book restatement (blind multiplexing from a min-plus aggregate)
An `n`-server offering a left-continuous min-plus service curve `β`
whose arrival processes have arrival curves `αⱼ`: the residual server
for flow `i` offers the min-plus service curve `β − ∑_{j≠i} αⱼ`. The
result is a warning — the residual may be negative
(`residualCurveEReal_rateLatency_neg`), so it cannot be applied to
compute performance bounds. (The book's left-continuity of `β` is
unnecessary: the proof takes an `ε`-approximate split instead of an
attained one.) -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → EReal}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hSrv : IsServerN S)
    (_hβlc : IsLeftContinuous β)
    (hβ : IsMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalCurve ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (curveEReal (As i))
        (residualCurveEReal β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v)) t
      ≤ curveEReal (Ds i) t :=
  minConv_residualCurveEReal_le_of_minimal_aggregate
    (fun j => hSrv.1 As Ds hp j)
    (hβ.sum_minConv_le hp)
    (fun j hj => (harr j hj).2) t

end DeepWiki
