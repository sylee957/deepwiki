import Mathlib.Topology.Order.Lattice
import DeepWiki.NetworkCalculus.ServersResidualMinimal

/-! # The blind-multiplexing residual is not strict
The residual of blind multiplexing is a min-plus service curve but not
in general a strict one: a server may flip priorities so that a flow
with backlogged data receives nothing for a whole interval, while the
aggregate keeps serving at exactly the strict rate. The witness: a
burst-plus-rate flow and a plain rate flow served at `λ₂` with the
priority flipped at `t = 1`; on `(1, 2]` flow `0` is backlogged and
frozen, yet the residual `[λ₂ − λ₁]⁺↑ = λ₁` promises it one unit. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The burst-plus-rate arrival `t ↦ t + 1` (for `t > 0`) as a curve:
a unit burst at `0⁺` on top of the unit rate. -/
noncomputable def flipWitnessA : Curve :=
  afterCurve 0 (fun w => w + 1)
    (fun _ _ hab => add_le_add hab le_rfl)
    (continuous_id.add continuous_const)

/-- `flipWitnessA u = u + 1` past `0`, `0` at `0`. -/
theorem flipWitnessA_apply (u : ℝ≥0) :
    flipWitnessA u = if 0 < u then u + 1 else 0 := rfl

/-- The flip-priority output of flow `0`: rate `2` while it has
priority on `[0, 1]`, frozen at `2` on `[1, 2]`, then rate `1`. -/
noncomputable def flipWitnessDBurst : Curve :=
  afterCurve 0 (fun w => min (2 * w) (max 2 w))
    (fun _ _ hab => min_le_min (mul_le_mul_right hab 2)
      (max_le_max le_rfl hab))
    ((continuous_const.mul continuous_id).min
      (continuous_const.max continuous_id))

/-- `flipWitnessDBurst` reads off as the unconditional two-piece minimum. -/
theorem flipWitnessDBurst_apply (u : ℝ≥0) :
    flipWitnessDBurst u = min (2 * u) (max 2 u) := by
  rw [flipWitnessDBurst, afterCurve_apply]
  rcases eq_zero_or_pos u with rfl | hu
  · rw [if_neg (lt_irrefl 0), mul_zero]
    exact (min_eq_left zero_le').symm
  · rw [if_pos hu]

/-- The flip-priority output of flow `1`: nothing while flow `0` has
priority, rate `2` on `[1, 2]` to catch up, then rate `1`. -/
noncomputable def flipWitnessDRate : Curve :=
  afterCurve 0 (fun w => min (2 * (w - 1)) w)
    (fun _ _ hab => min_le_min
      (mul_le_mul_right (tsub_le_tsub_right hab 1) 2) hab)
    ((continuous_const.mul
        (continuous_sub.comp (continuous_id.prodMk continuous_const))).min
      continuous_id)

/-- `flipWitnessDRate` reads off as the unconditional clamped minimum. -/
theorem flipWitnessDRate_apply (u : ℝ≥0) :
    flipWitnessDRate u = min (2 * (u - 1)) u := by
  rw [flipWitnessDRate, afterCurve_apply]
  rcases eq_zero_or_pos u with rfl | hu
  · rw [if_neg (lt_irrefl 0), zero_tsub, mul_zero]
    exact (min_self 0).symm
  · rw [if_pos hu]

/-- The witness pairs are causal. -/
theorem flipWitness_causal :
    ∀ j : Fin 2, (![flipWitnessDBurst, flipWitnessDRate] j)
      ≤ (![flipWitnessA, mpWitnessRate] j) := by
  intro j
  fin_cases j
  · intro u
    show flipWitnessDBurst u ≤ flipWitnessA u
    rw [flipWitnessDBurst_apply, flipWitnessA_apply]
    rcases eq_zero_or_pos u with rfl | hu
    · rw [if_neg (lt_irrefl 0), mul_zero]
      exact min_le_left _ _
    · rw [if_pos hu]
      by_cases h1 : u ≤ 1
      · refine le_trans (min_le_left _ _) ?_
        rw [two_mul]
        exact add_le_add le_rfl h1
      · refine le_trans (min_le_right _ _) (max_le ?_ le_self_add)
        calc (2 : ℝ≥0) = 1 + 1 := one_add_one_eq_two.symm
          _ ≤ u + 1 := add_le_add (not_le.mp h1).le le_rfl
  · intro u
    show flipWitnessDRate u ≤ mpWitnessRate u
    rw [flipWitnessDRate_apply, mpWitnessRate_apply]
    exact min_le_right _ _

/-- The witness aggregate output is exactly the strict rate:
`D₁(x) + D₂(x) = 2x` — the priority flip reassigns the service but
never wastes it. -/
theorem flipWitness_sum_eq (x : ℝ≥0) :
    flipWitnessDBurst x + flipWitnessDRate x = 2 * x := by
  rw [flipWitnessDBurst_apply, flipWitnessDRate_apply]
  by_cases h1 : x ≤ 1
  · -- flow `0` is served alone at rate `2`
    have h2x : 2 * x ≤ 2 := by
      calc 2 * x ≤ 2 * 1 := mul_le_mul_right h1 2
        _ = 2 := mul_one 2
    rw [min_eq_left (le_trans h2x (le_max_left 2 x)),
      tsub_eq_zero_of_le h1, mul_zero, min_eq_left zero_le', add_zero]
  · have h1x : (1 : ℝ≥0) ≤ x := (not_le.mp h1).le
    by_cases h2 : x ≤ 2
    · -- flow `0` is frozen at `2`; flow `1` catches up at rate `2`
      have hd1 : min (2 * x) (max 2 x) = 2 := by
        rw [max_eq_left h2]
        refine min_eq_right ?_
        calc (2 : ℝ≥0) = 2 * 1 := (mul_one 2).symm
          _ ≤ 2 * x := mul_le_mul_right h1x 2
      have hd2 : min (2 * (x - 1)) x = 2 * (x - 1) := by
        refine min_eq_left ?_
        rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub h1x]
        have hx2 : (x : ℝ) ≤ 2 := by exact_mod_cast h2
        push_cast
        linarith
      rw [hd1, hd2, ← NNReal.coe_inj]
      push_cast [NNReal.coe_sub h1x]
      ring
    · -- both flows are caught up and served at their rates
      have h2x : (2 : ℝ≥0) ≤ x := (not_le.mp h2).le
      have hd1 : min (2 * x) (max 2 x) = x := by
        rw [max_eq_right h2x]
        refine min_eq_right ?_
        calc x = 1 * x := (one_mul x).symm
          _ ≤ 2 * x := mul_le_mul_left one_le_two x
      have hd2 : min (2 * (x - 1)) x = x := by
        refine min_eq_right ?_
        rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub
          (le_trans one_le_two h2x)]
        have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h2x
        push_cast
        linarith
      rw [hd1, hd2, two_mul]

/-- The witness aggregate obeys the strict service inequality for
`λ₂ = rateLatency 2 0` — with equality, so no backlog premise is
needed. -/
theorem flipWitness_strict :
    ∀ s t, s ≤ t →
      IsBacklogged
        (fun x => ∑ j,
          ((![flipWitnessA, mpWitnessRate] : Fin 2 → Curve) j) x)
        (fun x => ∑ j,
          ((![flipWitnessDBurst, flipWitnessDRate] : Fin 2 → Curve) j) x)
        (Set.Ioc s t) →
      (∑ j, ((![flipWitnessDBurst, flipWitnessDRate] : Fin 2 → Curve) j) s)
          + (rateLatency 2 0) (t - s)
        ≤ ∑ j, ((![flipWitnessDBurst, flipWitnessDRate] : Fin 2 → Curve) j) t := by
  intro s t hst _
  have hsum : ∀ x : ℝ≥0,
      (∑ j, ((![flipWitnessDBurst, flipWitnessDRate] : Fin 2 → Curve) j) x)
        = 2 * x := fun x => by
    rw [Fin.sum_univ_two]
    show flipWitnessDBurst x + flipWitnessDRate x = 2 * x
    exact flipWitness_sum_eq x
  rw [hsum s, hsum t,
    show (rateLatency (2 : ℝ≥0) 0) (t - s) = 2 * (t - s) from by
      show (2 : ℝ≥0) * ((t - s) - 0) = 2 * (t - s)
      rw [tsub_zero],
    ← mul_add, add_tsub_cancel_of_le hst]

/-- The starved flow is backlogged throughout `(1, 2]`: its output is
frozen at `2` while its arrivals keep growing. -/
theorem flipWitness_backlogged :
    IsBacklogged ⇑flipWitnessA ⇑flipWitnessDBurst (Set.Ioc 1 2) := by
  intro u hu
  have hpos : (0 : ℝ≥0) < u := lt_trans one_pos hu.1
  show flipWitnessDBurst u < flipWitnessA u
  rw [flipWitnessDBurst_apply, flipWitnessA_apply, if_pos hpos,
    max_eq_left hu.2,
    min_eq_right (by
      calc (2 : ℝ≥0) = 2 * 1 := (mul_one 2).symm
        _ ≤ 2 * u := mul_le_mul_right hu.1.le 2)]
  calc (2 : ℝ≥0) = 1 + 1 := one_add_one_eq_two.symm
    _ < u + 1 := add_lt_add_left hu.1 1

/-- The violation: the residual `λ₁` promises the starved flow one unit
over `(1, 2]`, but its output is frozen at `2`. -/
theorem not_add_residualCurve_le_flipWitness :
    ¬ (flipWitnessDBurst 1 + residualCurve (rateLatency 2 0)
          (fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 0,
            (fun _ v => v) j v) (2 - 1)
        ≤ flipWitnessDBurst 2) := by
  intro h
  have hβmono : Monotone (rateLatency (2 : ℝ≥0) 0) :=
    fun a b hab => mul_le_mul_right (tsub_le_tsub_right hab 0) 2
  have hd11 : flipWitnessDBurst 1 = 2 := by
    rw [flipWitnessDBurst_apply, max_eq_left one_le_two, mul_one, min_self]
  have hd12 : flipWitnessDBurst 2 = 2 := by
    rw [flipWitnessDBurst_apply, max_self,
      min_eq_right (by
        calc (2 : ℝ≥0) = 2 * 1 := (mul_one 2).symm
          _ ≤ 2 * 2 := mul_le_mul_right one_le_two 2)]
  have hres : (1 : ℝ≥0) ≤ residualCurve (rateLatency 2 0)
      (fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 0,
        (fun _ v => v) j v) (2 - 1) := by
    rw [show (2 : ℝ≥0) - 1 = 1 from tsub_eq_of_eq_add (by norm_num)]
    refine le_trans ?_ (tsub_le_residualCurve
      (closureBddAbove_tsub_of_monotone hβmono) (le_refl 1))
    show (1 : ℝ≥0) ≤ (rateLatency (2 : ℝ≥0) 0) 1
      - (∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 0, (1 : ℝ≥0))
    rw [show ((Finset.univ : Finset (Fin 2)).erase 0) = {1} from by decide,
      Finset.sum_singleton,
      show (rateLatency (2 : ℝ≥0) 0) 1 = 2 from by
        show (2 : ℝ≥0) * (1 - 0) = 2
        rw [tsub_zero, mul_one],
      show (2 : ℝ≥0) - 1 = 1 from tsub_eq_of_eq_add (by norm_num)]
  rw [hd11, hd12] at h
  have h3 : (2 : ℝ≥0) + 1 ≤ 2 := le_trans (add_le_add le_rfl hres) h
  norm_num at h3

/-- **The blind-multiplexing residual cannot be upgraded to strict**:
the statement of blind multiplexing
(`minConv_residualCurve_le_of_strict_aggregate`, arrival-constrained
cross-traffic) with its min-plus conclusion replaced by the strict
service inequality for flow `i` is false. Contrast
`add_residualCurve_le_of_strict_aggregate`: the same conclusion *is* a
theorem when the cross-traffic *departures* are constrained. -/
theorem not_forall_add_residualCurve_le_of_strict_aggregate_of_arrival_bounds :
    ¬ ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (As Ds : ι → Curve) (β : ℝ≥0 → ℝ≥0) (α : ι → ℝ≥0 → ℝ≥0),
      (∀ j, Ds j ≤ As j) →
      (∀ s t, s ≤ t →
        IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
          (Set.Ioc s t) →
        (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t) →
      ∀ i, (∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j)) →
      ∀ s t, s ≤ t →
        IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t) →
        (Ds i) s + residualCurve β
            (fun v => ∑ j ∈ Finset.univ.erase i, α j v) (t - s)
          ≤ (Ds i) t := by
  intro h
  have hbad := h (Fin 2) ![flipWitnessA, mpWitnessRate]
    ![flipWitnessDBurst, flipWitnessDRate] (rateLatency 2 0) (fun _ v => v)
    flipWitness_causal flipWitness_strict 0
    (by
      intro j hj
      fin_cases j
      · exact absurd rfl hj
      · exact mpWitnessRate_arrivalBound)
    1 2 one_le_two flipWitness_backlogged
  exact not_add_residualCurve_le_flipWitness hbad

/-! ## Book restatement (residual service curves are not strict)
The two-flow figure: `β = λ₂` strict, `A₀(t) = t + 1`, `A₁(t) = t`,
priority flipped at `t = 1`. The residual `[λ₂ − λ₁]⁺↑` is a min-plus
service curve for flow `0` (blind multiplexing) — but not a strict
one: during `1 ≤ t ≤ 2` flow `0` has data backlogged and is not served
at all. -/
example :
    (∀ t, minConv (Deviation.liftENN ⇑flipWitnessA)
        (Deviation.liftENN
          (residualCurve (rateLatency 2 0) (fun v => v))) t
      ≤ ((flipWitnessDBurst t : ℝ≥0) : ℝ≥0∞))
    ∧ ¬ (flipWitnessDBurst 1
          + residualCurve (rateLatency 2 0) (fun v => v) (2 - 1)
        ≤ flipWitnessDBurst 2) := by
  constructor
  · intro t
    have h := minConv_residualCurve_le_of_strict_aggregate
      (As := ![flipWitnessA, mpWitnessRate])
      (Ds := ![flipWitnessDBurst, flipWitnessDRate])
      (β := rateLatency 2 0) (α := fun _ v => v) (i := 0)
      flipWitness_causal flipWitness_strict
      (by
        intro j hj
        fin_cases j
        · exact absurd rfl hj
        · exact mpWitnessRate_arrivalBound)
      t
    simpa using h
  · rw [show (fun v => v : ℝ≥0 → ℝ≥0)
        = (fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 0,
            (fun _ v => v) j v) from funext fun v => by
      rw [show ((Finset.univ : Finset (Fin 2)).erase 0) = {1} from by
          decide, Finset.sum_singleton]]
    exact not_add_residualCurve_le_flipWitness

/-! ## Not even weakly strict
The same flip witness refutes the weaker start-anchored upgrade: the
plain residual is not a *weakly strict* curve on the residual server
— the deconvolution in the weakly strict composition is necessary. -/

/-- The starved flow's own start at `t = 2` sits at `1`: past the
burst the only equality points of `(A₀, D₀)` are `0` and `1`. -/
theorem flipWitness_start_eq :
    start ⇑flipWitnessA ⇑flipWitnessDBurst 2 = 1 := by
  refine le_antisymm (csSup_le ⟨0, zero_le', ?_⟩ fun u hu => ?_) ?_
  · show flipWitnessA 0 = flipWitnessDBurst 0
    rw [flipWitnessA_apply, if_neg (lt_irrefl 0), flipWitnessDBurst_apply,
      mul_zero, min_eq_left zero_le']
  · by_contra h1u
    rw [not_le] at h1u
    exact absurd hu.2.symm
      (ne_of_lt (flipWitness_backlogged u ⟨h1u, hu.1⟩))
  · refine le_csSup ⟨2, fun x hx => hx.1⟩ ⟨one_le_two, ?_⟩
    show flipWitnessA 1 = flipWitnessDBurst 1
    rw [flipWitnessA_apply, if_pos one_pos, flipWitnessDBurst_apply,
      max_eq_left one_le_two, mul_one, min_self]
    exact one_add_one_eq_two

/-- The own-start violation: at `t = 2` the starved flow's start is
`1`, where the anchored residual bound is the strict-window
violation. -/
theorem not_add_residualCurve_start_le_flipWitness :
    ¬ (flipWitnessDBurst (start ⇑flipWitnessA ⇑flipWitnessDBurst 2)
        + residualCurve (rateLatency 2 0)
          (fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 0,
            (fun _ v => v) j v)
          (2 - start ⇑flipWitnessA ⇑flipWitnessDBurst 2)
      ≤ flipWitnessDBurst 2) := by
  rw [flipWitness_start_eq]
  exact not_add_residualCurve_le_flipWitness

/-- The burst-plus-rate arrivals are `(· + 1)`-upper constrained: the
worst increment is from the origin, a burst on top of the rate. -/
theorem flipWitnessA_arrivalBound :
    IsMaximalArrivalBound ⇑flipWitnessA (fun v => v + 1) := by
  rw [isMaximalArrivalBound_iff_increment]
  intro t d
  show flipWitnessA (t + d) ≤ flipWitnessA t + (d + 1)
  rw [flipWitnessA_apply, flipWitnessA_apply]
  rcases eq_or_ne t 0 with rfl | ht
  · rw [if_neg (lt_irrefl 0), zero_add, zero_add]
    split
    · exact le_rfl
    · exact zero_le'
  · rw [if_pos (pos_of_ne_zero ht),
      if_pos (lt_of_lt_of_le (pos_of_ne_zero ht) le_self_add)]
    calc t + d + 1 = (t + 1) + d := by ring
      _ ≤ (t + 1) + (d + 1) := add_le_add le_rfl le_self_add

/-- The flip witness's aggregate offers `λ₂` weakly strictly: the
strict window bound anchors at the aggregate start. -/
theorem flipWitness_wstrict_aggregate :
    IsWeaklyStrictMinimalServiceCurve (rateLatency 2 0)
      (aggregateServer (fun A D =>
        A = ![flipWitnessA, mpWitnessRate]
          ∧ D = ![flipWitnessDBurst, flipWitnessDRate])) := by
  rintro A D ⟨As, Ds, ⟨rfl, rfl⟩, rfl, rfl⟩ t
  have hws := flipWitness_strict
    (start
      (fun x => ∑ j,
        ((![flipWitnessA, mpWitnessRate] : Fin 2 → Curve) j) x)
      (fun x => ∑ j,
        ((![flipWitnessDBurst, flipWitnessDRate] : Fin 2 → Curve) j) x)
      t)
    t (start_le _ _ t)
    (isBacklogged_Ioc_start
      (fun x => Finset.sum_le_sum fun j _ => flipWitness_causal j x) t)
  rw [← Curve.coe_sum, ← Curve.coe_sum] at hws
  exact hws

/-- **The deconvolution is necessary**: the weakly strict composition
(`isWeaklyStrictMinimalServiceCurve_residualServer_of_wstrict`) with
the deconvolved residual replaced by the plain blind-multiplexing
residual `[β − ∑_{j≠i} αⱼ]⁺↑` is false — the book's two-flow figure:
the plain residual is min-plus but not weakly strict for the starved
flow. -/
theorem not_forall_isWeaklyStrictMinimalServiceCurve_residualCurve :
    ¬ ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (S : (ι → Curve) → (ι → Curve) → Prop) (β : ℝ≥0 → ℝ≥0)
      (α : ι → ℝ≥0 → ℝ≥0) (i : ι),
      IsCausalN S →
      IsWeaklyStrictMinimalServiceCurve β (aggregateServer S) →
      IsWeaklyStrictMinimalServiceCurve
        (residualCurve β (fun v => ∑ j ∈ Finset.univ.erase i, α j v))
        (residualServer (fun A D => S A D ∧
          ∀ j, IsMaximalArrivalBound ⇑(A j) (α j)) i) := by
  intro h
  have hbad := h (Fin 2)
    (fun A D =>
      A = ![flipWitnessA, mpWitnessRate]
        ∧ D = ![flipWitnessDBurst, flipWitnessDRate])
    (rateLatency 2 0) ![fun v => v + 1, fun v => v] 0
    (by rintro A D ⟨rfl, rfl⟩ j; exact flipWitness_causal j)
    flipWitness_wstrict_aggregate
    flipWitnessA flipWitnessDBurst
    ⟨![flipWitnessA, mpWitnessRate],
      ![flipWitnessDBurst, flipWitnessDRate],
      ⟨⟨rfl, rfl⟩, by
        intro j
        fin_cases j
        · exact flipWitnessA_arrivalBound
        · exact mpWitnessRate_arrivalBound⟩,
      rfl, rfl⟩ 2
  rw [show (fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 0,
      (![fun v => v + 1, fun v => v] : Fin 2 → ℝ≥0 → ℝ≥0) j v)
      = (fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 0,
        (fun (_ : Fin 2) (v : ℝ≥0) => v) j v) from funext fun v => by
    rw [show ((Finset.univ : Finset (Fin 2)).erase 0) = {1} from by
        decide, Finset.sum_singleton, Finset.sum_singleton]
    rfl] at hbad
  exact not_add_residualCurve_start_le_flipWitness hbad

end DeepWiki
