import Book.ServersConcatenation
import Book.ServiceCurvePackets

/-! # The concatenation inclusion is strict
The convolution does not exactly model the composition:
`Smp(λ₁) ∘ Smp(δ₃) ⊊ Smp(δ₃ ∗ λ₁)`. Witnesses: the arrival with burst
`2` and rate `1/2`, and the departure holding at `2` on `(0, 4]` before
rejoining the arrival. The pair is served by `δ₃ ∗ λ₁`, but any
intermediate `B` dominates both the departure and `A ∗ δ₃`, forcing
`(B ∗ λ₁) 4 ≥ 5/2 > 2 = C 4`. -/

namespace DeepWiki

open scoped Classical NNReal

/-- Nonnegativity of the `EReal` rate curve: `0 ≤ rateEReal C t`. -/
theorem isNonneg_rateEReal (C : ℝ≥0) : IsNonneg (rateEReal C) := fun t => by
  rw [rateEReal_apply]
  exact_mod_cast (C * t).coe_nonneg

/-- Halving is monotone on `ℝ≥0`. -/
theorem monotone_half : Monotone (fun t : ℝ≥0 => t / 2) := fun a b h => by
  show a / 2 ≤ b / 2
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_left h _

/-- The arrival witness: burst `2`, then rate `1/2` (a `γ_{2,1/2}`
token-bucket shape). -/
noncomputable def witnessArrival : Curve :=
  afterCurve 0 (fun t => 2 + t / 2)
    (fun _ _ h => add_le_add le_rfl (monotone_half h))
    (continuous_const.add (continuous_id.div_const 2))

/-- The departure witness: `2` on `(0, 4]`, rejoining the arrival past
`4`. -/
noncomputable def witnessDeparture : Curve :=
  stepCurve 0 2 + afterCurve 4 (fun t => t / 2)
    monotone_half
    (continuous_id.div_const 2)

/-- `witnessArrival t = 2 + t / 2` for `0 < t`, `0` at the origin. -/
theorem witnessArrival_apply (t : ℝ≥0) :
    witnessArrival t = if 0 < t then 2 + t / 2 else 0 := rfl

/-- `witnessDeparture` as the sum of the burst step and the post-`4`
ramp. -/
theorem witnessDeparture_apply (t : ℝ≥0) :
    witnessDeparture t
      = (if 0 < t then 2 else 0) + (if 4 < t then t / 2 else 0) := rfl

/-- `witnessArrival t = 2 + t / 2` past the origin. -/
theorem witnessArrival_pos {t : ℝ≥0} (ht : 0 < t) :
    witnessArrival t = 2 + t / 2 := by
  rw [witnessArrival_apply, if_pos ht]

/-- `witnessDeparture t = 2` on `(0, 4]`. -/
theorem witnessDeparture_mid {t : ℝ≥0} (ht : 0 < t) (ht4 : t ≤ 4) :
    witnessDeparture t = 2 := by
  rw [witnessDeparture_apply, if_pos ht, if_neg (not_lt.mpr ht4), add_zero]

/-- `witnessDeparture t = 2 + t / 2` past `4`. -/
theorem witnessDeparture_late {t : ℝ≥0} (ht : 4 < t) :
    witnessDeparture t = 2 + t / 2 := by
  rw [witnessDeparture_apply, if_pos (lt_trans (by norm_num) ht),
    if_pos ht]

/-- The witness pair is served by the convolved curve:
`A ≥ C ≥ A ∗ δ₃ ∗ λ₁`, so `(A, C) ∈ Smp(δ₃ ∗ λ₁)`. -/
theorem witness_mem_minimalServiceRel :
    minimalServiceRel (minConv (delayEReal 3) (rateEReal 1))
      witnessArrival witnessDeparture := by
  rw [mem_minimalServiceRel_iff]
  constructor
  · -- `C ≤ A`
    intro t
    rcases eq_zero_or_pos t with rfl | ht
    · simp [witnessDeparture_apply, witnessArrival_apply]
    · rw [witnessDeparture_apply, witnessArrival_pos ht, if_pos ht]
      rcases le_or_gt t 4 with h4 | h4
      · rw [if_neg (not_lt.mpr h4), add_zero]
        exact le_self_add
      · rw [if_pos h4]
  · -- `A ∗ (δ₃ ∗ λ₁) ≤ C`
    intro t
    rcases le_or_gt t 4 with h4 | h4
    · -- split `(0, t)`; the inner convolution is at most `min 2 (t - 3)₊`
      refine le_trans (minConv_le_add _ _ (zero_add t)) ?_
      rw [curveEReal_zero, zero_add]
      rcases le_or_gt t 3 with h3 | h3
      · -- inner split `(t, 0)`: both factors vanish
        refine le_trans (minConv_le_add _ _ (add_zero t)) ?_
        rw [show delayEReal 3 t = 0 from delay_eq_zero 3 h3,
          rateEReal_zero_eq 1, add_zero]
        exact curveEReal_nonneg _ t
      · -- inner split `(3, t - 3)`: worth at most `1 ≤ 2 = C t`
        refine le_trans
          (minConv_le_add _ _ (add_tsub_cancel_of_le h3.le)) ?_
        rw [show delayEReal 3 3 = 0 from delay_eq_zero 3 le_rfl, zero_add]
        simp only [curveEReal_apply, rateEReal_apply]
        rw [witnessDeparture_mid (lt_trans (by norm_num) h3) h4]
        have h2 : (1 * (t - 3) : ℝ≥0) ≤ 2 := by
          rw [one_mul]
          exact tsub_le_iff_right.mpr (le_trans h4 (by norm_num))
        exact_mod_cast h2
    · -- split `(t, 0)`: the curves agree past `4`
      refine le_trans (minConv_le_add _ _ (add_zero t)) ?_
      have hinner : minConv (delayEReal 3) (rateEReal 1) 0 ≤ 0 := by
        refine le_trans (minConv_le_add _ _ (add_zero 0)) ?_
        rw [show delayEReal 3 0 = 0 from delay_eq_zero 3 zero_le',
          rateEReal_zero_eq 1, add_zero]
      refine le_trans (add_le_add le_rfl hinner) ?_
      rw [add_zero]
      simp only [curveEReal_apply]
      rw [witnessArrival_pos (lt_trans (by norm_num) h4),
        witnessDeparture_late h4]

/-- No intermediate curve `B` serves the witness pair through `δ₃` then
`λ₁`: any such `B` dominates both the departure and `A ∗ δ₃`, so
`(B ∗ λ₁) 4 ≥ 5/2 > 2 = C 4`. -/
theorem witness_not_mem_comp :
    ¬ Relation.Comp (minimalServiceRel (delayEReal 3))
        (minimalServiceRel (rateEReal 1))
      witnessArrival witnessDeparture := by
  rintro ⟨B, hAB, hBC⟩
  rw [mem_minimalServiceRel_iff] at hAB hBC
  have hbound := hBC.2 4
  have hC4 : curveEReal witnessDeparture 4 = (((2 : ℝ≥0) : ℝ) : EReal) := by
    rw [curveEReal_apply, witnessDeparture_mid (by norm_num) le_rfl]
  rw [hC4] at hbound
  have hlow : (((5 / 2 : ℝ≥0) : ℝ) : EReal)
      ≤ minConv (curveEReal B) (rateEReal 1) 4 := by
    refine le_minConv fun u s hus => ?_
    simp only [curveEReal_apply, rateEReal_apply]
    have key : (5 / 2 : ℝ≥0) ≤ B u + 1 * s := by
      rw [one_mul]
      rcases le_or_gt u 3 with hu3 | hu3
      · rcases eq_zero_or_pos u with rfl | hu0
        · -- `u = 0`: the rate term alone is `4`
          rw [zero_add] at hus
          have h52 : (5 / 2 : ℝ≥0) ≤ 4 := by
            exact_mod_cast (by norm_num : (5 / 2 : ℝ) ≤ 4)
          calc (5 / 2 : ℝ≥0) ≤ 4 := h52
            _ ≤ B 0 + 4 := le_add_self
            _ = B 0 + s := by rw [hus]
        · -- `0 < u ≤ 3`: `B u ≥ C u = 2` and `s ≥ 1`
          have hBu : (2 : ℝ≥0) ≤ B u := by
            have h := hBC.1 u
            rwa [witnessDeparture_mid hu0
              (le_trans hu3 (by norm_num))] at h
          have hs1 : (1 : ℝ≥0) ≤ s := by
            by_contra hcon
            rw [not_le] at hcon
            have hlt : u + s < 3 + 1 := add_lt_add_of_le_of_lt hu3 hcon
            rw [hus] at hlt
            norm_num at hlt
          have h52 : (5 / 2 : ℝ≥0) ≤ 2 + 1 := by
            exact_mod_cast (by norm_num : (5 / 2 : ℝ) ≤ 2 + 1)
          calc (5 / 2 : ℝ≥0) ≤ 2 + 1 := h52
            _ ≤ B u + s := add_le_add hBu hs1
      · -- `3 < u`: `B u ≥ (A ∗ δ₃) u = 2 + (u - 3) / 2`
        obtain ⟨x, rfl⟩ := le_iff_exists_add.mp hu3.le
        have hx0 : 0 < x := by
          rcases eq_zero_or_pos x with rfl | hx
          · rw [add_zero] at hu3
            exact absurd hu3 (lt_irrefl _)
          · exact hx
        have hxs : x + s = 1 := by
          have h31 : (3 : ℝ≥0) + (x + s) = 3 + 1 := by
            rw [← add_assoc, hus]
            norm_num
          exact add_left_cancel h31
        have hAx : ((witnessArrival x : ℝ) : EReal) ≤ curveEReal B (3 + x) := by
          refine le_trans ?_ (hAB.2 (3 + x))
          refine le_minConv fun a b hab => ?_
          rcases le_or_gt b 3 with hb3 | hb3
          · rw [show delayEReal 3 b = 0 from delay_eq_zero 3 hb3,
              add_zero]
            have hxa : x ≤ a := by
              have hadd : x + b ≤ a + b := by
                rw [hab, add_comm 3 x]
                exact add_le_add le_rfl hb3
              exact le_of_add_le_add_right hadd
            simp only [curveEReal_apply]
            exact_mod_cast witnessArrival.mono hxa
          · rw [show delayEReal 3 b = ⊤ from delay_eq_top 3 hb3,
              show curveEReal witnessArrival a + (⊤ : EReal) = ⊤ from
                EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
            exact le_top
        have hBu : (2 + x / 2 : ℝ≥0) ≤ B (3 + x) := by
          rw [witnessArrival_pos hx0, curveEReal_apply] at hAx
          exact_mod_cast hAx
        have hhalf : (1 / 2 : ℝ≥0) ≤ x / 2 + s :=
          calc (1 / 2 : ℝ≥0) = (x + s) / 2 := by rw [hxs]
            _ = x / 2 + s / 2 := add_div x s 2
            _ ≤ x / 2 + s := add_le_add le_rfl (NNReal.half_le_self s)
        have h52 : (5 / 2 : ℝ≥0) = 2 + 1 / 2 := by
          apply NNReal.coe_injective
          push_cast
          norm_num
        calc (5 / 2 : ℝ≥0) = 2 + 1 / 2 := h52
          _ ≤ 2 + (x / 2 + s) := add_le_add le_rfl hhalf
          _ = (2 + x / 2) + s := (add_assoc _ _ _).symm
          _ ≤ B (3 + x) + s := add_le_add hBu le_rfl
    exact_mod_cast key
  have hcontra : (5 / 2 : ℝ) ≤ 2 := by
    exact_mod_cast le_trans hlow hbound
  norm_num at hcontra

/-- **The reverse containment fails**:
`Smp(δ₃ ∗ λ₁) ⊄ Smp(λ₁) ∘ Smp(δ₃)` — the witness pair satisfies the
end-to-end convolution bound but factors through no intermediate curve. -/
theorem not_minimalServiceRel_le_comp_delay_rate :
    ¬ minimalServiceRel (minConv (delayEReal 3) (rateEReal 1))
      ≤ Relation.Comp (minimalServiceRel (delayEReal 3))
          (minimalServiceRel (rateEReal 1)) :=
  fun hle => witness_not_mem_comp (hle _ _ witness_mem_minimalServiceRel)

/-- **The concatenation inclusion is strict**:
`Smp(λ₁) ∘ Smp(δ₃) ⊊ Smp(δ₃ ∗ λ₁)`. The convolution is commutative, the
composition is not — the convolution does not exactly model the
composition. -/
theorem comp_minimalServiceRel_lt_delay_rate :
    Relation.Comp (minimalServiceRel (delayEReal 3))
        (minimalServiceRel (rateEReal 1))
      < minimalServiceRel (minConv (delayEReal 3) (rateEReal 1)) :=
  lt_of_le_not_ge
    (comp_minimalServiceRel_le
      (isNonneg_delayEReal 3).isBddBelowReal
      (isNonneg_rateEReal 1).isBddBelowReal)
    not_minimalServiceRel_le_comp_delay_rate

/-! ## Book restatement (the inclusion may be strict)
Let `β₁ = δ₃`, `β₂ = λ₁`, `A = γ_{2,1/2}`, and
`C : 0 ↦ 0; t ∈ (0, 4] ↦ 2; t > 4 ↦ A t`. Then `A ≥ C ≥ A ∗ β₁ ∗ β₂`,
but there does not exist `B ∈ 𝒞` such that `(A, B) ∈ Smp(β₁)` and
`(B, C) ∈ Smp(β₂)`: any admissible `B` dominates `max(C, A ∗ β₁)`, and
`(B ∗ β₂) 4 ≥ 5/2 > 2 = C 4`. Hence `Smp(β₂) ∘ Smp(β₁) ⊊ Smp(β₁ ∗ β₂)`. -/
example :
    minimalServiceRel (minConv (delayEReal 3) (rateEReal 1))
        witnessArrival witnessDeparture
      ∧ ¬ ∃ B : Curve,
          minimalServiceRel (delayEReal 3) witnessArrival B
            ∧ minimalServiceRel (rateEReal 1) B witnessDeparture :=
  ⟨witness_mem_minimalServiceRel,
    fun ⟨B, h₁, h₂⟩ => witness_not_mem_comp ⟨B, h₁, h₂⟩⟩

example :
    Relation.Comp (minimalServiceRel (delayEReal 3))
        (minimalServiceRel (rateEReal 1))
      < minimalServiceRel (minConv (delayEReal 3) (rateEReal 1)) :=
  comp_minimalServiceRel_lt_delay_rate

/-! The strictness decomposes into its two directions: the concatenation
containment `Smp(β₂) ∘ Smp(β₁) ⊆ Smp(β₁ ∗ β₂)` holds, while the reverse
containment `Smp(β₁ ∗ β₂) ⊆ Smp(β₂) ∘ Smp(β₁)` fails — a pair satisfying
the end-to-end bound need not factor through any intermediate curve. -/
example :
    (Relation.Comp (minimalServiceRel (delayEReal 3))
        (minimalServiceRel (rateEReal 1))
      ≤ minimalServiceRel (minConv (delayEReal 3) (rateEReal 1)))
    ∧ ¬ (minimalServiceRel (minConv (delayEReal 3) (rateEReal 1))
      ≤ Relation.Comp (minimalServiceRel (delayEReal 3))
          (minimalServiceRel (rateEReal 1))) :=
  ⟨comp_minimalServiceRel_le
      (isNonneg_delayEReal 3).isBddBelowReal
      (isNonneg_rateEReal 1).isBddBelowReal,
    not_minimalServiceRel_le_comp_delay_rate⟩

end DeepWiki
