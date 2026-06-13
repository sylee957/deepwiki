import Book.ServiceCurveStrictEReal
import Book.ServiceCurveStrictTandem
import Book.Continuity

/-! # Lemma 9.5 reverse dilution: the catch-up time-warp
Building towards the reverse inclusion `S_mp(δ_T) ⊆ S̄(⋃ₙ (S_strict(δ_{T/n}))ⁿ)`.
The witness is a tandem of strict `δ_{T/n}` servers whose stages are time-warps of
the input: `Dᵢ = Dᵢ₋₁ ∘ hᵢ` for a continuous **catch-up warp** `h` (`h ≤ id`,
catching up to the identity within one period). This file defines the single warp
`warp d r` (period `d`, ramp width `r`) — flat-hold then a steep ramp that touches
the identity at each multiple of `d` — and its per-warp regularity. The staggered
composition and the delay bound `h₁∘…∘hₙ ≤ id − (T−ε)` build on it. -/

namespace DeepWiki

open Set
open scoped Classical NNReal

/-- The catch-up time-warp `warp d r`: on each period `(kd, (k+1)d]` it holds flat at
`kd` until `(k+1)d − r`, then ramps (slope `d/r`) up to touch the identity at
`(k+1)d`. Written `base + (d/r)·(φ − (d−r))₊` with `base = d⌊τ/d⌋`, `φ = τ − base`
(truncated subtraction makes the `(φ − (d−r))₊` vanish on the flat part). -/
noncomputable def warp (d r τ : ℝ≥0) : ℝ≥0 :=
  d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0) +
    d / r * ((τ - d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0)) - (d - r))

/-- `warp d r τ` unfolds to its base-plus-ramp form. -/
theorem warp_apply (d r τ : ℝ≥0) :
    warp d r τ = d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0) +
      d / r * ((τ - d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0)) - (d - r)) := rfl

/-- The base `d⌊τ/d⌋` never exceeds `τ`. -/
theorem warp_base_le (d τ : ℝ≥0) : d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0) ≤ τ := by
  rcases eq_zero_or_pos d with rfl | hd
  · simp
  · have hd' : (0 : ℝ) < (d : ℝ) := NNReal.coe_pos.mpr hd
    rw [← NNReal.coe_le_coe]
    push_cast
    calc (d : ℝ) * (⌊(τ : ℝ) / d⌋₊ : ℝ) ≤ d * ((τ : ℝ) / d) :=
          mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) d.coe_nonneg
      _ = τ := by field_simp

/-- `warp d r 0 = 0`. -/
theorem warp_zero_eq (d r : ℝ≥0) : warp d r 0 = 0 := by
  simp [warp]

/-- The fractional position `τ − d⌊τ/d⌋` stays below one period. -/
theorem warp_frac_lt {d : ℝ≥0} (hd : 0 < d) (τ : ℝ≥0) :
    ((τ - d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0) : ℝ≥0) : ℝ) < d := by
  have hd' : (0 : ℝ) < (d : ℝ) := NNReal.coe_pos.mpr hd
  rw [NNReal.coe_sub (warp_base_le d τ)]
  push_cast
  have h : (τ : ℝ) / d < (⌊(τ : ℝ) / d⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : (τ : ℝ) < ((⌊(τ : ℝ) / d⌋₊ : ℝ) + 1) * d := (div_lt_iff₀ hd').mp h
  have h3 : ((⌊(τ : ℝ) / d⌋₊ : ℝ) + 1) * d = (⌊(τ : ℝ) / d⌋₊ : ℝ) * d + d := by ring
  rw [mul_comm (d : ℝ)]
  linarith [h2, h3]

/-- The warp never exceeds the identity: `warp d r τ ≤ τ` (`0 < r ≤ d`). -/
theorem warp_le_self {d r : ℝ≥0} (hr : 0 < r) (hrd : r ≤ d) (τ : ℝ≥0) :
    warp d r τ ≤ τ := by
  have hd : 0 < d := lt_of_lt_of_le hr hrd
  have hbτ : d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0) ≤ τ := warp_base_le d τ
  set φ : ℝ≥0 := τ - d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0) with hφ
  have hbφ : d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0) + φ = τ := add_tsub_cancel_of_le hbτ
  have hφd : (φ : ℝ) < d := warp_frac_lt hd τ
  have key : d / r * (φ - (d - r)) ≤ φ := by
    rcases le_or_gt φ (d - r) with h | h
    · rw [tsub_eq_zero_of_le h, mul_zero]; exact zero_le'
    · rw [← NNReal.coe_le_coe]
      push_cast [NNReal.coe_sub h.le, NNReal.coe_sub hrd]
      have hr' : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
      rw [div_mul_eq_mul_div, div_le_iff₀ hr']
      nlinarith [hφd, NNReal.coe_le_coe.mpr hrd]
  calc warp d r τ = d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0) + d / r * (φ - (d - r)) := by
        rw [warp_apply]
    _ ≤ d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0) + φ := by gcongr
    _ = τ := hbφ

/-- The warp touches the identity at every multiple of the period:
`warp d r (d·k) = d·k` (the catch-up fixed points). -/
theorem warp_mul_nat {d r : ℝ≥0} (hd : 0 < d) (k : ℕ) : warp d r (d * (k : ℝ≥0)) = d * k := by
  have hd' : (0 : ℝ) < (d : ℝ) := NNReal.coe_pos.mpr hd
  have hfloor : ⌊((d * (k : ℝ≥0) : ℝ≥0) : ℝ) / d⌋₊ = k := by
    push_cast
    rw [mul_comm, mul_div_assoc, div_self hd'.ne', mul_one, Nat.floor_natCast]
  rw [warp_apply, hfloor, tsub_self, tsub_eq_zero_of_le zero_le', mul_zero, add_zero]

/-- **Catch-up density**: the warp has a fixed point in every window `(x, x + d]` —
namely the next multiple of the period, `d·(⌊x/d⌋ + 1)`. This is the hypothesis
`strictServiceRelEReal_delay_of_comp_catchUp` consumes to make each tandem stage a
strict `δ_d` server. -/
theorem warp_catchUp_dense {d r : ℝ≥0} (hd : 0 < d) (x : ℝ≥0) :
    ∃ p, x < p ∧ p ≤ x + d ∧ warp d r p = p := by
  have hd' : (0 : ℝ) < (d : ℝ) := NNReal.coe_pos.mpr hd
  refine ⟨d * ((⌊(x : ℝ) / d⌋₊ : ℝ≥0) + 1), ?_, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    push_cast
    have h : (x : ℝ) / d < (⌊(x : ℝ) / d⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [mul_comm]
    exact (div_lt_iff₀ hd').mp h
  · rw [← NNReal.coe_le_coe]
    push_cast
    have h : (⌊(x : ℝ) / d⌋₊ : ℝ) ≤ (x : ℝ) / d := Nat.floor_le (by positivity)
    have h2 : (d : ℝ) * (⌊(x : ℝ) / d⌋₊ : ℝ) ≤ x := by
      have hm := mul_le_mul_of_nonneg_left h hd'.le
      rwa [mul_comm (d : ℝ) ((x : ℝ) / d), div_mul_cancel₀ (x : ℝ) hd'.ne'] at hm
    have hexp : (d : ℝ) * ((⌊(x : ℝ) / d⌋₊ : ℝ) + 1) = d * (⌊(x : ℝ) / d⌋₊ : ℝ) + d := by
      ring
    linarith [h2, hexp]
  · rw [show d * ((⌊(x : ℝ) / d⌋₊ : ℝ≥0) + 1)
        = d * ((⌊(x : ℝ) / d⌋₊ + 1 : ℕ) : ℝ≥0) by push_cast; ring]
    exact warp_mul_nat hd _

/-- Within one period the warp stays at or below the next catch-up point:
`warp d r τ ≤ d⌊τ/d⌋ + d`. -/
theorem warp_le_period_top {d r : ℝ≥0} (hr : 0 < r) (hrd : r ≤ d) (τ : ℝ≥0) :
    warp d r τ ≤ d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0) + d := by
  have hd : 0 < d := lt_of_lt_of_le hr hrd
  rw [warp_apply]
  have hφd : (τ - d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0)) ≤ d :=
    (NNReal.coe_lt_coe.mp (warp_frac_lt hd τ)).le
  have hbound : (τ - d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0)) - (d - r) ≤ r := by
    rw [tsub_le_iff_right, add_tsub_cancel_of_le hrd]
    exact hφd
  have hstep : d / r * ((τ - d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0)) - (d - r)) ≤ d := by
    calc d / r * ((τ - d * (⌊(τ : ℝ) / d⌋₊ : ℝ≥0)) - (d - r))
        ≤ d / r * r := by gcongr
      _ = d := by rw [div_mul_cancel₀ _ hr.ne']
  gcongr

/-- The warp is monotone. -/
theorem warp_mono {d r : ℝ≥0} (hr : 0 < r) (hrd : r ≤ d) : Monotone (warp d r) := by
  have hd : 0 < d := lt_of_lt_of_le hr hrd
  have hd' : (0 : ℝ) < (d : ℝ) := NNReal.coe_pos.mpr hd
  intro a b hab
  have hfa : ⌊(a : ℝ) / d⌋₊ ≤ ⌊(b : ℝ) / d⌋₊ := Nat.floor_mono (by gcongr)
  rcases eq_or_lt_of_le hfa with heq | hlt
  · -- same period: only the ramp term moves, monotone in `τ`
    rw [warp_apply, warp_apply, heq]
    gcongr
  · -- `a` is in an earlier period than `b`: `warp a ≤ top_a ≤ base_b ≤ warp b`
    have hbase_b : d * (⌊(b : ℝ) / d⌋₊ : ℝ≥0) ≤ warp d r b := by
      rw [warp_apply]; exact le_self_add
    have htop_a : warp d r a ≤ d * (⌊(a : ℝ) / d⌋₊ : ℝ≥0) + d := warp_le_period_top hr hrd a
    have hsucc : (⌊(a : ℝ) / d⌋₊ : ℝ≥0) + 1 ≤ (⌊(b : ℝ) / d⌋₊ : ℝ≥0) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hchain : d * (⌊(a : ℝ) / d⌋₊ : ℝ≥0) + d ≤ d * (⌊(b : ℝ) / d⌋₊ : ℝ≥0) :=
      calc d * (⌊(a : ℝ) / d⌋₊ : ℝ≥0) + d
          = d * ((⌊(a : ℝ) / d⌋₊ : ℝ≥0) + 1) := by ring
        _ ≤ d * (⌊(b : ℝ) / d⌋₊ : ℝ≥0) := by gcongr
    exact htop_a.trans (hchain.trans hbase_b)

/-- The period-`j` formula `f_j(τ) = dj + (d/r)(τ − dj − (d−r))` that the warp
follows on `[dj, d(j+1)]`. -/
noncomputable def warpPeriod (d r : ℝ≥0) (j : ℕ) (τ : ℝ≥0) : ℝ≥0 :=
  d * (j : ℝ≥0) + d / r * (τ - d * (j : ℝ≥0) - (d - r))

/-- `warpPeriod d r j` is continuous (truncated subtractions of continuous maps). -/
theorem warpPeriod_continuous (d r : ℝ≥0) (j : ℕ) : Continuous (warpPeriod d r j) := by
  unfold warpPeriod
  exact continuous_const.add
    (((continuous_sub_right _).comp (continuous_sub_right _)).const_mul _)

/-- On its period the warp equals the period formula: if `⌊τ/d⌋ = j` then
`warp d r τ = warpPeriod d r j τ`. -/
theorem warp_eq_warpPeriod {d r : ℝ≥0} {τ : ℝ≥0} {j : ℕ}
    (h : ⌊(τ : ℝ) / d⌋₊ = j) : warp d r τ = warpPeriod d r j τ := by
  rw [warp_apply, warpPeriod, h]

/-- If `dj ≤ τ < d(j+1)` (as reals) then `⌊τ/d⌋ = j`. -/
theorem warp_floor_eq {d : ℝ≥0} (hd : 0 < d) {τ : ℝ≥0} {j : ℕ}
    (h1 : (d : ℝ) * j ≤ τ) (h2 : (τ : ℝ) < d * (j + 1)) : ⌊(τ : ℝ) / d⌋₊ = j := by
  have hd' : (0 : ℝ) < (d : ℝ) := NNReal.coe_pos.mpr hd
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hd', mul_comm]; exact h1
  · rw [div_lt_iff₀ hd', mul_comm]; exact h2

/-- The ramp reaches the next catch-up: `warpPeriod d r j (d·(j+1)) = d·(j+1)`. -/
theorem warpPeriod_top {d r : ℝ≥0} (hr : 0 < r) (hrd : r ≤ d) (j : ℕ) :
    warpPeriod d r j (d * ((j + 1 : ℕ) : ℝ≥0)) = d * ((j + 1 : ℕ) : ℝ≥0) := by
  rw [warpPeriod]
  push_cast
  rw [show d * ((j : ℝ≥0) + 1) - d * (j : ℝ≥0) = d by
      rw [mul_add, mul_one, add_tsub_cancel_left],
    tsub_tsub_cancel_of_le hrd, div_mul_cancel₀ _ hr.ne']
  ring

/-- The warp is left-continuous: on every left-neighborhood it coincides with a
continuous period formula. -/
theorem warp_leftCont {d r : ℝ≥0} (hr : 0 < r) (hrd : r ≤ d) :
    IsLeftContinuous (warp d r) := by
  have hd : 0 < d := lt_of_lt_of_le hr hrd
  have hd' : (0 : ℝ) < (d : ℝ) := NNReal.coe_pos.mpr hd
  intro u
  rcases eq_or_ne u 0 with rfl | hune
  · exact isLeftContinuousAt_zero _
  have hupos : (0 : ℝ) < (u : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hune)
  set k : ℕ := ⌊(u : ℝ) / d⌋₊ with hk
  have hkle : (d : ℝ) * k ≤ u := by
    have h := Nat.floor_le (le_of_lt (div_pos hupos hd'))
    rw [← hk, le_div_iff₀ hd', mul_comm] at h; linarith
  have hklt : (u : ℝ) < d * (k + 1) := by
    have h := Nat.lt_floor_add_one ((u : ℝ) / d)
    rw [← hk, div_lt_iff₀ hd'] at h; nlinarith [h]
  -- pick the period `j` just left of `u`: `j = k` if `u` is interior, else `k-1`
  obtain ⟨j, hlo, hub, hval⟩ : ∃ j : ℕ, (d : ℝ) * j < u ∧ (u : ℝ) ≤ d * (j + 1) ∧
      warp d r u = warpPeriod d r j u := by
    rcases eq_or_lt_of_le hkle with heq | hlt
    · -- `u = d·k`, a multiple (so `k ≥ 1`); the period just left is `k-1`
      obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · rw [hk0, Nat.cast_zero, mul_zero] at heq; exact absurd heq.symm (ne_of_gt hupos)
        · exact ⟨k - 1, (Nat.succ_pred_eq_of_pos hk0).symm⟩
      have huval : u = d * ((k' + 1 : ℕ) : ℝ≥0) := by
        rw [← NNReal.coe_inj]; push_cast; rw [hk'] at heq; push_cast at heq; linarith
      refine ⟨k', ?_, ?_, ?_⟩
      · rw [hk'] at heq; push_cast at heq ⊢; nlinarith [heq, hd']
      · rw [hk'] at heq; push_cast at heq ⊢; linarith
      · rw [huval, warp_mul_nat hd, warpPeriod_top hr hrd]
    · exact ⟨k, hlt, hklt.le, warp_eq_warpPeriod hk.symm⟩
  -- on `(d·j, u)` the warp follows the period formula
  have hlo' : d * (j : ℝ≥0) < u := by
    rw [← NNReal.coe_lt_coe]; push_cast; exact hlo
  have hev : warp d r =ᶠ[nhdsWithin u (Set.Iio u)] warpPeriod d r j := by
    filter_upwards [Ioo_mem_nhdsLT hlo'] with τ hτ
    refine warp_eq_warpPeriod (warp_floor_eq hd ?_ ?_)
    · have h := hτ.1; rw [← NNReal.coe_lt_coe] at h; push_cast at h; linarith
    · have h := hτ.2; rw [← NNReal.coe_lt_coe] at h; linarith [hub]
  exact (warpPeriod_continuous d r j).continuousWithinAt.congr_of_eventuallyEq hev hval

/-- The warp is continuous: left-continuous, and right-continuous because it follows
the continuous period formula `warpPeriod d r k` on each `[kd, (k+1)d)`. -/
theorem warp_continuous {d r : ℝ≥0} (hr : 0 < r) (hrd : r ≤ d) : Continuous (warp d r) := by
  have hd : 0 < d := lt_of_lt_of_le hr hrd
  have hd' : (0 : ℝ) < (d : ℝ) := NNReal.coe_pos.mpr hd
  rw [continuous_iff_continuousAt]
  intro u
  rw [← continuousWithinAt_univ, ← Set.Iic_union_Ici (a := u), continuousWithinAt_union]
  set k : ℕ := ⌊(u : ℝ) / d⌋₊ with hk
  have hval : warp d r u = warpPeriod d r k u := warp_eq_warpPeriod hk.symm
  have huk : (d : ℝ) * k ≤ u := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ (u : ℝ) / d by positivity)
    rw [← hk, le_div_iff₀ hd', mul_comm] at h; linarith
  refine ⟨?_, ?_⟩
  · rw [show Set.Iic u = Set.Iio u ∪ {u} from by
        ext x; simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
        exact le_iff_lt_or_eq,
      continuousWithinAt_union]
    exact ⟨warp_leftCont hr hrd u, continuousWithinAt_singleton⟩
  · have hu_lt : (u : ℝ) < d * (k + 1) := by
      have h := Nat.lt_floor_add_one ((u : ℝ) / d)
      rw [← hk, div_lt_iff₀ hd'] at h; nlinarith [h]
    have hu_lt' : u < d * ((k : ℝ≥0) + 1) := by
      rw [← NNReal.coe_lt_coe]; push_cast; exact hu_lt
    have hev : warp d r =ᶠ[nhdsWithin u (Set.Ici u)] warpPeriod d r k := by
      filter_upwards [Ico_mem_nhdsGE hu_lt'] with τ hτ
      refine warp_eq_warpPeriod (warp_floor_eq hd ?_ ?_)
      · have h := hτ.1; rw [← NNReal.coe_le_coe] at h; linarith
      · have h := hτ.2; rw [← NNReal.coe_lt_coe] at h; push_cast at h; linarith
    exact (warpPeriod_continuous d r k).continuousWithinAt.congr_of_eventuallyEq hev hval

/-- **Piecewise continuity is preserved by precomposition with a continuous monotone
map.** If `A` is piecewise continuous and `g` is continuous and monotone, then `A ∘ g`
is piecewise continuous: on each level set `{g = a}` (an interval, by monotonicity)
`A ∘ g` is constant, so its discontinuities sit only at the `≤ 2` endpoints, and `A`
has finitely many discontinuity values on `[0, g T]`. -/
theorem IsPiecewiseContinuous.comp_continuous_monotone {A : ℝ≥0 → ℝ≥0}
    (hA : IsPiecewiseContinuous A) {g : ℝ≥0 → ℝ≥0} (hgc : Continuous g) (hgm : Monotone g) :
    IsPiecewiseContinuous (fun τ => A (g τ)) := by
  intro T
  set S : ℝ≥0 → Set ℝ≥0 := fun a => {σ | σ ∈ Set.Icc 0 T ∧ g σ = a} with hSdef
  have hbddB : ∀ a, BddBelow (S a) := fun a => ⟨0, fun σ hσ => hσ.1.1⟩
  have hbddA : ∀ a, BddAbove (S a) := fun a => ⟨T, fun σ hσ => hσ.1.2⟩
  refine Set.Finite.subset ((hA (g T)).biUnion (fun a _ =>
    (Set.finite_singleton (sInf (S a))).union (Set.finite_singleton (sSup (S a))))) ?_
  rintro τ hτ
  have hτdisc : ¬ ContinuousAt (fun τ => A (g τ)) τ := hτ.1
  have hτT : τ ∈ Set.Icc 0 T := hτ.2
  have hgτD : g τ ∈ discontSet A ∩ Set.Icc 0 (g T) :=
    ⟨fun hcon => hτdisc (hcon.comp hgc.continuousAt), ⟨zero_le', hgm hτT.2⟩⟩
  have hτS : τ ∈ S (g τ) := ⟨hτT, rfl⟩
  refine Set.mem_biUnion hgτD ?_
  by_contra hcon
  rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_singleton_iff] at hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  obtain ⟨σ1, hσ1S, hσ1τ⟩ := exists_lt_of_csInf_lt ⟨τ, hτS⟩
    (lt_of_le_of_ne (csInf_le (hbddB _) hτS) (Ne.symm hne1))
  obtain ⟨σ2, hσ2S, hτσ2⟩ := exists_lt_of_lt_csSup ⟨τ, hτS⟩
    (lt_of_le_of_ne (le_csSup (hbddA _) hτS) hne2)
  refine hτdisc ((continuousAt_const : ContinuousAt (fun _ : ℝ≥0 => A (g τ)) τ).congr ?_)
  filter_upwards [Ioo_mem_nhds hσ1τ hτσ2] with σ' hσ'
  show A (g τ) = A (g σ')
  have hgeq : g σ' = g τ := by
    have h1 : g σ1 ≤ g σ' := hgm (le_of_lt hσ'.1)
    have h2 : g σ' ≤ g σ2 := hgm (le_of_lt hσ'.2)
    rw [hσ1S.2] at h1
    rw [hσ2S.2] at h2
    exact le_antisymm h2 h1
  rw [hgeq]

/-- Left-continuity is preserved by precomposition with a continuous monotone map. -/
theorem IsLeftContinuous.comp_continuous_monotone {A : ℝ≥0 → ℝ≥0} (hA : IsLeftContinuous A)
    {g : ℝ≥0 → ℝ≥0} (hgc : Continuous g) (hgm : Monotone g) :
    IsLeftContinuous (fun τ => A (g τ)) := by
  intro t
  have hA' : ContinuousWithinAt A (Set.Iic (g t)) (g t) := by
    rw [show Set.Iic (g t) = Set.Iio (g t) ∪ {g t} from by
        ext x; simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
        exact le_iff_lt_or_eq,
      continuousWithinAt_union]
    exact ⟨hA (g t), continuousWithinAt_singleton⟩
  exact hA'.comp (hgc.continuousAt.continuousWithinAt) (fun s hs => hgm (le_of_lt hs))

/-- The first tandem stage `A ∘ warp d r` as a `Curve`: the warp turns the smooth
arrival `A` into a staircase (flats of length `d − r`, ramps of width `r`), which is a
strict `δ_d` server of `A`. -/
noncomputable def warpCurve (A : Curve) {d r : ℝ≥0} (hr : 0 < r) (hrd : r ≤ d) : Curve :=
  ⟨fun τ => A (warp d r τ), A.mono.comp (warp_mono hr hrd),
    by show A (warp d r 0) = 0; rw [warp_zero_eq]; exact A.zero,
    A.pwc.comp_continuous_monotone (warp_continuous hr hrd) (warp_mono hr hrd),
    A.leftCont.comp_continuous_monotone (warp_continuous hr hrd) (warp_mono hr hrd)⟩

/-- `warpCurve A hr hrd τ = A (warp d r τ)`. -/
@[simp] theorem warpCurve_apply (A : Curve) {d r : ℝ≥0} (hr : 0 < r) (hrd : r ≤ d) (τ : ℝ≥0) :
    warpCurve A hr hrd τ = A (warp d r τ) := rfl

/-- **The first stage is a strict `δ_d` server**:
`(A, A ∘ warp d r) ∈ S_strict(δ_d)`, via the catch-up warp (`warp ≤ id`, catch-up
dense) and the per-stage criterion. -/
theorem warpCurve_strictServiceRelEReal (A : Curve) {d r : ℝ≥0} (hr : 0 < r) (hrd : r ≤ d) :
    strictServiceRelEReal (delayEReal d) A (warpCurve A hr hrd) :=
  strictServiceRelEReal_delay_of_comp_catchUp (fun τ => (warpCurve_apply A hr hrd τ))
    (warp_le_self hr hrd) (warp_catchUp_dense (lt_of_lt_of_le hr hrd))
