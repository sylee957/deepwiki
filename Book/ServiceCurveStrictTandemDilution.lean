import Book.ServiceCurveStrictEReal
import Book.ServiceCurveStrictTandem

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
