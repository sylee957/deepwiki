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
