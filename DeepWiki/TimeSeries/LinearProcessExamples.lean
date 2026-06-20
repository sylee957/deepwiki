import DeepWiki.TimeSeries.LinearProcess
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Example 3.2.2: the `AR(1)` process as an `MA(∞)` linear process
The causal `AR(1)` process `Xₜ = φ Xₜ₋₁ + Zₜ` with `|φ| < 1` is the moving average of infinite
order with weights `ψⱼ = φʲ` (`j ≥ 0`): `Xₜ = ∑_{j≥0} φʲ Zₜ₋ⱼ`. Its filter is absolutely summable
(a geometric series), so the `L²` linear process `linearProcessLp` is well-defined and `MA(∞)`
(Definition 3.2.1). -/

namespace DeepWiki.TimeSeries

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The `MA(∞)` weight sequence of a causal `AR(1)` process: `ψⱼ = φʲ` for `j ≥ 0`, else `0`
(Example 3.2.2) — a one-sided (causal) filter on `ℤ`. -/
noncomputable def ar1Filter (φ : ℝ) : ℤ → ℝ := fun j => if 0 ≤ j then φ ^ j.toNat else 0

/-- `ar1Filter φ` at a nonnegative integer `↑n` is `φⁿ`. -/
@[simp] theorem ar1Filter_natCast (φ : ℝ) (n : ℕ) : ar1Filter φ (n : ℤ) = φ ^ n := by
  simp [ar1Filter]

/-- `ar1Filter φ` vanishes at negative indices (the filter is causal). -/
theorem ar1Filter_neg (φ : ℝ) {j : ℤ} (hj : j < 0) : ar1Filter φ j = 0 := by
  simp only [ar1Filter]; exact if_neg (not_le.mpr hj)

/-- **Example 3.2.2:** the `AR(1)` filter `ψⱼ = φʲ` is absolutely summable when `|φ| < 1` — the
defining `∑ⱼ |ψⱼ| < ∞` of an `MA(∞)` process (Definition 3.2.1), via the geometric series. -/
theorem summable_ar1Filter {φ : ℝ} (hφ : |φ| < 1) : Summable (ar1Filter φ) := by
  have hf : ∀ x ∉ Set.range (Nat.cast : ℕ → ℤ), ar1Filter φ x = 0 := by
    intro x hx
    refine ar1Filter_neg φ ?_
    rcases lt_or_ge x 0 with h | h
    · exact h
    · exact absurd ⟨x.toNat, Int.toNat_of_nonneg h⟩ hx
  rw [← Function.Injective.summable_iff Nat.cast_injective hf]
  have hcomp : (ar1Filter φ ∘ (Nat.cast : ℕ → ℤ)) = fun n => φ ^ n := by
    funext n; exact ar1Filter_natCast φ n
  rw [hcomp]
  exact summable_geometric_iff_norm_lt_one.mpr (by rwa [Real.norm_eq_abs])

/-- The `AR(1)` weights sum to `(1 − φ)⁻¹` — the geometric series `∑_{j≥0} φʲ`. -/
theorem tsum_ar1Filter {φ : ℝ} (hφ : |φ| < 1) : ∑' j, ar1Filter φ j = (1 - φ)⁻¹ := by
  have hf : Function.support (ar1Filter φ) ⊆ Set.range (Nat.cast : ℕ → ℤ) := by
    intro x hx
    rw [Function.mem_support] at hx
    rcases lt_or_ge x 0 with h | h
    · exact absurd (ar1Filter_neg φ h) hx
    · exact ⟨x.toNat, Int.toNat_of_nonneg h⟩
  rw [← Function.Injective.tsum_eq Nat.cast_injective hf]
  simp only [ar1Filter_natCast]
  exact tsum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])

/-- Squaring the `AR(1)` filter gives the `AR(1)` filter of `φ²`: `(ar1Filter φ j)² = ar1Filter φ² j`
(since `(φʲ)² = (φ²)ʲ` on `j ≥ 0`, and both vanish for `j < 0`). -/
theorem ar1Filter_sq (φ : ℝ) (j : ℤ) : (ar1Filter φ j) ^ 2 = ar1Filter (φ ^ 2) j := by
  rcases lt_or_ge j 0 with h | h
  · rw [ar1Filter_neg φ h, ar1Filter_neg (φ ^ 2) h]; ring
  · lift j to ℕ using h
    rw [ar1Filter_natCast, ar1Filter_natCast]; ring

/-- The squared `AR(1)` weights sum to `(1 − φ²)⁻¹` — the geometric series `∑_{j≥0} φ^{2j}`. -/
theorem tsum_ar1Filter_sq {φ : ℝ} (hφ : |φ| < 1) : ∑' j, (ar1Filter φ j) ^ 2 = (1 - φ ^ 2)⁻¹ := by
  have hφ2 : |φ ^ 2| < 1 := by rw [abs_pow]; nlinarith [abs_nonneg φ, hφ]
  simp only [ar1Filter_sq]
  exact tsum_ar1Filter hφ2

/-- **Example 3.2.2 (variance):** an `AR(1)` linear process driven by innovations orthogonal up to
`σ²` (`⟪Zₐ, Z_b⟫ = σ²·[a=b]`), with `|φ| < 1`, has variance `γ(0) = ⟪Xₜ, Xₜ⟫ = σ²/(1 − φ²)`. -/
theorem ar1_linearProcess_variance {φ σ2 : ℝ} (hφ : |φ| < 1) {Z : ℤ → Lp ℝ 2 μ} {C : ℝ}
    (hZb : ∀ t, ‖Z t‖ ≤ C) (hZorth : ∀ a b, inner ℝ (Z a) (Z b) = if a = b then σ2 else 0)
    (t : ℤ) :
    inner ℝ (linearProcessLp (ar1Filter φ) Z t) (linearProcessLp (ar1Filter φ) Z t)
      = σ2 * (1 - φ ^ 2)⁻¹ := by
  rw [linearProcessLp_inner_self (summable_ar1Filter hφ) hZb hZorth, tsum_ar1Filter_sq hφ]

end DeepWiki.TimeSeries
