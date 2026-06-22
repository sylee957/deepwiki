import DeepWiki.TimeSeries.LinearProcess
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # `§3.2` examples: `MA(q)` and `AR(1)` as `MA(∞)` linear processes
**Example 3.2.1** — the `MA(q)` process `Xₜ = ∑_{j=0}^q θⱼ Zₜ₋ⱼ` is an `MA(∞)` with the finite
filter `ψⱼ = θⱼ` (vacuously summable), and its linear process collapses to that finite sum.
**Example 3.2.2** — the causal `AR(1)` process `Xₜ = φ Xₜ₋₁ + Zₜ` with `|φ| < 1` is an `MA(∞)`
with `ψⱼ = φʲ` (a geometric, hence absolutely summable, filter), with variance `σ²/(1−φ²)` and
autocovariance `σ² φ^|h|/(1−φ²)`. -/

namespace DeepWiki.TimeSeries

open MeasureTheory
open scoped Polynomial

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

/-- The lag-`h` product of `AR(1)` weights (`h ≥ 0`): `ψₖ ψ_{k+h} = φʰ · (ar1Filter φ² k)` — the
`φʰ` factor pulls out, leaving the squared filter. -/
theorem ar1Filter_mul_shift {φ : ℝ} {h : ℤ} (hh : 0 ≤ h) (k : ℤ) :
    ar1Filter φ k * ar1Filter φ (k + h) = φ ^ h.toNat * ar1Filter (φ ^ 2) k := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [ar1Filter_neg φ hk, ar1Filter_neg (φ ^ 2) hk]; ring
  · lift k to ℕ using hk
    lift h to ℕ using hh
    rw [show (k : ℤ) + (h : ℤ) = ((k + h : ℕ) : ℤ) by push_cast; ring]
    simp only [ar1Filter_natCast, Int.toNat_natCast]
    ring

/-- **Example 3.2.2 (autocovariance, `h ≥ 0`):** the causal `AR(1)` linear process driven by
innovations orthogonal up to `σ²` (`|φ| < 1`) has autocovariance `γ(h) = σ² φʰ/(1 − φ²)` for
`h ≥ 0` (so `γ(h) = σ² φ^|h|/(1 − φ²)` by evenness). -/
theorem ar1_linearProcess_acvf {φ σ2 : ℝ} (hφ : |φ| < 1) {Z : ℤ → Lp ℝ 2 μ} {C : ℝ}
    (hZb : ∀ t, ‖Z t‖ ≤ C) (hZorth : ∀ a b, inner ℝ (Z a) (Z b) = if a = b then σ2 else 0)
    (t : ℤ) {h : ℤ} (hh : 0 ≤ h) :
    inner ℝ (linearProcessLp (ar1Filter φ) Z (t + h)) (linearProcessLp (ar1Filter φ) Z t)
      = σ2 * (φ ^ h.toNat * (1 - φ ^ 2)⁻¹) := by
  have hφ2 : |φ ^ 2| < 1 := by rw [abs_pow]; nlinarith [abs_nonneg φ, hφ]
  rw [linearProcessLp_inner (summable_ar1Filter hφ) hZb hZorth]
  congr 1
  calc ∑' k, ar1Filter φ k * ar1Filter φ (k + h)
      = ∑' k, φ ^ h.toNat * ar1Filter (φ ^ 2) k := tsum_congr (ar1Filter_mul_shift hh)
    _ = φ ^ h.toNat * ∑' k, ar1Filter (φ ^ 2) k := tsum_mul_left
    _ = φ ^ h.toNat * (1 - φ ^ 2)⁻¹ := by rw [tsum_ar1Filter hφ2]

/-! ## Example 3.2.1: the `MA(q)` process as an `MA(∞)` -/

/-- The `MA(q)` filter `ψⱼ = θⱼ` (`0 ≤ j ≤ q`), else `0` — the coefficient sequence of the
moving-average polynomial `θ`, as a one-sided finite filter on `ℤ`. -/
noncomputable def maqFilter (θ : ℝ[X]) : ℤ → ℝ := fun j => if 0 ≤ j then θ.coeff j.toNat else 0

/-- `maqFilter θ` at a nonnegative integer `↑n` is the coefficient `θₙ`. -/
@[simp] theorem maqFilter_natCast (θ : ℝ[X]) (n : ℕ) : maqFilter θ (n : ℤ) = θ.coeff n := by
  simp [maqFilter]

/-- `maqFilter θ` vanishes at negative indices. -/
theorem maqFilter_neg (θ : ℝ[X]) {j : ℤ} (hj : j < 0) : maqFilter θ j = 0 := by
  simp only [maqFilter]; exact if_neg (not_le.mpr hj)

/-- **Example 3.2.1:** the `MA(q)` filter `ψⱼ = θⱼ` is (absolutely) summable — it is finitely
supported (`ψⱼ = 0` for `j > deg θ`), so the `MA(q)` is trivially an `MA(∞)` (Definition 3.2.1). -/
theorem summable_maqFilter (θ : ℝ[X]) : Summable (maqFilter θ) :=
  summable_of_ne_finset_zero (s := Finset.Icc 0 (θ.natDegree : ℤ)) (fun j hj => by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    rcases hj with h | h
    · exact maqFilter_neg θ h
    · simp only [maqFilter]
      rw [if_pos (by omega : (0 : ℤ) ≤ j)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))

/-- **Example 3.2.1:** the `MA(∞)` linear process with the finite `MA(q)` filter collapses to the
finite moving average `Xₜ = ∑_{j=0}^q θⱼ Zₜ₋ⱼ` (the `MA(q)` defining sum `θ(B) Z`). -/
theorem linearProcessLp_maqFilter_eq (θ : ℝ[X]) (Z : ℤ → Lp ℝ 2 μ) (t : ℤ) :
    linearProcessLp (maqFilter θ) Z t
      = ∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j • Z (t - j) := by
  have hsupp : Function.support (fun j : ℤ => maqFilter θ j • Z (t - j)) ⊆
      Set.range (Nat.cast : ℕ → ℤ) := by
    intro x hx
    rw [Function.mem_support] at hx
    rcases lt_or_ge x 0 with h | h
    · exact absurd (by rw [maqFilter_neg θ h, zero_smul]) hx
    · exact ⟨x.toNat, Int.toNat_of_nonneg h⟩
  rw [linearProcessLp, ← Function.Injective.tsum_eq Nat.cast_injective hsupp]
  simp only [maqFilter_natCast]
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]

/-- `maqFilter θ` vanishes beyond the degree: `ψₘ = 0` once `deg θ < m`. -/
theorem maqFilter_eq_zero_of_natDegree_lt (θ : ℝ[X]) {m : ℤ} (hm : (θ.natDegree : ℤ) < m) :
    maqFilter θ m = 0 := by
  simp only [maqFilter, if_pos (by omega : (0 : ℤ) ≤ m)]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- **The `MA(q)` autocovariance has finite support:** `∑ₖ ψₖ ψ_{k+h} = 0` for `|h| > deg θ` — the
defining property of an `MA(q)` process, that its autocovariance `γ(h) = σ² ∑ₖ ψₖ ψ_{k+h}` vanishes
at every lag beyond the order `q = deg θ`. A pure consequence of the filter's finite support. -/
theorem maqFilter_tsum_mul_shift_eq_zero (θ : ℝ[X]) {h : ℤ} (hh : (θ.natDegree : ℤ) < |h|) :
    ∑' k : ℤ, maqFilter θ k * maqFilter θ (k + h) = 0 := by
  have hz : ∀ k : ℤ, maqFilter θ k * maqFilter θ (k + h) = 0 := by
    intro k
    rcases le_or_gt 0 k with hk | hk
    · rcases le_or_gt k (θ.natDegree : ℤ) with hkd | hkd
      · rcases lt_abs.mp hh with hpos | hneg
        · rw [maqFilter_eq_zero_of_natDegree_lt θ (by omega : (θ.natDegree : ℤ) < k + h), mul_zero]
        · rw [maqFilter_neg θ (by omega : k + h < 0), mul_zero]
      · rw [maqFilter_eq_zero_of_natDegree_lt θ hkd, zero_mul]
    · rw [maqFilter_neg θ hk, zero_mul]
  simp only [hz, tsum_zero]

/-- **The `MA(q)` autocovariance, explicit formula** (`0 ≤ h`): `∑ₖ ψₖ ψ_{k+h} = ∑_{k=0}^q θₖ θ_{k+h}`,
so by Theorem 3.2.1 the `MA(q)` autocovariance is `γ(h) = σ² ∑_{k=0}^{q−h} θₖ θ_{k+h}` for `0 ≤ h ≤ q`
(the terms with `k + h > q` vanish), the classical `MA(q)` acvf. -/
theorem maqFilter_tsum_mul_shift_eq (θ : ℝ[X]) {h : ℤ} (hh : 0 ≤ h) :
    ∑' k : ℤ, maqFilter θ k * maqFilter θ (k + h)
      = ∑ k ∈ Finset.range (θ.natDegree + 1), θ.coeff k * θ.coeff (k + h.toNat) := by
  have key : ∀ n : ℕ, maqFilter θ ((n : ℤ) + h) = θ.coeff (n + h.toNat) := by
    intro n
    simp only [maqFilter, if_pos (by omega : (0 : ℤ) ≤ (n : ℤ) + h)]
    congr 1; omega
  have hsupp : Function.support (fun k : ℤ => maqFilter θ k * maqFilter θ (k + h)) ⊆
      Set.range (Nat.cast : ℕ → ℤ) := by
    intro k hk
    rw [Function.mem_support] at hk
    rcases le_or_gt 0 k with h0 | h0
    · exact ⟨k.toNat, Int.toNat_of_nonneg h0⟩
    · exact absurd (by rw [maqFilter_neg θ h0, zero_mul]) hk
  rw [← Function.Injective.tsum_eq Nat.cast_injective hsupp]
  simp only [maqFilter_natCast, key]
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : θ.natDegree < n), zero_mul]

/-- `maqFilter θ` is absolutely summable — finitely supported, so `∑ⱼ ‖ψⱼ‖ < ∞`. -/
theorem summable_norm_maqFilter (θ : ℝ[X]) : Summable (fun j => ‖maqFilter θ j‖) :=
  summable_of_ne_finset_zero (s := Finset.Icc 0 (θ.natDegree : ℤ)) (fun j hj => by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    rcases hj with hj | hj
    · rw [maqFilter_neg θ hj, norm_zero]
    · rw [maqFilter, if_pos (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        norm_zero])

/-- **Asymptotic-variance identity (B&D Theorem 7.1.2's `v`):** the sum of all autocovariance terms
of a finite `MA(q)` filter equals the square of its total weight,
`∑ₕ ∑ₖ ψₖ ψ_{k+h} = (∑ⱼ ψⱼ)²` — so `∑ₕ γ(h) = σ²(∑θ)²`, matching the `MA(q)` central-limit-theorem
variance to the sum of autocovariances of Theorem 7.1.1. Fubini on the absolutely summable double
series (reindexed `(h,k) ↦ (k, k+h)`) plus shift-invariance of the inner sum. -/
theorem maqFilter_acvfSum (θ : ℝ[X]) :
    ∑' h : ℤ, ∑' k : ℤ, maqFilter θ k * maqFilter θ (k + h) = (∑' j : ℤ, maqFilter θ j) ^ 2 := by
  set ψ := maqFilter θ with hψdef
  have hns : Summable (fun j => ‖ψ j‖) := summable_norm_maqFilter θ
  have hprod : Summable (fun q : ℤ × ℤ => ψ q.1 * ψ q.2) :=
    summable_mul_of_summable_norm hns hns
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.2, p.2 + p.1)
      invFun := fun q => (q.2 - q.1, q.1)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  have hsum2 : Summable (fun p : ℤ × ℤ => ψ p.2 * ψ (p.2 + p.1)) := by
    have hcomp : (fun p : ℤ × ℤ => ψ p.2 * ψ (p.2 + p.1)) = (fun q : ℤ × ℤ => ψ q.1 * ψ q.2) ∘ e := by
      ext ⟨h, k⟩; rfl
    rw [hcomp]; exact (e.summable_iff).mpr hprod
  have step2 : (∑' p : ℤ × ℤ, ψ p.2 * ψ (p.2 + p.1)) = ∑' q : ℤ × ℤ, ψ q.1 * ψ q.2 :=
    Equiv.tsum_eq e (fun q => ψ q.1 * ψ q.2)
  have hrow_prod : ∀ b : ℤ, Summable fun c : ℤ => ψ b * ψ c :=
    fun b => (summable_maqFilter θ).mul_left (ψ b)
  have hrow_sum2 : ∀ b : ℤ, Summable fun c : ℤ => ψ c * ψ (c + b) := fun b =>
    summable_of_ne_finset_zero (s := Finset.Icc 0 (θ.natDegree : ℤ)) (fun c hc => by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hc
      rcases hc with hc | hc
      · rw [hψdef, maqFilter_neg θ hc, zero_mul]
      · rw [show ψ c = θ.coeff c.toNat from by
            simp only [hψdef, maqFilter, if_pos (by omega : (0 : ℤ) ≤ c)],
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : θ.natDegree < c.toNat), zero_mul])
  rw [← hsum2.tsum_prod' hrow_sum2, step2, hprod.tsum_prod' hrow_prod]
  simp_rw [tsum_mul_left]
  rw [tsum_mul_right, sq]

end DeepWiki.TimeSeries
