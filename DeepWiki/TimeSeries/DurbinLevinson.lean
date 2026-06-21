import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic

/-! # §5.2 — The Durbin–Levinson algorithm (Proposition 5.2.1)

A purely algebraic recursion on an autocovariance `γ : ℤ → ℝ` computing the one-step prediction
coefficients `φₙⱼ` and mean-square errors `vₙ`. The recursion solves the order-`n` Toeplitz
prediction equations `∑_{j=1}^n φₙⱼ γ(k−j) = γ(k)` (`k = 1,…,n`) — the normal equations of §5.1 —
without reference to the underlying `L²` process; the connection to the projection is `eq_5_1_5`.

Coefficients are indexed `1 ≤ j ≤ n` (zero elsewhere). The recursion (eqs 5.2.4–5.2.5):
`φₙₙ = [γ(n) − ∑_{j<n} φ_{n−1,j} γ(n−j)] / v_{n−1}`, `φₙⱼ = φ_{n−1,j} − φₙₙ φ_{n−1,n−j}`,
`vₙ = v_{n−1}(1 − φₙₙ²)`, `v₀ = γ(0)`. -/

namespace DeepWiki.TimeSeries

open Finset

variable (γ : ℤ → ℝ)

/-- The reflection coefficient (partial autocorrelation) `φ_{n+1,n+1}` from order-`n` data
`p = (vₙ, φₙ,·)`: `[γ(n+1) − ∑_{j=1}^n φₙⱼ γ(n+1−j)] / vₙ`. -/
noncomputable def dlRefl (n : ℕ) (p : ℝ × (ℕ → ℝ)) : ℝ :=
  (γ (n + 1) - ∑ j ∈ Icc 1 n, p.2 j * γ (n + 1 - j)) / p.1

/-- One Durbin–Levinson update: from order-`n` data `(vₙ, φₙ,·)` produce order `n+1`
(`φ_{n+1,n+1} = dlRefl`, the lower coefficients via the Levinson update). -/
noncomputable def dlStep (n : ℕ) (p : ℝ × (ℕ → ℝ)) : ℝ × (ℕ → ℝ) :=
  (p.1 * (1 - dlRefl γ n p ^ 2),
    fun j => if j = n + 1 then dlRefl γ n p
      else if 1 ≤ j ∧ j ≤ n then p.2 j - dlRefl γ n p * p.2 (n + 1 - j) else 0)

/-- The Durbin–Levinson recursion `dl γ n = (vₙ, φₙ,·)`: order-`n` mean-square error and prediction
coefficients, from `v₀ = γ(0)` and the zero coefficient sequence. -/
noncomputable def dl (n : ℕ) : ℝ × (ℕ → ℝ) :=
  Nat.rec (γ 0, fun _ => 0) (dlStep γ) n

/-- The order-`n` prediction coefficients `φₙⱼ` (supported on `1 ≤ j ≤ n`). -/
noncomputable def dlCoeff (n j : ℕ) : ℝ := (dl γ n).2 j

/-- The order-`n` mean-square prediction error `vₙ`. -/
noncomputable def dlError (n : ℕ) : ℝ := (dl γ n).1

@[simp] theorem dl_zero : dl γ 0 = (γ 0, fun _ => 0) := rfl

theorem dl_succ (n : ℕ) : dl γ (n + 1) = dlStep γ n (dl γ n) := rfl

@[simp] theorem dlError_zero : dlError γ 0 = γ 0 := rfl

/-- The new reflection coefficient `φ_{n+1,n+1} = [γ(n+1) − ∑_{j=1}^n φₙⱼ γ(n+1−j)] / vₙ`
(the top case of eq 5.2.4). -/
theorem dlCoeff_succ_diag (n : ℕ) :
    dlCoeff γ (n + 1) (n + 1) = dlRefl γ n (dl γ n) := by
  simp [dlCoeff, dl_succ, dlStep]

/-- `vₙ = v_{n−1}(1 − φₙₙ²)` (eq 5.2.5). -/
theorem dlError_succ (n : ℕ) :
    dlError γ (n + 1) = dlError γ n * (1 - dlCoeff γ (n + 1) (n + 1) ^ 2) := by
  rw [dlCoeff_succ_diag]
  simp [dlError, dl_succ, dlStep]

/-- The Levinson update for the lower coefficients: `φ_{n+1,j} = φₙⱼ − φ_{n+1,n+1} φ_{n,n+1−j}`
for `1 ≤ j ≤ n` (eq 5.2.4). -/
theorem dlCoeff_succ_of_le (n j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    dlCoeff γ (n + 1) j
      = dlCoeff γ n j - dlCoeff γ (n + 1) (n + 1) * dlCoeff γ n (n + 1 - j) := by
  have h : dlCoeff γ (n + 1) j
      = (dl γ n).2 j - dlRefl γ n (dl γ n) * (dl γ n).2 (n + 1 - j) := by
    rw [dlCoeff, dl_succ, dlStep]
    dsimp only
    rw [if_neg (by omega : j ≠ n + 1), if_pos (And.intro hj1 hjn)]
  rw [h, dlCoeff_succ_diag]
  simp only [dlCoeff]

/-- The order-`1` coefficient `φ₁₁ = γ(1)/γ(0)`. -/
theorem dlCoeff_one_one : dlCoeff γ 1 1 = γ 1 / γ 0 := by
  rw [dlCoeff_succ_diag, dlRefl, dl_zero]
  simp

/-- **Base case of the prediction equations (order 1):** `φ₁₁ γ(0) = γ(1)`. -/
theorem dl_prediction_eq_one (h0 : γ 0 ≠ 0) : dlCoeff γ 1 1 * γ 0 = γ 1 := by
  rw [dlCoeff_one_one, div_mul_cancel₀ _ h0]

/-- Reflection of a sum over `Icc 1 n`: `j ↦ n+1−j` is an involution on `{1,…,n}`. -/
theorem sum_Icc_reflect {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ j ∈ Icc 1 n, f (n + 1 - j) = ∑ j ∈ Icc 1 n, f j := by
  refine Finset.sum_nbij' (fun j => n + 1 - j) (fun j => n + 1 - j) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro _ _; rfl

/-- The defining relation of the reflection coefficient: `φ_{n+1,n+1} · vₙ = γ(n+1) − ∑ⱼ φₙⱼ γ(n+1−j)`
(eq 5.2.4 cleared of the division, valid when `vₙ ≠ 0`). -/
theorem dlCoeff_diag_mul_error (n : ℕ) (hvn : dlError γ n ≠ 0) :
    dlCoeff γ (n + 1) (n + 1) * dlError γ n
      = γ ((n : ℤ) + 1) - ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ ((n : ℤ) + 1 - j) := by
  rw [dlCoeff_succ_diag, dlRefl, ← dlError, div_mul_cancel₀ _ hvn]
  simp only [dlCoeff]

/-- The reflected-coefficient sum: reindexing `j ↦ n+1−j` in `∑ⱼ φ_{n,n+1−j} γ(c−j)`. -/
theorem sum_reflect_coeff (n : ℕ) (c : ℤ) :
    ∑ j ∈ Icc 1 n, dlCoeff γ n (n + 1 - j) * γ (c - j)
      = ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ (c - ((n : ℤ) + 1) + j) := by
  rw [← sum_Icc_reflect (fun i => dlCoeff γ n i * γ (c - ((n : ℤ) + 1) + i)) n]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_Icc] at hj
  have hc : c - ((n : ℤ) + 1) + ↑(n + 1 - j) = c - j := by omega
  rw [hc]

end DeepWiki.TimeSeries
