import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

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

/-- Expansion of the order-`n+1` prediction sum: split the top term and apply the Levinson update
(`dlCoeff_succ_of_le`) + the reflected-sum identity to the rest. -/
theorem dl_sum_expand (n : ℕ) (c : ℤ) :
    ∑ j ∈ Icc 1 (n + 1), dlCoeff γ (n + 1) j * γ (c - j)
      = (∑ j ∈ Icc 1 n, dlCoeff γ n j * γ (c - j))
        - dlCoeff γ (n + 1) (n + 1) *
            (∑ j ∈ Icc 1 n, dlCoeff γ n j * γ (c - ((n : ℤ) + 1) + j))
        + dlCoeff γ (n + 1) (n + 1) * γ (c - ((n : ℤ) + 1)) := by
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  have h1 : ∀ j ∈ Icc 1 n, dlCoeff γ (n + 1) j * γ (c - j)
      = dlCoeff γ n j * γ (c - j)
        - dlCoeff γ (n + 1) (n + 1) * (dlCoeff γ n (n + 1 - j) * γ (c - j)) := by
    intro j hj
    rw [dlCoeff_succ_of_le γ n j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_reflect_coeff]
  push_cast
  ring

/-- **Proposition 5.2.1 (Durbin–Levinson, correctness):** for an even autocovariance `γ` whose
prediction errors `vₘ` (`m < n`) are nonzero, the recursively computed coefficients solve the
order-`n` prediction (normal) equations `∑_{j=1}^n φₙⱼ γ(k−j) = γ(k)` (`k = 1,…,n`), and the
mean-square error has the closed form `vₙ = γ(0) − ∑_{j=1}^n φₙⱼ γ(j)`. Proved by a joint induction:
the `k = n+1` prediction equation and the error formula interlock through the reflection coefficient. -/
theorem dl_correct (heven : ∀ h : ℤ, γ (-h) = γ h) :
    ∀ n, (∀ m, m < n → dlError γ m ≠ 0) →
      (∀ k, 1 ≤ k → k ≤ n →
          ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ ((k : ℤ) - j) = γ (k : ℤ))
        ∧ dlError γ n = γ 0 - ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ (j : ℤ) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨fun k hk1 hk2 => by omega, by simp [dlError]⟩
  | succ n ih =>
    intro hv
    have hvn : dlError γ n ≠ 0 := hv n (Nat.lt_succ_self n)
    obtain ⟨ihPE, ihMSE⟩ := ih fun m hm => hv m (Nat.lt_succ_of_lt hm)
    have hdiag := dlCoeff_diag_mul_error γ n hvn
    refine ⟨fun k hk1 hk2 => ?_, ?_⟩
    · rw [dl_sum_expand]
      rcases eq_or_lt_of_le hk2 with hk | hk
      · -- k = n + 1
        subst hk
        push_cast
        simp only [sub_self, zero_add]
        have hv2 : dlCoeff γ (n + 1) (n + 1) * dlError γ n
            = dlCoeff γ (n + 1) (n + 1) * γ 0
              - dlCoeff γ (n + 1) (n + 1) * ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ (j : ℤ) := by
          rw [ihMSE]; ring
        linarith [hdiag, hv2]
      · -- k ≤ n
        have hkn : k ≤ n := by omega
        rw [ihPE k hk1 hkn]
        have hSR : ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ ((k : ℤ) - ((n : ℤ) + 1) + j)
            = γ ((k : ℤ) - ((n : ℤ) + 1)) := by
          have key : ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ ((k : ℤ) - ((n : ℤ) + 1) + j)
              = ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ (((n + 1 - k : ℕ) : ℤ) - j) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            simp only [Finset.mem_Icc] at hj
            congr 1
            rw [← heven (((n + 1 - k : ℕ) : ℤ) - j)]
            congr 1
            omega
          rw [key, ihPE (n + 1 - k) (by omega) (by omega), ← heven ((k : ℤ) - ((n : ℤ) + 1))]
          congr 1
          omega
        rw [hSR]; ring
    · -- mean-square error closed form
      have hconv : ∑ j ∈ Icc 1 (n + 1), dlCoeff γ (n + 1) j * γ (j : ℤ)
          = ∑ j ∈ Icc 1 (n + 1), dlCoeff γ (n + 1) j * γ ((0 : ℤ) - j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show ((0 : ℤ) - j) = -(j : ℤ) by ring, heven]
      have hA : ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ ((0 : ℤ) - j)
          = ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ (j : ℤ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show ((0 : ℤ) - j) = -(j : ℤ) by ring, heven]
      have hB : ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ ((0 : ℤ) - ((n : ℤ) + 1) + j)
          = ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ ((n : ℤ) + 1 - j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show ((0 : ℤ) - ((n : ℤ) + 1) + j) = -((n : ℤ) + 1 - j) by ring, heven]
      have hC : γ ((0 : ℤ) - ((n : ℤ) + 1)) = γ ((n : ℤ) + 1) := by
        rw [show ((0 : ℤ) - ((n : ℤ) + 1)) = -((n : ℤ) + 1) by ring, heven]
      have hAval : ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ (j : ℤ) = γ 0 - dlError γ n := by
        linarith [ihMSE]
      have hBval : ∑ j ∈ Icc 1 n, dlCoeff γ n j * γ ((n : ℤ) + 1 - j)
          = γ ((n : ℤ) + 1) - dlCoeff γ (n + 1) (n + 1) * dlError γ n := by
        linarith [hdiag]
      rw [dlError_succ, hconv, dl_sum_expand, hA, hB, hC, hAval, hBval]
      ring

/-- **Prediction-error product formula** (iterating eq 5.2.5): `vₙ = γ(0) ∏_{k=1}^n (1 − φₖₖ²)`.
In particular the one-step error decreases monotonically with the order `n`. -/
theorem dlError_eq_prod (n : ℕ) :
    dlError γ n = γ 0 * ∏ k ∈ Icc 1 n, (1 - dlCoeff γ k k ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [dlError_succ, ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
    ring

end DeepWiki.TimeSeries
