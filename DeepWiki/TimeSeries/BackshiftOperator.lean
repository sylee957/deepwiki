import Mathlib.Algebra.Ring.Pi
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-! # The backshift and difference operators
The backshift operator `B`, the difference operator `∇ = 1 − B`, and the lag-`d`
difference `∇_d = 1 − Bᵈ`, used to eliminate polynomial trend and seasonal
components from a time series (§1.4). Deterministic operators on bi-infinite
sequences `ℤ → V`. -/

namespace DeepWiki.TimeSeries

variable {V : Type*}

/-! ## The backshift operator `B` -/

/-- The backshift operator `B`: `(B x) t = x (t − 1)`. -/
def backshift (x : ℤ → V) : ℤ → V := fun t => x (t - 1)

@[simp] theorem backshift_apply (x : ℤ → V) (t : ℤ) : backshift x t = x (t - 1) := rfl

/-- The forward shift `B⁻¹`: `(forwardShift x) t = x (t + 1)`. -/
def forwardShift (x : ℤ → V) : ℤ → V := fun t => x (t + 1)

@[simp] theorem forwardShift_apply (x : ℤ → V) (t : ℤ) : forwardShift x t = x (t + 1) := rfl

/-- `B⁻¹` is a left inverse of `B`: `B⁻¹ (B x) = x`. -/
theorem backshift_leftInverse :
    Function.LeftInverse (forwardShift : (ℤ → V) → ℤ → V) backshift := by
  intro x; funext t; simp

/-- `B⁻¹` is a right inverse of `B`: `B (B⁻¹ x) = x`. -/
theorem backshift_rightInverse :
    Function.RightInverse (forwardShift : (ℤ → V) → ℤ → V) backshift := by
  intro x; funext t; simp

/-- The backshift is a bijection of the sequence space `ℤ → V`. -/
theorem backshift_bijective : Function.Bijective (backshift : (ℤ → V) → ℤ → V) :=
  ⟨backshift_leftInverse.injective, backshift_rightInverse.surjective⟩

/-- `(B^[n] x) t = x (t − n)`. -/
@[simp] theorem backshift_iterate_apply (n : ℕ) (x : ℤ → V) (t : ℤ) :
    (backshift^[n] x) t = x (t - n) := by
  induction n generalizing t with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', backshift_apply, ih]
    congr 1
    push_cast
    ring

/-- `Bⁿ` lags by `n`: `B^[n] x = fun t => x (t − n)`. -/
theorem backshift_iterate (n : ℕ) (x : ℤ → V) : backshift^[n] x = fun t => x (t - n) := by
  funext t; exact backshift_iterate_apply n x t

/-- `B` is additive: `B (x + y) = B x + B y`. -/
theorem backshift_add [Add V] (x y : ℤ → V) :
    backshift (x + y) = backshift x + backshift y := by funext t; simp [Pi.add_apply]

/-! ## The difference operator `∇ = 1 − B` -/

variable [AddCommGroup V]

/-- The difference operator `∇ = 1 − B`: `(∇ x) t = x t − x (t − 1)`. -/
def difference (x : ℤ → V) : ℤ → V := fun t => x t - x (t - 1)

@[simp] theorem difference_apply (x : ℤ → V) (t : ℤ) :
    difference x t = x t - x (t - 1) := rfl

/-- `∇ = id − B` pointwise. -/
theorem difference_eq_sub_backshift (x : ℤ → V) : difference x = x - backshift x := by
  funext t; simp [Pi.sub_apply]

/-- `∇` annihilates a constant series: `∇ c = 0`. -/
@[simp] theorem difference_const (c : V) : difference (fun _ : ℤ => c) = 0 := by
  funext t; simp

/-- `∇` is additive: `∇ (x + y) = ∇ x + ∇ y`. -/
theorem difference_add (x y : ℤ → V) :
    difference (x + y) = difference x + difference y := by
  funext t; simp only [difference_apply, Pi.add_apply]; abel

/-! ## The lag-`d` difference `∇_d = 1 − Bᵈ` (eq. 1.4.19) -/

/-- The lag-`d` difference `∇_d = 1 − Bᵈ`: `(∇_d x) t = x t − x (t − d)`. Not to be
confused with the iterate `∇^[d] = (1 − B)^[d]`. -/
def seasonalDifference (d : ℕ) (x : ℤ → V) : ℤ → V := fun t => x t - x (t - d)

@[simp] theorem seasonalDifference_apply (d : ℕ) (x : ℤ → V) (t : ℤ) :
    seasonalDifference d x t = x t - x (t - d) := rfl

/-- `∇_d = id − Bᵈ` pointwise. -/
theorem seasonalDifference_eq_sub_backshift_iterate (d : ℕ) (x : ℤ → V) :
    seasonalDifference d x = x - backshift^[d] x := by
  funext t; simp [Pi.sub_apply]

/-- `∇_1 = ∇`: the lag-1 difference is the ordinary difference. -/
theorem seasonalDifference_one : (seasonalDifference 1 : (ℤ → V) → ℤ → V) = difference := by
  funext x t; simp

/-- `∇_d` removes a seasonal component of period `d`: if `s (t + d) = s t` for all
`t`, then `∇_d s = 0`. -/
theorem seasonalDifference_periodic {d : ℕ} {s : ℤ → V}
    (hper : ∀ t : ℤ, s (t + d) = s t) : seasonalDifference d s = 0 := by
  funext t
  have key : s t - s (t - (d : ℤ)) = 0 := by
    rw [sub_eq_zero]
    have hidx : (t - (d : ℤ)) + (d : ℤ) = t := by ring
    have h := hper (t - (d : ℤ))
    rwa [hidx] at h
  simpa using key

/-! ## Trend reduction -/

/-- `∇` reduces a linear (degree-1) trend to a constant: `∇ (a·t + b) = a`. -/
theorem difference_linear {R : Type*} [CommRing R] (a b : R) :
    difference (fun t : ℤ => a * (t : R) + b) = fun _ => a := by
  funext t
  simp only [difference_apply]
  push_cast
  ring

/-- **Problem 1.8(b)**: the second seasonal difference `∇_d²` annihilates a linearly
modulated period-`d` seasonal component: `∇_d (∇_d ((a + b·t)·sₜ)) = 0` when `{sₜ}` has
period `d`. One `∇_d` turns `(a + b·t)·sₜ` into the period-`d` series `b·d·sₜ`; the second
`∇_d` kills it. -/
theorem seasonalDifference_sq_linear_periodic {d : ℕ} (a b : ℝ) {s : ℤ → ℝ}
    (hper : ∀ t : ℤ, s (t + d) = s t) :
    seasonalDifference d (seasonalDifference d (fun t : ℤ => (a + b * (t : ℝ)) * s t)) = 0 := by
  have hg : seasonalDifference d (fun t : ℤ => (a + b * (t : ℝ)) * s t)
      = fun t => b * (d : ℝ) * s t := by
    funext t
    have hst : s (t - (d : ℤ)) = s t := by
      have h := hper (t - (d : ℤ))
      rw [show (t - (d : ℤ)) + (d : ℤ) = t from by ring] at h
      exact h.symm
    simp only [seasonalDifference_apply, hst]
    push_cast
    ring
  rw [hg]
  apply seasonalDifference_periodic
  intro t
  show b * (d : ℝ) * s (t + (d : ℤ)) = b * (d : ℝ) * s t
  rw [hper t]

/-- The book's caution (§1.4, p.24): the lag-`d` difference `∇_d` is **not** the
iterate `∇^[d] = (1 − B)^[d]`. Already at `d = 2` they disagree — on the trend
`x t = t`, `∇_2 x = 2` (constant) while `∇^[2] x = 0`. -/
example : seasonalDifference 2 (fun t : ℤ => t) ≠ difference^[2] (fun t : ℤ => t) := by
  intro h
  have h0 := congrFun h 0
  simp only [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    seasonalDifference_apply, difference_apply] at h0
  norm_num at h0

end DeepWiki.TimeSeries
