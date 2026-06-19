import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! # State-space models (§12.1)
A (time-invariant) linear state-space model: the observation equation `Yₜ = G Xₜ + Wₜ` (eq 12.1.1)
and the state equation `X_{t+1} = F Xₜ + Vₜ` (eq 12.1.2), with `F` the state-transition matrix and
`G` the observation matrix. -/

namespace DeepWiki.TimeSeries

open Matrix

variable {w v : ℕ}

/-- **§12.1 (eq 12.1.1 and 12.1.2)**: a (time-invariant) linear **state-space model** with a
`v`-dimensional state and `w`-dimensional observation, given by the state-transition matrix `F`
and the observation matrix `G`. -/
structure StateSpaceModel (w v : ℕ) where
  /-- State-transition matrix `F` of the state equation `X_{t+1} = F Xₜ + Vₜ`. -/
  F : Matrix (Fin v) (Fin v) ℝ
  /-- Observation matrix `G` of the observation equation `Yₜ = G Xₜ + Wₜ`. -/
  G : Matrix (Fin w) (Fin v) ℝ

namespace StateSpaceModel

/-- The **state trajectory** `Xₜ` driven by an initial state `x₁` and a state-noise sequence `V`,
defined by the state equation `X_{t+1} = F Xₜ + Vₜ` (eq 12.1.2). -/
def state (M : StateSpaceModel w v) (x₁ : Fin v → ℝ) (V : ℕ → Fin v → ℝ) : ℕ → Fin v → ℝ
  | 0 => x₁
  | (t + 1) => M.F *ᵥ M.state x₁ V t + V t

/-- The **observation** `Yₜ = G Xₜ + Wₜ` (eq 12.1.1) of a state trajectory `X` under an
observation-noise sequence `W`. -/
def obs (M : StateSpaceModel w v) (X : ℕ → Fin v → ℝ) (W : ℕ → Fin w → ℝ) (t : ℕ) : Fin w → ℝ :=
  M.G *ᵥ X t + W t

/-- The observation equation `Yₜ = G Xₜ + Wₜ` (eq 12.1.1), pointwise. -/
theorem obs_apply (M : StateSpaceModel w v) (X : ℕ → Fin v → ℝ) (W : ℕ → Fin w → ℝ) (t : ℕ) :
    M.obs X W t = M.G *ᵥ X t + W t := rfl

/-- The state equation `X_{t+1} = F Xₜ + Vₜ` (eq 12.1.2). -/
theorem state_succ (M : StateSpaceModel w v) (x₁ : Fin v → ℝ) (V : ℕ → Fin v → ℝ) (t : ℕ) :
    M.state x₁ V (t + 1) = M.F *ᵥ M.state x₁ V t + V t := rfl

/-- With zero state noise the state evolves deterministically as `Xₜ = Fᵗ x₁`. -/
theorem state_zero_noise (M : StateSpaceModel w v) (x₁ : Fin v → ℝ) (t : ℕ) :
    M.state x₁ 0 t = (M.F ^ t) *ᵥ x₁ := by
  induction t with
  | zero => simp [state, pow_zero, one_mulVec]
  | succ t ih => rw [state_succ, ih, Pi.zero_apply, add_zero, mulVec_mulVec, pow_succ']

end StateSpaceModel

end DeepWiki.TimeSeries
