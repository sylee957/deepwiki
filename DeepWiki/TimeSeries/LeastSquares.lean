import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Real.Basic

/-! # Least-squares normal equations (§2.5)
For an over-determined system, the least-squares coefficient `β` is characterized by the **normal
equations** `XᵀX β = Xᵀx`: they are exactly the condition that the residual `x − Xβ` be orthogonal to
the column space of `X`. -/

open Matrix

namespace DeepWiki.TimeSeries

/-- **§2.5 — the least-squares normal equations give residual orthogonality**: if `β` solves the
normal equations `XᵀX β = Xᵀx` (here in `mulVec` form `Xᵀ(Xβ) = Xᵀx`), then the residual `x − Xβ` is
orthogonal to every column-space vector `Xv` (`⟪Xv, x − Xβ⟫ = 0`), so `Xβ` is the least-squares
approximation of `x` onto `col(X)`. -/
theorem residual_orthogonal_of_normalEquations {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℝ) (x : m → ℝ) (β : n → ℝ) (h : Xᵀ *ᵥ (X *ᵥ β) = Xᵀ *ᵥ x) (v : n → ℝ) :
    (X *ᵥ v) ⬝ᵥ (x - X *ᵥ β) = 0 := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, mulVec_sub, h, sub_self,
    zero_dotProduct]

end DeepWiki.TimeSeries
