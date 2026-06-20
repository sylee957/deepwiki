import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Tropical.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Min-plus matrices — foundation for the sub-additive-closure cyclicity theorem
The min-plus semiring `(ℤ ∪ {+∞}, min, +)` is Mathlib's `Tropical (WithTop ℤ)`: addition is `min`,
multiplication is `+`, `𝟘 = +∞ = ⊤`, `𝟙 = (0 : ℤ)`. Matrices over it inherit the (non-commutative)
semiring product `(A * B)ᵢⱼ = ⨁ₖ Aᵢₖ ⊗ Bₖⱼ = ⨅ₖ (Aᵢₖ + Bₖⱼ)` and powers `Aᵏ` from Mathlib.

This is the first step toward the **cyclicity theorem** (`Aᵏ⁺ᵈ = Aᵏ + λd` past a finite rank, BCOQ
"Synchronization and Linearity" Thm 3.112), which computes the sub-additive closure `f* = ⨅ₘ f^⊗ᵐ`
(the closure is *not* a finite truncation of `f^⊗ᵐ` — see `DeepWiki.UppSeq` — but a matrix power that
genuinely stabilizes). A research-scale arc; this file builds the algebraic substrate. -/

namespace DeepWiki.MinPlusMatrix

open Matrix

/-- The **min-plus semiring** `(ℤ ∪ {+∞}, min, +)` — Mathlib's tropical semiring on `WithTop ℤ`:
`⊕ = min`, `⊗ = +`, `𝟘 = ⊤ = +∞`, `𝟙 = (0 : ℤ)`. -/
abbrev MP := Tropical (WithTop ℤ)

/-- The additive identity (`⊕`-zero) of the min-plus semiring is `+∞`. -/
theorem mp_zero : (0 : MP) = Tropical.trop ⊤ := rfl

/-- The multiplicative identity (`⊗`-unit) of the min-plus semiring is `0`. -/
theorem mp_one : (1 : MP) = Tropical.trop (0 : WithTop ℤ) := rfl

/-- `⊕` is `min` on the underlying values. -/
theorem mp_add (a b : MP) : (a + b).untrop = min a.untrop b.untrop := rfl

/-- `⊗` is `+` on the underlying values. -/
theorem mp_mul (a b : MP) : (a * b).untrop = a.untrop + b.untrop := rfl

/-- Min-plus matrices form a semiring (from Mathlib), so the product
`(A * B)ᵢⱼ = ⨅ₖ (Aᵢₖ + Bₖⱼ)` and powers `Aᵏ` are available. -/
example (A : Matrix (Fin 2) (Fin 2) MP) (k : ℕ) : Matrix (Fin 2) (Fin 2) MP := A ^ k

/-- A concrete 2×2 min-plus matrix (entries `0,1,2,0`), for sanity checks. -/
def exA : Matrix (Fin 2) (Fin 2) MP :=
  !![Tropical.trop 0, Tropical.trop 1; Tropical.trop 2, Tropical.trop 0]

/-- Sanity (gate-verified): the min-plus matrix square computes `(A²)₀₀ = min(0+0, 1+2) = 0`,
confirming `Matrix` over `Tropical (WithTop ℤ)` is the min-plus matrix product. -/
example : (exA ^ 2) 0 0 = Tropical.trop 0 := by native_decide

/-- Sanity (gate-verified): `(A²)₀₁ = min(0+1, 1+0) = 1`. -/
example : (exA ^ 2) 0 1 = Tropical.trop 1 := by native_decide

/-- **Min-plus matrix power recursion**: `(Aᵐ⁺¹)ᵢⱼ = ⨅ₖ ((Aᵐ)ᵢₖ + Aₖⱼ)` on the underlying
`WithTop ℤ` values — the "relax over the last edge" step (matrix product `∑ = ⨅`, `⊗ = +`). The basic
tool for the walk/circuit analysis underlying the cyclicity theorem. -/
theorem untrop_pow_succ_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (m : ℕ) (i j : Fin n) :
    ((A ^ (m + 1)) i j).untrop
      = Finset.univ.inf (fun k => ((A ^ m) i k).untrop + (A k j).untrop) := by
  rw [pow_succ, Matrix.mul_apply, Finset.untrop_sum']
  rfl

/-- The **precedence graph** of a min-plus matrix: an edge `i → j` exists iff the entry is finite
(`≠ 𝟘 = +∞`). Its circuits carry the spectral theory (eigenvalue = min mean circuit, cyclicity). -/
def HasEdge {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (i j : Fin n) : Prop := A i j ≠ 0

end DeepWiki.MinPlusMatrix
