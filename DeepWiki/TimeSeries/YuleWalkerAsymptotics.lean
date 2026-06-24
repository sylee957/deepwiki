import DeepWiki.TimeSeries.YuleWalker
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Differentiability of the Yule–Walker estimator (toward Theorem 8.1.1)
The Yule–Walker estimator `φ̂ = Γ̂⁻¹ γ̂` is a differentiable function of the sample autocovariances
(at invertible `Γ̂`), via the determinant/adjugate formula `A⁻¹ = (det A)⁻¹ • adjugate A` — the
matrix-calculus prerequisite for the asymptotic normality of `φ̂` through the multivariate delta method.
Mathlib provides only *continuity* of `det`/`adjugate`/`⁻¹`; these are the differentiability analogues. -/

namespace DeepWiki.TimeSeries

open Matrix
open scoped Matrix.Norms.Elementwise

/-- The determinant `Matrix (Fin p) (Fin p) ℝ → ℝ` is differentiable — a polynomial in the entries
(the Leibniz sum of signed products, each entry access a continuous linear projection). -/
theorem differentiable_det_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℕ}
    {A : E → Matrix (Fin p) (Fin p) ℝ} (hA : ∀ i j, Differentiable ℝ (fun x => A x i j)) :
    Differentiable ℝ (fun x => (A x).det) := by
  have hprod : ∀ σ : Equiv.Perm (Fin p), Differentiable ℝ (fun x => ∏ i, A x (σ i) i) := fun σ x =>
    (HasFDerivAt.finsetProd (u := Finset.univ) (g := fun i x => A x (σ i) i)
      fun i _ => (hA (σ i) i x).hasFDerivAt).differentiableAt
  simp only [Matrix.det_apply]
  exact Differentiable.fun_sum fun σ _ => (hprod σ).const_smul _

/-- The determinant `Matrix (Fin p) (Fin p) ℝ → ℝ` is differentiable — the `A = id` case of
`differentiable_det_comp` (each entry access `M ↦ M i j` is a coordinate projection). -/
theorem differentiable_det {p : ℕ} :
    Differentiable ℝ (fun M : Matrix (Fin p) (Fin p) ℝ => M.det) :=
  differentiable_det_comp fun i j => differentiable_pi.mp (differentiable_pi.mp differentiable_id i) j

/-- Each adjugate entry `M ↦ adjugate M i j = (M.updateRow j (Pi.single i 1)).det` is differentiable
(a determinant whose entries are either constants or coordinate projections of `M`). -/
theorem differentiable_adjugate_entry {p : ℕ} (i j : Fin p) :
    Differentiable ℝ (fun M : Matrix (Fin p) (Fin p) ℝ => M.adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine differentiable_det_comp fun a b => ?_
  by_cases h : a = j
  · simp only [Matrix.updateRow_apply, if_pos h]
    exact differentiable_const _
  · simp only [Matrix.updateRow_apply, if_neg h]
    exact differentiable_pi.mp (differentiable_pi.mp differentiable_id a) b

end DeepWiki.TimeSeries
