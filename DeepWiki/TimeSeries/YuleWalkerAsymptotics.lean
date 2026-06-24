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
theorem differentiable_det {p : ℕ} :
    Differentiable ℝ (fun M : Matrix (Fin p) (Fin p) ℝ => M.det) := by
  have hentry : ∀ a b : Fin p, Differentiable ℝ (fun M : Matrix (Fin p) (Fin p) ℝ => M a b) :=
    fun a b => differentiable_pi.mp (differentiable_pi.mp differentiable_id a) b
  have hprod : ∀ σ : Equiv.Perm (Fin p),
      Differentiable ℝ (fun M : Matrix (Fin p) (Fin p) ℝ => ∏ i, M (σ i) i) := fun σ M =>
    (HasFDerivAt.finsetProd (u := Finset.univ) (g := fun i (M : Matrix (Fin p) (Fin p) ℝ) => M (σ i) i)
      fun i _ => (hentry (σ i) i M).hasFDerivAt).differentiableAt
  simp only [Matrix.det_apply]
  exact Differentiable.fun_sum fun σ _ => (hprod σ).const_smul _

end DeepWiki.TimeSeries
