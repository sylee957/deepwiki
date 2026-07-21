import DeepWiki.CAlgebra.Frontend.Expr
import DeepWiki.CAlgebra.Integrate.RatIntegrateSpec
import DeepWiki.CAlgebra.Frontend.IntegralExpr

/-! # The integration frontend

`integrateExpr` — normalize a rational-function expression and run the verified
integration pipeline — with end-to-end soundness: the produced integral differentiates
to the expression's denotation. -/

namespace DeepWiki.CAlgebra

universe u

namespace Expr

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R] [DensePolyGcd R]
  [DensePolySquarefree R]

open DensePoly

/-- **The frontend integrator**: normalize the expression into the canonical fraction
field and run the verified pipeline. -/
def integrateExpr (e : Expr R) : ResultRatIntegral R :=
  ratIntegrate e.toFrac

open scoped Differential FormalDiff in
/-- **End-to-end soundness of the frontend**: `D(∫ e) = ⟦e⟧` — the produced integral's
derivative is the expression's denotation. -/
theorem integrateExpr_sound [IsAlgClosed R] (e : Expr R) :
    (integrateExpr e).deriv = e.eval := by
  rw [integrateExpr, ratIntegrate_sound, Expr.toRatFunc_toFrac]

/-- **The frontend integrator, to output syntax**: the antiderivative rendered as an
expression `rational + ∫poly + ∑ᵢ RootSum(Qᵢ, α ↦ α · log Sᵢ(α, x))`. -/
def integrateAst (e : Expr R) : IntegralExpr R :=
  (integrateExpr e).toExpr

open scoped Differential FormalDiff in
/-- **End-to-end soundness on syntax**: `D(∫ e) = ⟦e⟧` — the output expression's formal
derivative is the input expression's denotation. -/
theorem integrateAst_sound [IsAlgClosed R] (e : Expr R) :
    (integrateAst e).deriv = e.eval := by
  rw [integrateAst, ResultRatIntegral.toExpr_deriv]
  exact integrateExpr_sound e

end Expr

end DeepWiki.CAlgebra
