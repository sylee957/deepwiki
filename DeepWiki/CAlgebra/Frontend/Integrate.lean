import DeepWiki.CAlgebra.Frontend.Expr
import DeepWiki.CAlgebra.Integrate.DerivDataSpec
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

/-- **End-to-end soundness of the frontend, data-level**: `D(∫ e)` is the expression's
computable normalization — an equation between canonical fractions. -/
theorem integrateExpr_sound [IsAlgClosed R] (e : Expr R) :
    (integrateExpr e).deriv = e.toFrac := by
  rw [integrateExpr, ratIntegrate_sound]

/-- **End-to-end denoted soundness of the frontend**: `D(∫ e) = ⟦e⟧` — the produced
integral's computable derivative reads as the expression's denotation. -/
theorem toRatFunc_integrateExpr_deriv [IsAlgClosed R] (e : Expr R) :
    DenseFrac.toRatFunc (integrateExpr e).deriv = e.eval := by
  rw [integrateExpr_sound, Expr.toRatFunc_toFrac]

/-- **The frontend integrator, to output syntax**: the antiderivative rendered as an
expression `rational + ∫poly + ∑ᵢ RootSum(Qᵢ, α ↦ α · log Sᵢ(α, x))`. -/
def integrateAst (e : Expr R) : IntegralExpr R :=
  (integrateExpr e).toExpr

open scoped Differential FormalDiff in
/-- **End-to-end soundness on syntax**: `D(∫ e) = ⟦e⟧` — the output expression's formal
derivative is the input expression's denotation. -/
theorem integrateAst_sound [IsAlgClosed R] (e : Expr R) :
    (integrateAst e).deriv = e.eval := by
  rw [integrateAst, ResultRatIntegral.toExpr_deriv (integrateExpr e)
      (lrtIntegrate_pairs_ne_zero (hermiteReduce e.toFrac).logPart
        (hermiteReduce e.toFrac).logPart_den_squarefree
        (hermiteReduce e.toFrac).logPart_isProper)]
  exact toRatFunc_integrateExpr_deriv e

/-- **Completeness of the frontend, record form**: every expression has an integration
result — a record whose computable derivative is its normalization. -/
theorem integrateExpr_complete [IsAlgClosed R] (e : Expr R) :
    ∃ res : ResultRatIntegral R, res.deriv = e.toFrac :=
  ⟨integrateExpr e, integrateExpr_sound e⟩

open scoped Differential FormalDiff in
/-- **Completeness of the frontend, syntax form**: every expression has an antiderivative
expression whose formal derivative is its denotation. -/
theorem integrateAst_complete [IsAlgClosed R] (e : Expr R) :
    ∃ I : IntegralExpr R, I.deriv = e.eval :=
  ⟨integrateAst e, integrateAst_sound e⟩

end Expr

end DeepWiki.CAlgebra
