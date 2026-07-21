import DeepWiki.CAlgebra.Integrate.DerivDataSpec

/-! # The integral output syntax

An abstract syntax tree for antiderivative expressions — rational terms and `RootSum`
logarithms — with its formal-derivative denotation, and the computable rendering of a
`ResultRatIntegral` record into it. Rendering preserves the derivative semantics. -/

namespace DeepWiki.CAlgebra

universe u

/-- Syntax of antiderivative expressions: rational-function terms, `RootSum` log terms
`∑_{Q(α)=0} α · log S(α, x)`, and sums. -/
inductive IntegralExpr (R : Type u) [Field R] [DecidableEq R] where
  /-- A rational-function term. -/
  | frac (f : DenseFrac R)
  /-- A `RootSum` logarithm class: `∑_{Q(α)=0} α · log S(α, x)`. -/
  | rootSum (Q : DensePoly R) (S : DensePoly (DensePoly R))
  /-- A scalar multiple of a logarithm: `a · log u`. -/
  | smulLog (a : R) (u : DensePoly R)
  /-- A sum of antiderivative terms. -/
  | add (a b : IntegralExpr R)

namespace IntegralExpr

open DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R] [DensePolyGcd R]
  [DensePolySquarefree R] [IsAlgClosed R]

open scoped Differential FormalDiff in
/-- The formal-derivative denotation of an antiderivative expression: rational terms
derive computably (then denote), `RootSum` terms read as their pair log-derivative. -/
noncomputable def deriv : IntegralExpr R → RatFunc R
  | frac f => DenseFrac.toRatFunc (f′)
  | rootSum Q S => lrtPairTerm (Q, S)
  | smulLog a u =>
      algebraMap (Polynomial R) (RatFunc R) (Polynomial.C a)
        * @Differential.logDeriv (RatFunc R) _
            SymbolicIntegration.instDifferentialRatFunc_deepWiki
            (algebraMap (Polynomial R) (RatFunc R) (toPolynomial u))
  | add a b => a.deriv + b.deriv

end IntegralExpr

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R] [DensePolyGcd R]
  [DensePolySquarefree R] [IsAlgClosed R]

omit [CharZero R] [DensePolyGcd R] [DensePolySquarefree R] [IsAlgClosed R] in
/-- Render a rational-integral record as an antiderivative expression:
`rational + ∫poly + ∑ᵢ RootSum(Qᵢ, Sᵢ)`. -/
def ResultRatIntegral.toExpr (res : ResultRatIntegral R) : IntegralExpr R :=
  res.logs.terms.foldr (fun QS acc => .add (.rootSum QS.1 QS.2) acc)
    (.add (.frac res.rational) (.frac (DenseFrac.ofPoly res.poly)))

omit [DensePolySquarefree R] in
open scoped Differential FormalDiff in
/-- **Rendering preserves the derivative semantics**: the output expression's formal
derivative reads the record's computable derivative, given the log-data nonvanishing
contract. -/
theorem ResultRatIntegral.toExpr_deriv (res : ResultRatIntegral R)
    (hS : ∀ QS ∈ res.logs.terms, ∀ α ∈ (toPolynomial QS.1).roots,
      (toPolynomial₂ QS.2).map (Polynomial.evalRingHom α) ≠ 0) :
    res.toExpr.deriv = DenseFrac.toRatFunc res.deriv := by
  rw [ResultRatIntegral.toRatFunc_deriv res hS]
  have hfold : ∀ (L : List (DensePoly R × DensePoly (DensePoly R)))
      (base : IntegralExpr R),
      (L.foldr (fun QS acc => .add (.rootSum QS.1 QS.2) acc) base).deriv
        = (L.map lrtPairTerm).sum + base.deriv := by
    intro L
    induction L with
    | nil => intro base; rw [List.foldr_nil, List.map_nil, List.sum_nil, zero_add]
    | cons QS T ih =>
        intro base
        simp only [List.foldr_cons, IntegralExpr.deriv, List.map_cons, List.sum_cons,
          ih, Prod.mk.eta]
        ring
  rw [ResultRatIntegral.toExpr, hfold]
  simp only [IntegralExpr.deriv]
  have hpoly : DenseFrac.toRatFunc ((DenseFrac.ofPoly res.poly)′)
      = toRatFuncHom (res.poly′) := by
    rw [DenseFrac.toRatFunc_deriv, DenseFrac.toRatFunc_ofPoly, ← toRatFuncHom_apply,
      toRatFuncHom_deriv]
  rw [hpoly]
  show _ = DenseFrac.toRatFunc (res.rational′) + toRatFuncHom (res.poly′)
      + (res.logs.terms.map lrtPairTerm).sum
  ring

end DensePoly

end DeepWiki.CAlgebra
