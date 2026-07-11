import DeepWiki.ComputableAlgebra.PolyInterpolateDense
import DeepWiki.ComputableAlgebra.PolyEngineSparse

/-! # Sparse polynomial interpolation

Sparse polynomials select the shared coefficient-list Lagrange computation and store its result through
the sparse representation's lawful coefficient-list constructor. -/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Sparse polynomials select interpolation followed by sparse coefficient storage. -/
instance instCPolyInterpolateSparse : CPolyInterpolate CPoly.SparsePoly where
  compute pts := CPolyEngine.ofCoeffList (DensePoly.cinterpolate pts)

namespace CPoly

/-- A sparse selected interpolant denotes the same polynomial as the coefficient-list computation. -/
@[denote] theorem toPoly_interpolate_sparse {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (pts : List (α × α)) :
    toPoly (interpolate (P := CPoly.SparsePoly) pts) =
      DensePoly.toPoly (DensePoly.cinterpolate pts) := by
  rw [interpolate]
  change toPoly (CPolyEngine.ofCoeffList (P := CPoly.SparsePoly)
    (DensePoly.cinterpolate pts)) = _
  rw [LawfulCPolyEngine.toPoly_ofCoeffList]
  exact CPoly.toPoly_ofList_eq_dense _

end CPoly

/-- Sparse selected interpolation satisfies the abstract interpolation laws. -/
instance instLawfulCPolyInterpolateSparse : LawfulCPolyInterpolate CPoly.SparsePoly where
  eval_compute := by
    intro α _ _ pts hnodup zk yk hmem
    change (CPoly.toPoly (CPoly.interpolate (P := CPoly.SparsePoly) pts)).eval
      (CFieldSpec.toK zk) = CFieldSpec.toK yk
    rw [CPoly.toPoly_interpolate_sparse]
    exact DensePoly.eval_toPolyG_cinterpolateG pts hnodup hmem
  degree_compute_lt := by
    intro α _ _ pts hne
    change (CPoly.toPoly (CPoly.interpolate (P := CPoly.SparsePoly) pts)).degree <
      (pts.length : WithBot ℕ)
    rw [CPoly.toPoly_interpolate_sparse]
    exact DensePoly.degree_toPolyG_cinterpolateG_lt pts hne

/-- Sparse selected interpolation computes `1 + 2X` through the abstract capability. -/
theorem interpolate_sparse_linear :
    CPoly.interpolate (P := CPoly.SparsePoly) ([(0, 1), (1, 3)] : List (ℚ × ℚ)) =
      CPoly.SparsePoly.ofList [(0, 1), (1, 2)] := by
  ccompute

end DeepWiki.SymbolicIntegration
