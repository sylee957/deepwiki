import DeepWiki.ComputableAlgebra.PolyInterpolate
import DeepWiki.ComputableAlgebra.PolyEngineSparse

/-! # Sparse polynomial interpolation

Sparse polynomials run the representation-generic Lagrange kernel directly through their selected
polynomial engine. -/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Sparse polynomials select the representation-generic interpolation kernel. -/
instance instCPolyInterpolateSparse : CPolyInterpolate CPoly.SparsePoly where
  compute := CPolyInterpolate.default

namespace CPoly

/-- Sparse selected interpolation unfolds to the representation-generic kernel. -/
@[simp] theorem interpolate_sparse_eq {α : Type u} [CField α] (pts : List (α × α)) :
    interpolate (P := CPoly.SparsePoly) pts =
      CPolyInterpolate.default (P := CPoly.SparsePoly) pts := rfl

end CPoly

/-- Sparse selected interpolation satisfies the abstract interpolation laws. -/
instance instLawfulCPolyInterpolateSparse : LawfulCPolyInterpolate CPoly.SparsePoly where
  eval_compute := by
    intro α _ _ pts hnodup zk yk hmem
    change (CPoly.toPoly (CPoly.interpolate (P := CPoly.SparsePoly) pts)).eval
      (CFieldSpec.toK zk) = CFieldSpec.toK yk
    rw [CPoly.interpolate_sparse_eq]
    exact CPolyInterpolate.eval_toPoly_default pts hnodup hmem
  degree_compute_lt := by
    intro α _ _ pts hne
    change (CPoly.toPoly (CPoly.interpolate (P := CPoly.SparsePoly) pts)).degree <
      (pts.length : WithBot ℕ)
    rw [CPoly.interpolate_sparse_eq]
    exact CPolyInterpolate.degree_toPoly_default_lt pts hne

end DeepWiki.SymbolicIntegration
