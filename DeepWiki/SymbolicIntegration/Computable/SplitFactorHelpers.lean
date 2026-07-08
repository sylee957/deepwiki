import DeepWiki.SymbolicIntegration.Computable.ConcreteCoherence
import DeepWiki.SymbolicIntegration.CanonicalRepresentation

/-! # Generic associate helper for splitting factorization
Generic associate helper for splitting factorization: degree is associate-invariant. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-- `Associated a b → a.natDegree = b.natDegree` in `K[X]`: degree is associate-invariant. -/
theorem natDegree_eq_of_associated {K : Type*} [Field K] {a b : K[X]} (h : Associated a b) :
    a.natDegree = b.natDegree :=
  Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated h)

end DeepWiki.SymbolicIntegration
