import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree
import DeepWiki.ComputableAlgebra.PolyReprSparse

/-! # Abstract executable polynomial Euclidean algorithms

`CPolyEuclidean` selects division and extended-gcd implementations for a polynomial representation.
`LawfulCPolyEuclidean` records their denotation-level Euclidean and Bézout laws; plain gcd selection is
the separate `CPolyGcd` capability. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Representation-selected executable Euclidean algorithms for computable polynomials. -/
class CPolyEuclidean (P : Type u → Type u) [CPoly P] where
  /-- Polynomial quotient and remainder. -/
  divmod : {α : Type u} → [CField α] → P α → P α → P α × P α
  /-- Extended gcd `(g, s, t)` with Bézout coefficients. -/
  gcdExt : {α : Type u} → [CField α] → P α → P α → P α × P α × P α

namespace CPolyEuclidean

variable {P : Type u → Type u} [CPoly P] [CPolyEuclidean P]

/-- Polynomial quotient selected by `CPolyEuclidean`. -/
def div {α : Type u} [CField α] (p q : P α) : P α := (CPolyEuclidean.divmod p q).1

/-- Polynomial remainder selected by `CPolyEuclidean`. -/
def mod {α : Type u} [CField α] (p q : P α) : P α := (CPolyEuclidean.divmod p q).2

end CPolyEuclidean

/-- Denotation laws for representation-selected polynomial Euclidean algorithms. -/
class LawfulCPolyEuclidean (P : Type u → Type u) [CPoly P] [CPolyEuclidean P] : Prop where
  /-- Quotient and remainder satisfy the Euclidean identity for a nonzero divisor. -/
  divmod_spec : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q : P α),
    CPoly.toPoly q ≠ 0 →
      CPoly.toPoly p = CPoly.toPoly (CPolyEuclidean.div p q) * CPoly.toPoly q +
        CPoly.toPoly (CPolyEuclidean.mod p q)
  /-- Exact division reconstructs the dividend when the selected divisor divides it. -/
  div_exact : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q : P α),
    CPoly.toPoly q ≠ 0 → CPoly.toPoly q ∣ CPoly.toPoly p →
      CPoly.toPoly p = CPoly.toPoly q * CPoly.toPoly (CPolyEuclidean.div p q)
  /-- The selected extended gcd satisfies its Bézout identity. -/
  gcdExt_bezout : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q : P α),
    CPoly.toPoly (CPolyEuclidean.gcdExt p q).2.1 * CPoly.toPoly p +
        CPoly.toPoly (CPolyEuclidean.gcdExt p q).2.2 * CPoly.toPoly q =
      CPoly.toPoly (CPolyEuclidean.gcdExt p q).1

/-- Sparse polynomials use the representation-generic Euclidean algorithms. -/
instance instCPolyEuclideanSparse : CPolyEuclidean CPoly.SparsePoly where
  divmod := CPoly.cdivmod
  gcdExt := CPoly.cgcdExt

/-- The generic sparse Euclidean implementation satisfies the abstract laws. -/
instance instLawfulCPolyEuclideanSparse : LawfulCPolyEuclidean CPoly.SparsePoly where
  divmod_spec := by
    intro α _ _ p q _
    change CPoly.toPoly p = CPoly.toPoly (CPoly.cdivmod p q).1 * CPoly.toPoly q +
      CPoly.toPoly (CPoly.cdivmod p q).2
    simpa [mul_comm] using CPoly.toPoly_cdivmod p q
  div_exact := by
    intro α _ _ p q hq hdvd
    have hqz : ¬ CPoly.cisZero q = true := fun hz => hq ((CPoly.cisZero_iff q).mp hz)
    change CPoly.toPoly p = CPoly.toPoly q * CPoly.toPoly (CPoly.cdivmod p q).1
    exact CPoly.toPoly_mul_cdiv_of_dvd p q hqz hdvd
  gcdExt_bezout := CPoly.toPoly_cgcdExt

end DeepWiki.SymbolicIntegration
