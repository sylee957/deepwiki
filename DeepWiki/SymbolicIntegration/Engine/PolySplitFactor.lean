import DeepWiki.ComputableAlgebra.PolyGcdAlgorithms
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.SplitFactor

/-! # Representation-independent differential split factorization

The normal/special polynomial split composes the selected gcd and Euclidean algorithms with the
representation-independent monomial derivative.
-/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Executable differential split factorization selected for a polynomial representation and coefficient field. -/
class CPolySplitFactor (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Split a polynomial into its differential normal and special factors. -/
  compute : P α → P α → P α × P α

namespace CPolySplitFactor

/-- Internal bounded driver for differential normal/special factorization. -/
private def splitFactorAux {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P] [CDiffField α]
    (Dt : P α) : ℕ → P α → P α × P α
  | 0, p => (p, CPoly.one)
  | fuel + 1, p =>
    let implicitGcd := CPolyGcd.compute p (CPolyEngine.monomialDeriv Dt p)
    let formalGcd := CPolyGcd.compute p (CPolyEngine.deriv p)
    let special := CPolyEuclidean.div implicitGcd formalGcd
    if CPolyEngine.cdeg special = 0 then (p, CPoly.one)
    else
      let quotient := CPolyEuclidean.div p special
      if CPolyEngine.cdeg quotient < CPolyEngine.cdeg p then
        let parts := splitFactorAux Dt fuel quotient
        (parts.1, CPolyEngine.mul special parts.2)
      else (p, CPoly.one)

/-- Generic bounded differential split factorization through selected gcd and Euclidean operations. -/
def default {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P] [CDiffField α]
    (Dt p : P α) : P α × P α :=
  splitFactorAux Dt (CPoly.degBound p) p

end CPolySplitFactor

/-- Sparse polynomials select the representation-generic bounded split-factor kernel. -/
instance instCPolySplitFactorSparse {α : Type u} [CField α] [CDiffField α] :
    CPolySplitFactor CPoly.SparsePoly α where
  compute := CPolySplitFactor.default

namespace CPoly

/-- Split a represented differential polynomial using its selected implementation. -/
def splitFactor {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] [CPolySplitFactor P α]
    (Dt p : P α) : P α × P α :=
  CPolySplitFactor.compute Dt p

/-- Sparse splitting with the zero derivation extracts `(x - 1)²` as entirely special. -/
example :
    let p : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, 1), (1, -2), (2, 1)]
    let parts := splitFactor (CPoly.czero : CPoly.SparsePoly ℚ) p
    CPolyEngine.cdeg parts.1 = 0
      ∧ CPolyEngine.cisZero
          (CPolyEngine.sub (CPolyEngine.mul parts.1 parts.2) p) = true := by
  ccompute

end CPoly

/-- Denotation law for a selected differential split factorization. -/
class LawfulCPolySplitFactor (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] [CFieldSpec.{u,v} α] [CDiffFieldSpec α]
    [CharZero (CFieldSpec.K α)] [CPolySplitFactor P α] : Prop where
  /-- The selected split is a normal/special splitting factorization of every nonzero input. -/
  compute_isSplittingFactorizationGen : ∀ (Dt p : P α), CPoly.toPoly p ≠ 0 →
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly p) (CPoly.toPoly (CPoly.splitFactor Dt p).2)
        (CPoly.toPoly (CPoly.splitFactor Dt p).1)

namespace LawfulCPolySplitFactor

/-- The selected split-factorization operation satisfies its denotation law. -/
theorem compute_isSplittingFactorizationGen' {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] [CFieldSpec.{u,v} α] [CDiffFieldSpec α]
    [CharZero (CFieldSpec.K α)] [CPolySplitFactor P α] [LawfulCPolySplitFactor P α]
    (Dt p : P α) (hp : CPoly.toPoly p ≠ 0) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly p) (CPoly.toPoly (CPoly.splitFactor Dt p).2)
        (CPoly.toPoly (CPoly.splitFactor Dt p).1) :=
  LawfulCPolySplitFactor.compute_isSplittingFactorizationGen Dt p hp

end LawfulCPolySplitFactor

end DeepWiki.SymbolicIntegration
