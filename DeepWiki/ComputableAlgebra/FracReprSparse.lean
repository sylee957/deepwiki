import DeepWiki.ComputableAlgebra.FracRepr
import DeepWiki.ComputableAlgebra.PolyEngineSparse

/-! # Sparse computable-fraction representation

`SparseFrac α` is the proof-carrying `CFrac` specialization whose numerator and denominator use
`CPoly.SparsePoly α`. Its constructor is private so consumers pass through the representation interface. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Fractions represented by a sparse numerator and certified-nonzero sparse denominator. -/
structure SparseFrac (α : Type u) [CField α] where
  private mk ::
  /-- Implementation storage for the represented numerator-denominator pair. -/
  private toPair : CPoly.SparsePoly α × CPoly.SparsePoly α
  /-- The stored sparse denominator passes the executable nonzero test. -/
  private den_nonzero : CPolyEngine.cisZero toPair.2 = false

/-- `SparseFrac` implements `CFrac` through its private pair storage. -/
instance instCFracSparseFrac : CFrac SparseFrac CPoly.SparsePoly where
  toPair x := x.toPair
  ofPair num den h := ⟨(num, den), h⟩
  toPair_ofPair _ _ _ := rfl
  den_nonzero_impl x := x.den_nonzero

/-- Dot-notation access to the sparse numerator through the `CFrac` interface. -/
protected abbrev SparseFrac.num {α : Type u} [CField α] (x : SparseFrac α) : CPoly.SparsePoly α :=
  CFrac.num x

/-- Dot-notation access to the sparse denominator through the `CFrac` interface. -/
protected abbrev SparseFrac.den {α : Type u} [CField α] (x : SparseFrac α) : CPoly.SparsePoly α :=
  CFrac.den x

end DeepWiki.SymbolicIntegration
