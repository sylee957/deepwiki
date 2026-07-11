import DeepWiki.ComputableAlgebra.FracRepr
import DeepWiki.ComputableAlgebra.PolyEngineDense

/-! # Dense computable-fraction representation

`DenseFrac α` is the proof-carrying `CFrac` specialization whose numerator and denominator use
`DensePoly α`. Its constructor is private so consumers pass through the representation interface. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Fractions represented by a dense numerator and certified-nonzero dense denominator. -/
structure DenseFrac (α : Type u) [CField α] where
  private mk ::
  /-- Implementation storage for the represented numerator-denominator pair. -/
  private toPair : DensePoly α × DensePoly α
  /-- The stored dense denominator passes the executable nonzero test. -/
  private den_nonzero : CPolyEngine.cisZero toPair.2 = false

/-- `DenseFrac` implements `CFrac` through its private pair storage. -/
instance instCFracDenseFrac : CFrac DenseFrac DensePoly where
  toPair x := x.toPair
  ofPair num den h := ⟨(num, den), h⟩
  toPair_ofPair _ _ _ := rfl
  den_nonzero_impl x := x.den_nonzero

/-- Dot-notation access to the dense numerator through the `CFrac` interface. -/
protected abbrev DenseFrac.num {α : Type u} [CField α] (x : DenseFrac α) : DensePoly α :=
  CFrac.num x

/-- Dot-notation access to the dense denominator through the `CFrac` interface. -/
protected abbrev DenseFrac.den {α : Type u} [CField α] (x : DenseFrac α) : DensePoly α :=
  CFrac.den x

end DeepWiki.SymbolicIntegration
