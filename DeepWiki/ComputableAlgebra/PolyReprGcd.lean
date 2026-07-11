import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree
import DeepWiki.ComputableAlgebra.PolyReprDense

/-! # Representation-independent polynomial gcd capability

`CPolyGcd` separates the executable gcd operation from consumers such as fraction reduction. The default
instance uses the generic Euclidean algorithm on `CPoly`; `LawfulCPolyGcd` carries its denotation-level gcd
law so a representation-specific implementation can replace it without changing callers. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Executable polynomial gcd over a representation-independent `CPoly`. -/
class CPolyGcd (P : Type u → Type u) [CPoly P] where
  /-- Compute a greatest common divisor of two represented polynomials. -/
  compute : {α : Type u} → [CField α] → P α → P α → P α

/-- Denotation-level gcd law for an executable polynomial gcd. -/
class LawfulCPolyGcd (P : Type u → Type u) [CPoly P] [CPolyGcd P] : Prop where
  /-- The computed gcd divides both inputs and every common divisor divides it. -/
  compute_isGCD : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q : P α),
    CPoly.toPoly (CPolyGcd.compute p q) ∣ CPoly.toPoly p ∧
      CPoly.toPoly (CPolyGcd.compute p q) ∣ CPoly.toPoly q ∧
        ∀ d : (CFieldSpec.K α)[X], d ∣ CPoly.toPoly p → d ∣ CPoly.toPoly q →
          d ∣ CPoly.toPoly (CPolyGcd.compute p q)

/-! ### Built-in dense and sparse instances -/

/-- The generic Euclidean gcd supplies the dense executable capability. -/
instance instCPolyGcdDense : CPolyGcd DensePoly where
  compute := CPoly.cgcd

/-- The dense Euclidean gcd satisfies the lawful gcd interface. -/
instance instLawfulCPolyGcdDense : LawfulCPolyGcd DensePoly where
  compute_isGCD := by
    intro α _ _ p q
    exact CPoly.cgcd_isGCD p q

/-- The generic Euclidean gcd supplies the sparse executable capability. -/
instance instCPolyGcdSparse : CPolyGcd CPoly.SparsePoly where
  compute := CPoly.cgcd

/-- The sparse Euclidean gcd satisfies the lawful gcd interface. -/
instance instLawfulCPolyGcdSparse : LawfulCPolyGcd CPoly.SparsePoly where
  compute_isGCD := by
    intro α _ _ p q
    exact CPoly.cgcd_isGCD p q

variable {P : Type u → Type u} [CPoly P] [CPolyGcd P] [LawfulCPolyGcd.{u,v} P]

namespace LawfulCPolyGcd

/-- Universe-explicit projection of the lawful gcd law for a coefficient field. -/
theorem compute_isGCD' {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (p q : P α) :
    CPoly.toPoly (CPolyGcd.compute p q) ∣ CPoly.toPoly p ∧
      CPoly.toPoly (CPolyGcd.compute p q) ∣ CPoly.toPoly q ∧
        ∀ d : (CFieldSpec.K α)[X], d ∣ CPoly.toPoly p → d ∣ CPoly.toPoly q →
          d ∣ CPoly.toPoly (CPolyGcd.compute p q) := by
  exact @LawfulCPolyGcd.compute_isGCD P inferInstance inferInstance inferInstance α inferInstance
    (inferInstance : CFieldSpec.{u,v} α) p q

end LawfulCPolyGcd

end DeepWiki.SymbolicIntegration
