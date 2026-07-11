import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree
import DeepWiki.ComputableAlgebra.PolyReprDense

/-! # Representation-independent polynomial gcd capability

`CPolyGcd` separates the executable gcd operation from consumers such as fraction reduction. The default
instance uses the generic Euclidean algorithm on `CPoly`; `LawfulCPolyGcd` carries its denotation-level gcd
law so a representation-specific implementation can replace it without changing callers. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Executable polynomial gcd selected by a polynomial representation and coefficient field. -/
class CPolyGcd (P : Type u → Type u) [CPoly P] (α : Type u) [CField α] where
  /-- Compute a greatest common divisor of two represented polynomials. -/
  compute : P α → P α → P α

namespace CPolyGcd

/-- The selected gcd operation as a first-class binary function. -/
def computeFn {P : Type u → Type u} [CPoly P] {α : Type u} [CField α] [CPolyGcd P α] :
    P α → P α → P α :=
  fun p q => CPolyGcd.compute p q

/-- Applying the first-class selected gcd is `CPolyGcd.compute`. -/
@[simp] theorem computeFn_apply {P : Type u → Type u} [CPoly P]
    {α : Type u} [CField α] [CPolyGcd P α] (p q : P α) :
    CPolyGcd.computeFn p q = CPolyGcd.compute p q := rfl

end CPolyGcd

/-- Denotation-level gcd law for an executable polynomial gcd. -/
class LawfulCPolyGcd (P : Type u → Type u) [CPoly P] (α : Type u) [CField α]
    [CPolyGcd P α] : Prop where
  /-- The computed gcd divides both inputs and every common divisor divides it. -/
  compute_isGCD : ∀ [CFieldSpec.{u,v} α] (p q : P α),
    CPoly.toPoly (CPolyGcd.compute p q) ∣ CPoly.toPoly p ∧
      CPoly.toPoly (CPolyGcd.compute p q) ∣ CPoly.toPoly q ∧
        ∀ d : (CFieldSpec.K α)[X], d ∣ CPoly.toPoly p → d ∣ CPoly.toPoly q →
          d ∣ CPoly.toPoly (CPolyGcd.compute p q)

/-! ### Built-in dense and sparse instances -/

/-- The generic Euclidean gcd supplies the default dense executable capability. -/
instance (priority := low) instCPolyGcdDense {α : Type u} [CField α] :
    CPolyGcd DensePoly α where
  compute := CPoly.cgcd

/-- The dense Euclidean gcd satisfies the lawful gcd interface. -/
instance (priority := low) instLawfulCPolyGcdDense {α : Type u} [CField α] :
    LawfulCPolyGcd.{u,v} DensePoly α where
  compute_isGCD := by
    intro _ p q
    exact CPoly.cgcd_isGCD p q

/-- The generic Euclidean gcd supplies the sparse executable capability. -/
instance instCPolyGcdSparse {α : Type u} [CField α] : CPolyGcd CPoly.SparsePoly α where
  compute := CPoly.cgcd

/-- The sparse Euclidean gcd satisfies the lawful gcd interface. -/
instance instLawfulCPolyGcdSparse {α : Type u} [CField α] :
    LawfulCPolyGcd.{u,v} CPoly.SparsePoly α where
  compute_isGCD := by
    intro _ p q
    exact CPoly.cgcd_isGCD p q

variable {P : Type u → Type u} [CPoly P] {α : Type u} [CField α]
  [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]

namespace LawfulCPolyGcd

/-- Universe-explicit projection of the lawful gcd law for a coefficient field. -/
theorem compute_isGCD' [CFieldSpec.{u,v} α] (p q : P α) :
    CPoly.toPoly (CPolyGcd.compute p q) ∣ CPoly.toPoly p ∧
      CPoly.toPoly (CPolyGcd.compute p q) ∣ CPoly.toPoly q ∧
        ∀ d : (CFieldSpec.K α)[X], d ∣ CPoly.toPoly p → d ∣ CPoly.toPoly q →
          d ∣ CPoly.toPoly (CPolyGcd.compute p q) := by
  exact @LawfulCPolyGcd.compute_isGCD P inferInstance α inferInstance inferInstance inferInstance
    (inferInstance : CFieldSpec.{u,v} α) p q

/-- The selected gcd of `1` and any represented polynomial denotes a unit. -/
theorem compute_one_isUnit [CFieldSpec.{u,v} α] (p : P α) :
    IsUnit (CPoly.toPoly (CPolyGcd.compute (CPoly.one : P α) p)) := by
  have hdvd := (compute_isGCD' (CPoly.one : P α) p).1
  rw [CPoly.toPoly_one] at hdvd
  exact isUnit_iff_dvd_one.mpr hdvd

end LawfulCPolyGcd

end DeepWiki.SymbolicIntegration
