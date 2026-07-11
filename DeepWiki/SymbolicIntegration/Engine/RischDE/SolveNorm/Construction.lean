import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerGcdUnit
import DeepWiki.SymbolicIntegration.Engine.RischDE.Structural

/-! # Weak-normalization constructions for Risch-DE solving

Computable helpers and the normality predicate used by the weak-normalized solver. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac GBPolyCore

universe u

section Helpers

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {F : (α : Type u) → [CField α] → Type u} [CFrac F P]
variable {β : Type u} [CField β] [CDiffField β] [CFieldDomain β P]

/-- `weakNormalizedF f q' = f − Dq'/q'` for a represented fraction field. -/
def weakNormalizedF (f q' : F β) : F β :=
  sub f (mul (CFrac.towerDerivCFracWith (CPoly.one : P β) q') (inv q'))

end Helpers

section Normality

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {F : (α : Type u) → [CField α] → Type u} [CFrac F P]
variable {β : Type u} [CField β] [CFieldSpec β] [CDiffField β] [CPolySplitFactor P β]

/-- `IsWeaklyNormalizedNorm h`: `h`'s denominator equals its selected differential normal part. -/
def IsWeaklyNormalizedNorm (h : F β) : Prop :=
  CPoly.toPoly (CPoly.splitFactor (CPoly.one : P β) (CFrac.den h)).1 = CPoly.toPoly (CFrac.den h)

end Normality

example :
    let one : SparseFrac ℚ := CFrac.ofPoly (CPoly.one : CPoly.SparsePoly ℚ)
    CCommRing.isZero (CField.sub (weakNormalizedF one one) one) = true := by
  ccompute

end DeepWiki.SymbolicIntegration
