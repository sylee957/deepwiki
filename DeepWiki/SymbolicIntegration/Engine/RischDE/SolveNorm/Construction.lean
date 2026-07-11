import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerGcdWitnessWf
import DeepWiki.SymbolicIntegration.Engine.RischDE.Structural

/-! # Weak-normalization constructions for Risch-DE solving

Computable helpers and the normality predicate used by the weak-normalized solver. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac GBPolyCore

section Helpers

variable {β : Type*} [CField β] [CDiffField β] [CFieldDomain β DensePoly]

/-- `weakNormalizedF f q' = f − Dq'/q'` over `DenseFrac β`: the weakly-normalized field element. -/
def weakNormalizedF (f q' : DenseFrac β) : DenseFrac β :=
  sub f (mul (towerDerivCFrac ([CCommRing.one] : DensePoly β) q') (inv q'))

end Helpers

section Normality

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β]
  [CPolySplitFactor DensePoly β]

/-- `IsWeaklyNormalizedNorm h`: `h`'s denominator equals its selected differential normal part. -/
def IsWeaklyNormalizedNorm (h : DenseFrac β) : Prop :=
  CPoly.toPoly (CPoly.splitFactor (CPoly.one : DensePoly β) h.den).1 = CPoly.toPoly h.den

end Normality

end DeepWiki.SymbolicIntegration
