import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerGcdWitnessWf
import DeepWiki.SymbolicIntegration.Engine.RischDE.Structural

/-! # Weak-normalization constructions for Risch-DE solving

Computable helpers and the normality predicate used by the weak-normalized solver. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac GBPolyCore

section Helpers

variable {β : Type*} [CField β] [CDiffField β] [CFieldDomain β]

/-- `weakNormalizedF f q' = f − Dq'/q'` over `DenseFrac β`: the weakly-normalized field element. -/
def weakNormalizedF (f q' : DenseFrac β) : DenseFrac β :=
  qsubNZ f (qmulNZ (towerDerivCFrac ([CCommRing.one] : DensePoly β) q') (qinvNZ q'))

end Helpers

section Reduce

variable {β : Type*} [CField β] [CFieldSpec β]

/-- A `[CField β]`-data lowest-terms reducer that rebuilds the `qReduce` representative. -/
def reduceSoundOpt (a : DenseFrac β) : Option (DenseFrac β) :=
  let rd := CFrac.reduceDen a
  if h : DensePoly.cisZero rd = false then some (CFrac.ofFraction (CFrac.reduceNum a) rd h) else none

/-- `reduceSoundOpt a` is exactly `some (qReduce a)`. -/
theorem reduceSoundOpt_eq (a : DenseFrac β) : reduceSoundOpt a = some (qReduce a) := by
  unfold reduceSoundOpt qReduce
  rw [dif_pos (CFrac.cisZeroG_reduceDen a)]

end Reduce

section Normality

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- `IsWeaklyNormalizedNorm h`: `h`'s denominator equals its own normal part
`toPoly (cSplitFactorFast [1] _ h.den).1 = toPoly h.den`. -/
def IsWeaklyNormalizedNorm (h : DenseFrac β) : Prop :=
  toPoly (DensePoly.cSplitFactorFast ([CCommRing.one] : DensePoly β) h.den).1
    = toPoly h.den

end Normality

end DeepWiki.SymbolicIntegration
