import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerGcdWitnessWf
import DeepWiki.SymbolicIntegration.Engine.RischDE.Structural

/-! # Weak-normalization constructions for Risch-DE solving

Computable helpers and the normality predicate used by the weak-normalized solver. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZ GBPolyCore

section Lift

variable {β : Type*} [CField β] [CFieldDomain β]

/-- `qOfPolyNZ q`: lift a polynomial `q : CPoly β` to `QFunNZ β` as `q/1`. -/
def qOfPolyNZ (q : CPoly β) : QFunNZ β :=
  ⟨(q, [CField.one]), QFunNZ.cisZeroG_one_singleton⟩

end Lift

section Helpers

variable {β : Type*} [CField β] [CDiffField β] [CFieldDomain β]

/-- `weakNormalizedF f q' = f − Dq'/q'` over `QFunNZ β`: the weakly-normalized field element. -/
def weakNormalizedF (f q' : QFunNZ β) : QFunNZ β :=
  qsubNZ f (qmulNZ (towerDerivQFunNZ ([CField.one] : CPoly β) q') (qinvNZ q'))

end Helpers

section Reduce

variable {β : Type*} [CField β] [CFieldSpec β]

/-- A `[CField β]`-data lowest-terms reducer that rebuilds the `qReduce` representative. -/
def reduceSoundOpt (a : QFunNZ β) : Option (QFunNZ β) :=
  let rd := QFunNZ.reduceDen a
  if h : CPoly.cisZero rd = false then some ⟨(QFunNZ.reduceNum a, rd), h⟩ else none

/-- `reduceSoundOpt a` is exactly `some (qReduce a)`. -/
theorem reduceSoundOpt_eq (a : QFunNZ β) : reduceSoundOpt a = some (qReduce a) := by
  unfold reduceSoundOpt qReduce
  rw [dif_pos (QFunNZ.cisZeroG_reduceDen a)]

end Reduce

section Normality

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- `IsWeaklyNormalizedNorm h`: `h`'s denominator equals its own normal part
`toPoly (cSplitFactorFast [1] _ h.1.2).1 = toPoly h.1.2`. -/
def IsWeaklyNormalizedNorm (h : QFunNZ β) : Prop :=
  toPoly (CPoly.cSplitFactorFast ([CField.one] : CPoly β) h.1.2).1
    = toPoly h.1.2

end Normality

end DeepWiki.SymbolicIntegration
