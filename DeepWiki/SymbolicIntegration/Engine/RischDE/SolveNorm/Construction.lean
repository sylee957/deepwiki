import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerGcdWitnessWf
import DeepWiki.SymbolicIntegration.Engine.RischDE.Structural

/-! # Weak-normalization constructions for Risch-DE solving

Computable helpers and the normality predicate used by the weak-normalized solver. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

section Lift

variable {β : Type*} [CField β] [CFieldDomain β]

/-- `qOfPolyNZG q`: lift a polynomial `q : CPolyG β` to `QFunNZG β` as `q/1`. -/
def qOfPolyNZG (q : CPolyG β) : QFunNZG β :=
  ⟨(q, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

end Lift

section Helpers

variable {β : Type*} [CField β] [CDiffField β] [CFieldDomain β]

/-- `weakNormalizedF f q' = f − Dq'/q'` over `QFunNZG β`: the weakly-normalized field element. -/
def weakNormalizedF (f q' : QFunNZG β) : QFunNZG β :=
  qsubNZG f (qmulNZG (towerDerivQFunNZG ([CField.one] : CPolyG β) q') (qinvNZG q'))

end Helpers

section Reduce

variable {β : Type*} [CField β] [CFieldSpec β]

/-- A `[CField β]`-data lowest-terms reducer that rebuilds the `qReduce` representative. -/
def reduceSoundOpt (a : QFunNZG β) : Option (QFunNZG β) :=
  let rd := QFunNZG.reduceDen a
  if h : CPolyG.cisZeroG rd = false then some ⟨(QFunNZG.reduceNum a, rd), h⟩ else none

/-- `reduceSoundOpt a` is exactly `some (qReduce a)`. -/
theorem reduceSoundOpt_eq (a : QFunNZG β) : reduceSoundOpt a = some (qReduce a) := by
  unfold reduceSoundOpt qReduce
  rw [dif_pos (QFunNZG.cisZeroG_reduceDen a)]

end Reduce

section Normality

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- `IsWeaklyNormalizedNorm h`: `h`'s denominator equals its own normal part
`toPolyG (cSplitFactorFastG [1] _ h.1.2).1 = toPolyG h.1.2`. -/
def IsWeaklyNormalizedNorm (h : QFunNZG β) : Prop :=
  toPolyG (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) h.1.2).1
    = toPolyG h.1.2

end Normality

end DeepWiki.SymbolicIntegration
