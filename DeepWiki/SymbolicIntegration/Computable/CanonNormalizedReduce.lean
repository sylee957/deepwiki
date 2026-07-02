import DeepWiki.SymbolicIntegration.Computable.RischDE.SolveNorm
import DeepWiki.SymbolicIntegration.ComputableTowerRischDEWellFounded

/-! # The fuel-free §6.1 normality check is `qReduce`-invariant

This file records the Wf canonical-normality gate used by the fuel-free RDE solver.
The denominator-direct gate on `qReduce x` is definitionally the wrapper gate on `x`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

section CoreWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- The fuel-free denominator-direct canonical-normality check. -/
def cisCanonNormalizedCoreGWf (a : QFunNZG β) : Bool :=
  cdenomNormalGateGWf a

/-- The fuel-free wrapper canonical-normality check on the reduced denominator. -/
def cisCanonNormalizedGWf (ftilde : QFunNZG β) : Bool :=
  CPolyG.cisZeroG (CPolyG.csubG
    (CPolyG.cSplitFactorFastGWf ([CField.one] : CPolyG β)
      (QFunNZG.reduceDen ftilde)).1
    (QFunNZG.reduceDen ftilde))

end CoreWf

/-! ## The Wf keystone bridge -/

section Bridge

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- The fuel-free core check on `qReduce x` is the fuel-free wrapper check on `x`. -/
theorem cisCanonNormalizedCoreGWf_qReduce (x : QFunNZG β) :
    cisCanonNormalizedCoreGWf (qReduce x) = cisCanonNormalizedGWf x := rfl

example (x : QFunNZG β) : cisCanonNormalizedCoreGWf (qReduce x) = cisCanonNormalizedGWf x := rfl

end Bridge

/-! ## Fuel-free canonical-normality propositions

The Wf propositions are the fuel-free normality gates: they read the normal part through
`cSplitFactorFastGWf` and are the predicates consumed by the Wf soundness API. -/

section NormalityWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- The fuel-free weak-normalization guarantee for a rational function denominator. -/
def IsWeaklyNormalizedNormWf (h : QFunNZG β) : Prop :=
  toPolyG (CPolyG.cSplitFactorFastGWf ([CField.one] : CPolyG β) h.1.2).1
    = toPolyG h.1.2

/-- The fuel-free canonicalized weak-normalization guarantee. -/
def IsCanonNormalizedWf (f q' : QFunNZG β) : Prop :=
  IsWeaklyNormalizedNormWf (qReduce (weakNormalizedF f q'))

/-- The fuel-free Boolean check decides `IsCanonNormalizedWf`. -/
theorem cisCanonNormalizedGWf_iff (f q' : QFunNZG β) :
    cisCanonNormalizedGWf (weakNormalizedF f q') = true ↔ IsCanonNormalizedWf f q' := by
  unfold cisCanonNormalizedGWf IsCanonNormalizedWf IsWeaklyNormalizedNormWf
  rw [CPolyG.cisZeroG_iff, CPolyG.toPolyG_csubG, sub_eq_zero]
  rfl

end NormalityWf

/-! ## The Wf re-pin corollary

The Wf wrapper weak-normalizes `f` to `ftilde = weakNormalizedF f q'`
(`q' = qOfPolyNZG (cWeakNormalizerGWf [1] f.1.1 f.1.2)`) and passes the Wf gate
`cisCanonNormalizedGWf ftilde`. The Wf gated core, holding the reduced `qReduce ftilde`, runs the
denominator-direct gate `cisCanonNormalizedCoreGWf (qReduce ftilde)`. The following equations reconcile those
two Wf gates definitionally. -/

section Repin

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- **The Wf re-pin gate reconciliation** (`cisCanonNormalizedCoreGWf_qReduce_weakNormalized`): for the
weak-normalized `ftilde = weakNormalizedF f q'` (`q'` the lift of the fuel-free weak normalizer
`cWeakNormalizerGWf [1] f.1.1 f.1.2`), the Wf gated core's denominator-direct check on the reduced input
equals the Wf wrapper's check on the pre-reduce input. -/
theorem cisCanonNormalizedCoreGWf_qReduce_weakNormalized (f : QFunNZG β) :
    cisCanonNormalizedCoreGWf (qReduce (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))))
      = cisCanonNormalizedGWf (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))) :=
  cisCanonNormalizedCoreGWf_qReduce
    (weakNormalizedF f
      (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)))

/-- **The Wf re-pin gate decides `IsCanonNormalizedWf`**: the Wf gated core's denominator-direct check on the
reduced weak-normalized input passes iff the fuel-free §6.1 normalization guarantee holds. -/
theorem cisCanonNormalizedCoreGWf_qReduce_weakNormalized_iff [CFieldDomain β] (f : QFunNZG β) :
    cisCanonNormalizedCoreGWf (qReduce (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)))) = true
      ↔ IsCanonNormalizedWf f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) := by
  rw [cisCanonNormalizedCoreGWf_qReduce_weakNormalized]
  exact cisCanonNormalizedGWf_iff f _

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The same re-pin reconciliation stated entirely on the Wf gate.
example (f : QFunNZG β) :
    cisCanonNormalizedCoreGWf (qReduce (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))))
      = cisCanonNormalizedGWf (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))) :=
  cisCanonNormalizedCoreGWf_qReduce_weakNormalized f

end Repin

/-! ### Axiom audit -/

#print axioms cisCanonNormalizedCoreGWf_qReduce_weakNormalized
#print axioms cisCanonNormalizedCoreGWf_qReduce_weakNormalized_iff

end DeepWiki.SymbolicIntegration
