import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveNorm
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # The canonical-normality check is `qReduce`-invariant. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZG

section CoreWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- The fuel-free denominator-direct canonical-normality check. -/
def cisCanonNormalizedCoreG (a : QFunNZG β) : Bool :=
  cdenomNormalGateG a

/-- The fuel-free wrapper canonical-normality check on the reduced denominator. -/
def cisCanonNormalizedG (ftilde : QFunNZG β) : Bool :=
  CPoly.cisZeroG (CPoly.csubG
    (CPoly.cSplitFactorFastG ([CField.one] : CPoly β)
      (QFunNZG.reduceDen ftilde)).1
    (QFunNZG.reduceDen ftilde))

end CoreWf

/-! ## The Wf keystone bridge -/

section Bridge

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- The fuel-free core check on `qReduce x` is the fuel-free wrapper check on `x`. -/
theorem cisCanonNormalizedCoreG_qReduce (x : QFunNZG β) :
    cisCanonNormalizedCoreG (qReduce x) = cisCanonNormalizedG x := rfl

example (x : QFunNZG β) : cisCanonNormalizedCoreG (qReduce x) = cisCanonNormalizedG x := rfl

end Bridge

/-! ## Canonical-normality propositions -/

section NormalityWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- The fuel-free weak-normalization guarantee for a rational function denominator. -/
def IsWeaklyNormalizedNormWf (h : QFunNZG β) : Prop :=
  toPolyG (CPoly.cSplitFactorFastG ([CField.one] : CPoly β) h.1.2).1
    = toPolyG h.1.2

/-- The fuel-free canonicalized weak-normalization guarantee. -/
def IsCanonNormalizedWf (f q' : QFunNZG β) : Prop :=
  IsWeaklyNormalizedNormWf (qReduce (weakNormalizedF f q'))

/-- The fuel-free Boolean check decides `IsCanonNormalizedWf`. -/
theorem cisCanonNormalizedG_iff (f q' : QFunNZG β) :
    cisCanonNormalizedG (weakNormalizedF f q') = true ↔ IsCanonNormalizedWf f q' := by
  unfold cisCanonNormalizedG IsCanonNormalizedWf IsWeaklyNormalizedNormWf
  rw [CPoly.cisZeroG_iff]
  simp only [denote, sub_eq_zero]
  rfl

end NormalityWf

/-! ## The re-pin corollary -/

section Repin

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- For `ftilde = weakNormalizedF f q'` (`q'` the lift of `cWeakNormalizerG [1] f.1.1 f.1.2`), the
core check on the reduced input equals the wrapper check on the pre-reduce input. -/
theorem cisCanonNormalizedCoreG_qReduce_weakNormalized (f : QFunNZG β) :
    cisCanonNormalizedCoreG (qReduce (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2))))
      = cisCanonNormalizedG (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2))) :=
  cisCanonNormalizedCoreG_qReduce
    (weakNormalizedF f
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)))

/-- The core check on the reduced weak-normalized input passes iff `IsCanonNormalizedWf` holds. -/
theorem cisCanonNormalizedCoreG_qReduce_weakNormalized_iff [CFieldDomain β] (f : QFunNZG β) :
    cisCanonNormalizedCoreG (qReduce (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)))) = true
      ↔ IsCanonNormalizedWf f
        (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)) := by
  rw [cisCanonNormalizedCoreG_qReduce_weakNormalized]
  exact cisCanonNormalizedG_iff f _

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The same re-pin reconciliation stated entirely on the Wf gate.
example (f : QFunNZG β) :
    cisCanonNormalizedCoreG (qReduce (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2))))
      = cisCanonNormalizedG (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2))) :=
  cisCanonNormalizedCoreG_qReduce_weakNormalized f

end Repin

/-! ### Axiom audit -/

#print axioms cisCanonNormalizedCoreG_qReduce_weakNormalized
#print axioms cisCanonNormalizedCoreG_qReduce_weakNormalized_iff

/-! ### The canonical-normality predicate and soundness-gate witness -/

section CanonNormalized
variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- `IsCanonNormalized f q'`: the canonicalized element `qReduce (weakNormalizedF f q')` is weakly
normalized (`IsWeaklyNormalizedNorm`). -/
def IsCanonNormalized (f q' : QFunNZG β) : Prop :=
  IsWeaklyNormalizedNorm (qReduce (weakNormalizedF f q'))

end CanonNormalized

/-- The witness scalar `−x ∈ ℚ(x) = QFunNZG ℚ` (numerator `[0, -1] = −x`, denominator `[1]`). -/
def witnessNegX : QFunNZG ℚ := ⟨([(0 : ℚ), -1], [1]), by native_decide⟩

/-- The witness `f = 1/(t₁ − x) ∈ Lvl2 = ℚ(x)(t₁)`: a `D`-constant special pole with no
positive-integer residue. -/
def witnessF : Lvl2 := ⟨([CField.one], [witnessNegX, CField.one]), by native_decide⟩

end DeepWiki.SymbolicIntegration
