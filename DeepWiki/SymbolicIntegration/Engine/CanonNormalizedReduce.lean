import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveNorm
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # The canonical-normality check is `qReduce`-invariant. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZ

section CoreWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- The fuel-free denominator-direct canonical-normality check. -/
def cisCanonNormalizedCore (a : QFunNZ β) : Bool :=
  cdenomNormalGate a

/-- The fuel-free wrapper canonical-normality check on the reduced denominator. -/
def cisCanonNormalized (ftilde : QFunNZ β) : Bool :=
  CPoly.cisZero (CPoly.csub
    (CPoly.cSplitFactorFast ([CField.one] : CPoly β)
      (QFunNZ.reduceDen ftilde)).1
    (QFunNZ.reduceDen ftilde))

end CoreWf

/-! ## The Wf keystone bridge -/

section Bridge

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- The fuel-free core check on `qReduce x` is the fuel-free wrapper check on `x`. -/
theorem cisCanonNormalizedCoreG_qReduce (x : QFunNZ β) :
    cisCanonNormalizedCore (qReduce x) = cisCanonNormalized x := rfl

example (x : QFunNZ β) : cisCanonNormalizedCore (qReduce x) = cisCanonNormalized x := rfl

end Bridge

/-! ## Canonical-normality propositions -/

section NormalityWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- The fuel-free weak-normalization guarantee for a rational function denominator. -/
def IsWeaklyNormalizedNormWf (h : QFunNZ β) : Prop :=
  toPoly (CPoly.cSplitFactorFast ([CField.one] : CPoly β) h.1.2).1
    = toPoly h.1.2

/-- The fuel-free canonicalized weak-normalization guarantee. -/
def IsCanonNormalizedWf (f q' : QFunNZ β) : Prop :=
  IsWeaklyNormalizedNormWf (qReduce (weakNormalizedF f q'))

/-- The fuel-free Boolean check decides `IsCanonNormalizedWf`. -/
theorem cisCanonNormalizedG_iff (f q' : QFunNZ β) :
    cisCanonNormalized (weakNormalizedF f q') = true ↔ IsCanonNormalizedWf f q' := by
  unfold cisCanonNormalized IsCanonNormalizedWf IsWeaklyNormalizedNormWf
  rw [CPoly.cisZeroG_iff]
  simp only [denote, sub_eq_zero]
  rfl

end NormalityWf

/-! ## The re-pin corollary -/

section Repin

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- For `ftilde = weakNormalizedF f q'` (`q'` the lift of `cWeakNormalizer [1] f.1.1 f.1.2`), the
core check on the reduced input equals the wrapper check on the pre-reduce input. -/
theorem cisCanonNormalizedCoreG_qReduce_weakNormalized (f : QFunNZ β) :
    cisCanonNormalizedCore (qReduce (weakNormalizedF f
        (qOfPolyNZ (cWeakNormalizer ([CField.one] : CPoly β) f.1.1 f.1.2))))
      = cisCanonNormalized (weakNormalizedF f
        (qOfPolyNZ (cWeakNormalizer ([CField.one] : CPoly β) f.1.1 f.1.2))) :=
  cisCanonNormalizedCoreG_qReduce
    (weakNormalizedF f
      (qOfPolyNZ (cWeakNormalizer ([CField.one] : CPoly β) f.1.1 f.1.2)))

/-- The core check on the reduced weak-normalized input passes iff `IsCanonNormalizedWf` holds. -/
theorem cisCanonNormalizedCoreG_qReduce_weakNormalized_iff [CFieldDomain β] (f : QFunNZ β) :
    cisCanonNormalizedCore (qReduce (weakNormalizedF f
        (qOfPolyNZ (cWeakNormalizer ([CField.one] : CPoly β) f.1.1 f.1.2)))) = true
      ↔ IsCanonNormalizedWf f
        (qOfPolyNZ (cWeakNormalizer ([CField.one] : CPoly β) f.1.1 f.1.2)) := by
  rw [cisCanonNormalizedCoreG_qReduce_weakNormalized]
  exact cisCanonNormalizedG_iff f _

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The same re-pin reconciliation stated entirely on the Wf gate.
example (f : QFunNZ β) :
    cisCanonNormalizedCore (qReduce (weakNormalizedF f
        (qOfPolyNZ (cWeakNormalizer ([CField.one] : CPoly β) f.1.1 f.1.2))))
      = cisCanonNormalized (weakNormalizedF f
        (qOfPolyNZ (cWeakNormalizer ([CField.one] : CPoly β) f.1.1 f.1.2))) :=
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
def IsCanonNormalized (f q' : QFunNZ β) : Prop :=
  IsWeaklyNormalizedNorm (qReduce (weakNormalizedF f q'))

end CanonNormalized

/-- The witness scalar `−x ∈ ℚ(x) = QFunNZ ℚ` (numerator `[0, -1] = −x`, denominator `[1]`). -/
def witnessNegX : QFunNZ ℚ := ⟨([(0 : ℚ), -1], [1]), by native_decide⟩

/-- The witness `f = 1/(t₁ − x) ∈ Lvl2 = ℚ(x)(t₁)`: a `D`-constant special pole with no
positive-integer residue. -/
def witnessF : Lvl2 := ⟨([CField.one], [witnessNegX, CField.one]), by native_decide⟩

end DeepWiki.SymbolicIntegration
