import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveNorm
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # The canonical-normality check is `qReduce`-invariant. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

section CoreWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- The fuel-free wrapper canonical-normality check on the reduced denominator. -/
def cisCanonNormalized (ftilde : CFrac β) : Bool :=
  DensePoly.cisZero (DensePoly.csub
    (DensePoly.cSplitFactorFast ([CCommRing.one] : DensePoly β)
      (CFrac.reduceDen ftilde)).1
    (CFrac.reduceDen ftilde))

end CoreWf

/-! ## The Wf keystone bridge -/

section Bridge

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- The denominator-normality gate on `qReduce x` is the wrapper check on `x`. -/
theorem cdenomNormalGateG_qReduce (x : CFrac β) :
    cdenomNormalGate (qReduce x) = cisCanonNormalized x := rfl

example (x : CFrac β) : cdenomNormalGate (qReduce x) = cisCanonNormalized x := rfl

end Bridge

/-! ## Canonical-normality propositions -/

section NormalityWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- `IsCanonNormalized f q'`: the canonicalized element `qReduce (weakNormalizedF f q')` is weakly
normalized (`IsWeaklyNormalizedNorm`). -/
def IsCanonNormalized (f q' : CFrac β) : Prop :=
  IsWeaklyNormalizedNorm (qReduce (weakNormalizedF f q'))

/-- The fuel-free Boolean check decides `IsCanonNormalized`. -/
theorem cisCanonNormalizedG_iff (f q' : CFrac β) :
    cisCanonNormalized (weakNormalizedF f q') = true ↔ IsCanonNormalized f q' := by
  unfold cisCanonNormalized IsCanonNormalized IsWeaklyNormalizedNorm
  rw [DensePoly.cisZeroG_iff]
  simp only [denote, sub_eq_zero]
  rfl

end NormalityWf

/-! ## The re-pin corollary -/

section Repin

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- For `ftilde = weakNormalizedF f q'` (`q'` the lift of `cWeakNormalizer [1] f.1.1 f.1.2`), the
denominator gate on the reduced input equals the wrapper check on the pre-reduce input. -/
theorem cdenomNormalGateG_qReduce_weakNormalized (f : CFrac β) :
    cdenomNormalGate (qReduce (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2))))
      = cisCanonNormalized (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2))) :=
  cdenomNormalGateG_qReduce
    (weakNormalizedF f
      (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2)))

/-- The denominator gate on the reduced weak-normalized input passes iff `IsCanonNormalized` holds. -/
theorem cdenomNormalGateG_qReduce_weakNormalized_iff [CFieldDomain β] (f : CFrac β) :
    cdenomNormalGate (qReduce (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2)))) = true
      ↔ IsCanonNormalized f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2)) := by
  rw [cdenomNormalGateG_qReduce_weakNormalized]
  exact cisCanonNormalizedG_iff f _

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The same re-pin reconciliation stated entirely on the Wf gate.
example (f : CFrac β) :
    cdenomNormalGate (qReduce (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2))))
      = cisCanonNormalized (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2))) :=
  cdenomNormalGateG_qReduce_weakNormalized f

end Repin

/-! ### Axiom audit -/

#print axioms cdenomNormalGateG_qReduce_weakNormalized
#print axioms cdenomNormalGateG_qReduce_weakNormalized_iff

/-- The witness scalar `−x ∈ ℚ(x) = CFrac ℚ` (numerator `[0, -1] = −x`, denominator `[1]`). -/
def witnessNegX : CFrac ℚ := CFrac.ofPoly [(0 : ℚ), -1]

/-- The witness `f = 1/(t₁ − x) ∈ Lvl2 = ℚ(x)(t₁)`: a `D`-constant special pole with no
positive-integer residue. -/
def witnessF : Lvl2 := CFrac.ofFraction [CCommRing.one] [witnessNegX, CCommRing.one]

end DeepWiki.SymbolicIntegration
