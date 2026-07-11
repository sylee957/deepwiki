import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveNorm
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # The canonical-normality check is `qReduce`-invariant. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

universe u

namespace CFrac

/-- The fuel-free wrapper canonical-normality check on the reduced denominator. -/
def canonNormalizedGate {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [CPolyGcd P] [CPolyEuclidean P] [CFrac F P]
    {β : Type u} [CField β] [CDiffField β] (ftilde : F β) : Bool :=
  CPolyEngine.cisZero (CPolyEngine.sub
    (CPoly.splitFactor (CPoly.one : P β) (CFrac.reduceDen ftilde)).1
    (CFrac.reduceDen ftilde))

/-- Sparse canonical-normality checking shares the generic reduced-denominator path. -/
example :
    let den : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, 1), (1, 1)]
    let a : SparseFrac ℚ := CFrac.ofFraction CPoly.one den (by cfrac_nonzero)
    CFrac.canonNormalizedGate a = true := by
  ccompute

end CFrac

/-! ## The Wf keystone bridge -/

section Bridge

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β]

/-- The denominator-normality gate on `qReduce x` is the wrapper check on `x`. -/
theorem denomNormalGate_qReduce (x : DenseFrac β) :
    CFrac.denomNormalGate (qReduce x) = CFrac.canonNormalizedGate x := rfl

example (x : DenseFrac β) :
    CFrac.denomNormalGate (qReduce x) = CFrac.canonNormalizedGate x := rfl

end Bridge

/-! ## Canonical-normality propositions -/

section NormalityWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β DensePoly]

/-- `IsCanonNormalized f q'`: the canonicalized element `qReduce (weakNormalizedF f q')` is weakly
normalized (`IsWeaklyNormalizedNorm`). -/
def IsCanonNormalized (f q' : DenseFrac β) : Prop :=
  IsWeaklyNormalizedNorm (qReduce (weakNormalizedF f q'))

/-- The fuel-free Boolean check decides `IsCanonNormalized`. -/
theorem canonNormalizedGate_iff (f q' : DenseFrac β) :
    CFrac.canonNormalizedGate (weakNormalizedF f q') = true ↔ IsCanonNormalized f q' := by
  unfold CFrac.canonNormalizedGate IsCanonNormalized IsWeaklyNormalizedNorm
  rw [LawfulCPolyEngine.cisZero_iff, CPolyEngine.toPoly_sub, sub_eq_zero]
  rfl

end NormalityWf

/-! ## The re-pin corollary -/

section Repin

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- For `ftilde = weakNormalizedF f q'` (`q'` the lift of `cWeakNormalizer [1] f.num f.den`), the
denominator gate on the reduced input equals the wrapper check on the pre-reduce input. -/
theorem denomNormalGate_qReduce_weakNormalized (f : DenseFrac β) :
    CFrac.denomNormalGate (qReduce (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den))))
      = CFrac.canonNormalizedGate (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den))) :=
  denomNormalGate_qReduce
    (weakNormalizedF f
      (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)))

/-- The denominator gate on the reduced weak-normalized input passes iff `IsCanonNormalized` holds. -/
theorem denomNormalGate_qReduce_weakNormalized_iff [CFieldDomain β DensePoly] (f : DenseFrac β) :
    CFrac.denomNormalGate (qReduce (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)))) = true
      ↔ IsCanonNormalized f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)) := by
  rw [denomNormalGate_qReduce_weakNormalized]
  exact canonNormalizedGate_iff f _

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The same re-pin reconciliation stated entirely on the Wf gate.
example (f : DenseFrac β) :
    CFrac.denomNormalGate (qReduce (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den))))
      = CFrac.canonNormalizedGate (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den))) :=
  denomNormalGate_qReduce_weakNormalized f

end Repin

/-! ### Axiom audit -/

#print axioms denomNormalGate_qReduce_weakNormalized
#print axioms denomNormalGate_qReduce_weakNormalized_iff

/-- The witness scalar `−x ∈ ℚ(x) = DenseFrac ℚ` (numerator `[0, -1] = −x`, denominator `[1]`). -/
def witnessNegX : DenseFrac ℚ := CFrac.ofPoly [(0 : ℚ), -1]

/-- The witness `f = 1/(t₁ − x) ∈ Lvl2 = ℚ(x)(t₁)`: a `D`-constant special pole with no
positive-integer residue. -/
def witnessF : Lvl2 :=
  CFrac.ofFraction [CCommRing.one] [witnessNegX, CCommRing.one] (by cfrac_nonzero)

end DeepWiki.SymbolicIntegration
