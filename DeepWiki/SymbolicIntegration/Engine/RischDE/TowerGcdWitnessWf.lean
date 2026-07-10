import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # The tower-gcd correctness witness `CTowerGcdWitnessWf`

A minimal `Prop`-class carrying top-level gcd correctness
`Associated (toPoly (cgcdFFCoreWf a b)) (gcd (toPoly a) (toPoly b))`, from which the primitive
monomial `Dt = [1]` has a constant special part (`cdegG_cSpecialPolyG_one_eq_zero`). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-- `CTowerGcdWitnessWf α`: the `Prop`-class asserting `toPoly (cgcdFFCoreWf a b)` is `Associated` to
`gcd (toPoly a) (toPoly b)` in `(CFieldSpec.K α)[X]`. -/
class CTowerGcdWitnessWf (α : Type*) [CField α] [CFieldSpec α] [CFracGcdCoreWf α] : Prop where
  /-- `toPoly (cgcdFFCoreWf a b)` is `Associated` to `gcd (toPoly a) (toPoly b)`. -/
  gcdCorrect : ∀ a b : DensePoly α,
    Associated (toPoly (CFracGcdCoreWf.cgcdFFCoreWf a b)) (gcd (toPoly a) (toPoly b))

section Hprim

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β]

omit [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β] in
/-- `toPoly [CCommRing.one] = 1`: the constant `[1]` reads as the polynomial `1`. -/
@[denote] theorem toPolyG_cone_eq_one_wf : toPoly ([CCommRing.one] : DensePoly β) = 1 := by
  simp only [denote]
  simp

omit [CDiffField β] in
/-- `toPoly (cgcdFFCoreWf [1] z)` is a unit for any `z` (the gcd is `Associated` to `1`). -/
theorem cgcdFFCoreWf_one_isUnit (z : DensePoly β) :
    IsUnit (toPoly (CFracGcdCoreWf.cgcdFFCoreWf ([CCommRing.one] : DensePoly β) z)) := by
  have hc := CTowerGcdWitnessWf.gcdCorrect ([CCommRing.one] : DensePoly β) z
  rw [toPolyG_cone_eq_one_wf, gcd_one_left] at hc
  exact associated_one_iff_isUnit.mp hc

omit [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β] in
/-- Dividing a degree-0 polynomial by a nonzero polynomial keeps degree 0. -/
theorem cdegG_div_eq_zero_of_cdegG_zero (c d : DensePoly β)
    (hc : cdeg c = 0) (hd0 : DensePoly.cnorm d ≠ []) :
    cdeg (CPolyEuclidean.div c d) = 0 := by
  have hdne : toPoly d ≠ 0 := fun h => hd0 ((DensePoly.cnormG_eq_nil_iff d).mpr h)
  have hcnd0 : (toPoly c).natDegree = 0 := by rw [← cdegG_eq_natDegree]; exact hc
  rw [cdegG_eq_natDegree]
  simpa only [toPoly_list_eq] using
    CPolyEuclidean.div_natDegree_eq_zero_of_natDegree_eq_zero c d
      (by simpa only [toPoly_list_eq] using hcnd0)
      (by simpa only [toPoly_list_eq] using hdne)

/-- The split step `cstep [1] [1]` on the unit input `[1]` has degree `0` (a unit-by-unit division). -/
theorem cdegG_cstepG_one : cdeg (DensePoly.cstep ([CCommRing.one] : DensePoly β) [CCommRing.one]) = 0 := by
  rw [DensePoly.cstep]
  set g1 := CFracGcdCoreWf.cgcdFFCoreWf ([CCommRing.one] : DensePoly β)
    (DensePoly.cmonomialDeriv [CCommRing.one] [CCommRing.one]) with hg1
  set g2 := CFracGcdCoreWf.cgcdFFCoreWf ([CCommRing.one] : DensePoly β) (DensePoly.cderiv [CCommRing.one]) with hg2
  have hd1 : cdeg g1 = 0 := by
    rw [hg1, cdegG_eq_natDegree]; exact natDegree_eq_zero_of_isUnit (cgcdFFCoreWf_one_isUnit _)
  have hg2u : IsUnit (toPoly g2) := by rw [hg2]; exact cgcdFFCoreWf_one_isUnit _
  have hg20 : DensePoly.cnorm g2 ≠ [] := by
    intro he; have hz : toPoly g2 = 0 := (DensePoly.cnormG_eq_nil_iff g2).mp he
    rw [hz] at hg2u; exact not_isUnit_zero hg2u
  exact cdegG_div_eq_zero_of_cdegG_zero g1 g2 hd1 hg20

/-- `cSplitFactorFast [1] [1] = ([1], [1])`: the split factorization of the unit `[1]` is trivial. -/
theorem cSplitFactorFastG_one_eq :
    DensePoly.cSplitFactorFast ([CCommRing.one] : DensePoly β) [CCommRing.one]
      = ([CCommRing.one], [CCommRing.one]) := by
  rw [DensePoly.cSplitFactorFast, if_pos cdegG_cstepG_one]

/-- `cdeg (cSpecialPoly [1]) = 0`: the special part of the primitive monomial `[1]` is constant. -/
theorem cdegG_cSpecialPolyG_one_eq_zero :
    cdeg (DensePoly.cSpecialPoly ([CCommRing.one] : DensePoly β)) = 0 := by
  rw [DensePoly.cSpecialPoly, cSplitFactorFastG_one_eq, cdegG_eq_natDegree]
  have hassoc := associated_toPolyG_cmonicG ([CCommRing.one] : DensePoly β)
  rw [toPolyG_cone_eq_one_wf] at hassoc
  exact natDegree_eq_zero_of_isUnit (associated_one_iff_isUnit.mp hassoc)

end Hprim

/-! ### Restatement -/

example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β] :
    cdeg (DensePoly.cSpecialPoly ([CCommRing.one] : DensePoly β)) = 0 :=
  cdegG_cSpecialPolyG_one_eq_zero

/-! ### Axiom audit -/

#print axioms cgcdFFCoreWf_one_isUnit
#print axioms cdegG_cSpecialPolyG_one_eq_zero

end DeepWiki.SymbolicIntegration
