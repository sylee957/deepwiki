import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # The tower-gcd correctness witness `CTowerGcdWitnessWf`

A minimal `Prop`-class carrying top-level gcd correctness
`Associated (toPoly (cgcdFFCoreWf a b)) (gcd (toPoly a) (toPoly b))`, from which the primitive
monomial `Dt = [1]` has a constant special part (`cdegG_cSpecialPolyG_one_eq_zero`). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZ

/-- `CTowerGcdWitnessWf α`: the `Prop`-class asserting `toPoly (cgcdFFCoreWf a b)` is `Associated` to
`gcd (toPoly a) (toPoly b)` in `(CFieldSpec.K α)[X]`. -/
class CTowerGcdWitnessWf (α : Type*) [CField α] [CFieldSpec α] [CFracGcdCoreWf α] : Prop where
  /-- `toPoly (cgcdFFCoreWf a b)` is `Associated` to `gcd (toPoly a) (toPoly b)`. -/
  gcdCorrect : ∀ a b : CPoly α,
    Associated (toPoly (CFracGcdCoreWf.cgcdFFCoreWf a b)) (gcd (toPoly a) (toPoly b))

section Hprim

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β]

omit [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β] in
/-- `toPoly [CField.one] = 1`: the constant `[1]` reads as the polynomial `1`. -/
@[denote] theorem toPolyG_cone_eq_one_wf : toPoly ([CField.one] : CPoly β) = 1 := by
  simp only [denote]
  simp

omit [CDiffField β] in
/-- `toPoly (cgcdFFCoreWf [1] z)` is a unit for any `z` (the gcd is `Associated` to `1`). -/
theorem cgcdFFCoreWf_one_isUnit (z : CPoly β) :
    IsUnit (toPoly (CFracGcdCoreWf.cgcdFFCoreWf ([CField.one] : CPoly β) z)) := by
  have hc := CTowerGcdWitnessWf.gcdCorrect ([CField.one] : CPoly β) z
  rw [toPolyG_cone_eq_one_wf, gcd_one_left] at hc
  exact associated_one_iff_isUnit.mp hc

omit [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β] in
/-- Division by a nonzero degree-0 divisor keeps degree 0: if `cdeg c = 0`, `cnorm d ≠ []`, and
`cdeg d = 0`, then `cdeg (cdivWf c d) = 0`. -/
theorem cdegG_cdivWf_zero_of_unit_divisor_wf (c d : CPoly β)
    (hc : cdeg c = 0) (hd0 : CPoly.cnorm d ≠ []) (hd : cdeg d = 0) :
    cdeg (CPoly.cdivWf c d) = 0 := by
  have hdlen : (CPoly.cnorm d : List β).length = 1 := by
    rw [cdeg] at hd
    have : 0 < (CPoly.cnorm d : List β).length := List.length_pos_iff.mpr hd0
    omega
  have hrem := CPoly.cmodWf_length_lt c d hd0
  rw [hdlen] at hrem
  have hremnil : CPoly.cnorm (CPoly.cmodWf c d) = [] := List.length_eq_zero_iff.mp (by omega)
  have hrem0 : toPoly (CPoly.cdivmodWf c d).2 = 0 := by
    rw [show ((CPoly.cdivmodWf c d).2) = CPoly.cmodWf c d from rfl]
    exact (CPoly.cnormG_eq_nil_iff _).mp hremnil
  have hid := CPoly.toPolyG_cdivmodWf c d hd0
  rw [show CPoly.cdivWf c d = (CPoly.cdivmodWf c d).1 from rfl]
  rw [hrem0, add_zero] at hid
  have hdne : toPoly d ≠ 0 := fun h => hd0 ((CPoly.cnormG_eq_nil_iff d).mpr h)
  have hdnd0 : (toPoly d).natDegree = 0 := by rw [← cdegG_eq_natDegree]; exact hd
  have hcnd0 : (toPoly c).natDegree = 0 := by rw [← cdegG_eq_natDegree]; exact hc
  rw [cdegG_eq_natDegree]
  by_cases hquo0 : toPoly (CPoly.cdivmodWf c d).1 = 0
  · rw [hquo0]; simp
  · have hnd := congrArg Polynomial.natDegree hid
    rw [Polynomial.natDegree_mul hquo0 hdne, hdnd0, hcnd0, add_zero] at hnd
    omega

/-- The split step `cstep [1] [1]` on the unit input `[1]` has degree `0` (a unit-by-unit division). -/
theorem cdegG_cstepG_one : cdeg (CPoly.cstep ([CField.one] : CPoly β) [CField.one]) = 0 := by
  rw [CPoly.cstep]
  set g1 := CFracGcdCoreWf.cgcdFFCoreWf ([CField.one] : CPoly β)
    (CPoly.cmonomialDeriv [CField.one] [CField.one]) with hg1
  set g2 := CFracGcdCoreWf.cgcdFFCoreWf ([CField.one] : CPoly β) (CPoly.cderiv [CField.one]) with hg2
  have hd1 : cdeg g1 = 0 := by
    rw [hg1, cdegG_eq_natDegree]; exact natDegree_eq_zero_of_isUnit (cgcdFFCoreWf_one_isUnit _)
  have hd2 : cdeg g2 = 0 := by
    rw [hg2, cdegG_eq_natDegree]; exact natDegree_eq_zero_of_isUnit (cgcdFFCoreWf_one_isUnit _)
  have hg2u : IsUnit (toPoly g2) := by rw [hg2]; exact cgcdFFCoreWf_one_isUnit _
  have hg20 : CPoly.cnorm g2 ≠ [] := by
    intro he; have hz : toPoly g2 = 0 := (CPoly.cnormG_eq_nil_iff g2).mp he
    rw [hz] at hg2u; exact not_isUnit_zero hg2u
  exact cdegG_cdivWf_zero_of_unit_divisor_wf g1 g2 hd1 hg20 hd2

/-- `cSplitFactorFast [1] [1] = ([1], [1])`: the split factorization of the unit `[1]` is trivial. -/
theorem cSplitFactorFastG_one_eq :
    CPoly.cSplitFactorFast ([CField.one] : CPoly β) [CField.one]
      = ([CField.one], [CField.one]) := by
  rw [CPoly.cSplitFactorFast, if_pos cdegG_cstepG_one]

/-- `cdeg (cSpecialPoly [1]) = 0`: the special part of the primitive monomial `[1]` is constant. -/
theorem cdegG_cSpecialPolyG_one_eq_zero :
    cdeg (CPoly.cSpecialPoly ([CField.one] : CPoly β)) = 0 := by
  rw [CPoly.cSpecialPoly, cSplitFactorFastG_one_eq, cdegG_eq_natDegree]
  have hassoc := associated_toPolyG_cmonicG ([CField.one] : CPoly β)
  rw [toPolyG_cone_eq_one_wf] at hassoc
  exact natDegree_eq_zero_of_isUnit (associated_one_iff_isUnit.mp hassoc)

end Hprim

/-! ### Restatement -/

example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β] :
    cdeg (CPoly.cSpecialPoly ([CField.one] : CPoly β)) = 0 :=
  cdegG_cSpecialPolyG_one_eq_zero

/-! ### Axiom audit -/

#print axioms cgcdFFCoreWf_one_isUnit
#print axioms cdegG_cSpecialPolyG_one_eq_zero

end DeepWiki.SymbolicIntegration
