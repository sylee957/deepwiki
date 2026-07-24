import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # Selected tower-gcd unit consequences

Consequences of `LawfulCPolyGcd` showing that the primitive monomial `Dt = [1]` has a constant
special part (`cdegG_cSpecialPolyG_one_eq_zero`). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

universe u v

section Hprim

variable {β : Type u} [CField β] [CFieldSpec.{u,v} β] [CDiffField β]
  [CPolyGcd DensePoly β] [LawfulCPolyGcd.{u,v} DensePoly β]

omit [CDiffField β] in
/-- The selected dense gcd of `[1]` and any tower polynomial denotes a unit. -/
theorem selectedGcd_one_isUnit (z : DensePoly β) :
    IsUnit (CPoly.toPoly (CPolyGcd.compute ([CCommRing.one] : DensePoly β) z)) :=
  LawfulCPolyGcd.compute_one_isUnit z

/-- The split step `cstep [1] [1]` on the unit input `[1]` has degree `0` (a unit-by-unit division). -/
theorem cdegG_cstepG_one : cdeg (DensePoly.cstep ([CCommRing.one] : DensePoly β) [CCommRing.one]) = 0 := by
  rw [DensePoly.cstep]
  set g1 := CPolyGcd.compute ([CCommRing.one] : DensePoly β)
    (CPolyEngine.monomialDeriv [CCommRing.one] [CCommRing.one]) with hg1
  set g2 := CPolyGcd.compute ([CCommRing.one] : DensePoly β) (DensePoly.cderiv [CCommRing.one]) with hg2
  have hd1 : cdeg g1 = 0 := by
    rw [hg1, cdegG_eq_natDegree]
    exact natDegree_eq_zero_of_isUnit (by
      simpa only [toPoly_list_eq] using selectedGcd_one_isUnit _)
  have hg2u : IsUnit (toPoly g2) := by
    rw [hg2]
    simpa only [toPoly_list_eq] using selectedGcd_one_isUnit _
  have hg20 : DensePoly.cnorm g2 ≠ [] := by
    intro he; have hz : toPoly g2 = 0 := (DensePoly.cnormG_eq_nil_iff g2).mp he
    rw [hz] at hg2u; exact not_isUnit_zero hg2u
  rw [cdegG_eq_natDegree]
  simpa only [toPoly_list_eq] using
    CPolyEuclidean.div_natDegree_eq_zero_of_natDegree_eq_zero g1 g2
      (by simpa only [toPoly_list_eq, ← cdegG_eq_natDegree] using hd1)
      (by simpa only [toPoly_list_eq] using
        (fun h => hg20 ((DensePoly.cnormG_eq_nil_iff g2).mpr h)))

/-- `CPoly.splitFactor [1] [1] = ([1], [1])`: the split factorization of the unit `[1]` is trivial. -/
theorem CPoly.splitFactor_one_eq :
    CPoly.splitFactor ([CCommRing.one] : DensePoly β) [CCommRing.one]
      = ([CCommRing.one], [CCommRing.one]) := by
  rw [CPoly.splitFactor_dense_eq, DensePoly.cSplitFactorFast, if_pos cdegG_cstepG_one]

/-- `cdeg (cSpecialPoly [1]) = 0`: the special part of the primitive monomial `[1]` is constant. -/
theorem cdegG_cSpecialPolyG_one_eq_zero :
    cdeg (DensePoly.cSpecialPoly ([CCommRing.one] : DensePoly β)) = 0 := by
  rw [DensePoly.cSpecialPoly, CPoly.splitFactor_one_eq, cdegG_eq_natDegree]
  have hassoc := associated_toPolyG_cmonicG ([CCommRing.one] : DensePoly β)
  have hone : toPoly ([CCommRing.one] : DensePoly β) = 1 := by
    simp only [denote]
    simp
  rw [hone] at hassoc
  exact natDegree_eq_zero_of_isUnit (associated_one_iff_isUnit.mp hassoc)

end Hprim

/-! ### Axiom audit -/

#print axioms selectedGcd_one_isUnit
#print axioms cdegG_cSpecialPolyG_one_eq_zero

end DeepWiki.SymbolicIntegration
