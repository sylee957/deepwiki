import DeepWiki.SymbolicIntegration.Computable.Tower.RischDEWellFounded

/-! # The fuel-free tower-gcd correctness witness `CTowerGcdWitnessWf`

The fuel-free analogue of `CTowerGcdWitness` (`SoundnessCapstone`): a minimal `Prop`-class carrying the
top-level Wf-gcd correctness `Associated (toPolyG (cgcdFFCoreWf a b)) (gcd (toPolyG a) (toPolyG b))`. Where
`CTowerGcdWitness` packages the raw PRS regularity witnesses and *derives* correctness through the fuel'd
`associated_toPolyG_cgcdFFCore` development, this Wf witness carries the *result* directly — the fuel-free
gcd `cgcdFFCoreWf` has no fuel-threaded abstract-correctness theorem yet, so the correctness it would produce
is assumed at the `cgcdFFCoreWf` level (the same *kind* of per-run regularity assumption, packaged one layer
up).

From it we derive the **Hprim chain** for the recursive primitive monomial `Dt = [1]`: the gcd of the unit
`[1]` is a unit, so the fuel-free splitting factorization of `[1]` is trivial, so the special part of `[1]` is
the constant `[1]` (`cdegG_cSpecialPolyGWf_one_eq_zero`). This is the fuel-free analogue of the
`RischDE/NormalCorrect.lean` Hprim section — the `hprim` discharge the fuel-free tower RDE instance's
soundness residual needs (`docs/rischde-wf-migration.md` Phase P2). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-- **★ The fuel-free tower-gcd correctness witness** `CTowerGcdWitnessWf α`: the minimal `Prop`-class
carrying the top-level Wf-gcd correctness at level `α` — `toPolyG (cgcdFFCoreWf a b)` is `Associated` to
`gcd (toPolyG a) (toPolyG b)` in `(CFieldSpec.K α)[X]`. The fuel-free analogue of `CTowerGcdWitness`,
packaging the correctness one layer up (at `cgcdFFCoreWf` rather than the raw PRS) since the fuel-free gcd has
no fuel-threaded abstract-correctness theorem. -/
class CTowerGcdWitnessWf (α : Type*) [CField α] [CFieldSpec α] [CFracGcdCoreWf α] : Prop where
  /-- The level-`α` fuel-free monic gcd is gcd-correct: `toPolyG (cgcdFFCoreWf a b)` is `Associated` to
  `gcd (toPolyG a) (toPolyG b)`. -/
  gcdCorrect : ∀ a b : CPolyG α,
    Associated (toPolyG (CFracGcdCoreWf.cgcdFFCoreWf a b)) (gcd (toPolyG a) (toPolyG b))

section Hprim

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β]

omit [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β] in
/-- `toPolyG [CField.one] = 1`: the constant `[1]` reads as the polynomial `1`. -/
theorem toPolyG_cone_eq_one_wf : toPolyG ([CField.one] : CPolyG β) = 1 := by
  rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]

omit [CDiffField β] in
/-- Under the fuel-free tower-gcd witness, `toPolyG (cgcdFFCoreWf [1] z)` is a unit for any `z`: the gcd is
`Associated` to `gcd 1 _ = 1`. -/
theorem cgcdFFCoreWf_one_isUnit (z : CPolyG β) :
    IsUnit (toPolyG (CFracGcdCoreWf.cgcdFFCoreWf ([CField.one] : CPolyG β) z)) := by
  have hc := CTowerGcdWitnessWf.gcdCorrect ([CField.one] : CPolyG β) z
  rw [toPolyG_cone_eq_one_wf, gcd_one_left] at hc
  exact associated_one_iff_isUnit.mp hc

omit [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β] in
/-- Division by a nonzero degree-0 divisor keeps degree 0: if `cdegG c = 0`, `cnormG d ≠ []`, and
`cdegG d = 0`, then `cdegG (cdivWf c d) = 0`. Fuel-agnostic (mirror of the fuel'd
`cdegG_cdivWf_zero_of_unit_divisor`). -/
theorem cdegG_cdivWf_zero_of_unit_divisor_wf (c d : CPolyG β)
    (hc : cdegG c = 0) (hd0 : CPolyG.cnormG d ≠ []) (hd : cdegG d = 0) :
    cdegG (CPolyG.cdivWf c d) = 0 := by
  have hdlen : (CPolyG.cnormG d : List β).length = 1 := by
    rw [cdegG] at hd
    have : 0 < (CPolyG.cnormG d : List β).length := List.length_pos_iff.mpr hd0
    omega
  have hrem := CPolyG.cmodWf_length_lt c d hd0
  rw [hdlen] at hrem
  have hremnil : CPolyG.cnormG (CPolyG.cmodWf c d) = [] := List.length_eq_zero_iff.mp (by omega)
  have hrem0 : toPolyG (CPolyG.cdivmodWf c d).2 = 0 := by
    rw [show ((CPolyG.cdivmodWf c d).2) = CPolyG.cmodWf c d from rfl]
    exact (CPolyG.cnormG_eq_nil_iff _).mp hremnil
  have hid := CPolyG.toPolyG_cdivmodWf c d hd0
  rw [show CPolyG.cdivWf c d = (CPolyG.cdivmodWf c d).1 from rfl]
  rw [hrem0, add_zero] at hid
  have hdne : toPolyG d ≠ 0 := fun h => hd0 ((CPolyG.cnormG_eq_nil_iff d).mpr h)
  have hdnd0 : (toPolyG d).natDegree = 0 := by rw [← cdegG_eq_natDegree]; exact hd
  have hcnd0 : (toPolyG c).natDegree = 0 := by rw [← cdegG_eq_natDegree]; exact hc
  rw [cdegG_eq_natDegree]
  by_cases hquo0 : toPolyG (CPolyG.cdivmodWf c d).1 = 0
  · rw [hquo0]; simp
  · have hnd := congrArg Polynomial.natDegree hid
    rw [Polynomial.natDegree_mul hquo0 hdne, hdnd0, hcnd0, add_zero] at hnd
    omega

/-- The fuel-free split step `cstepGWf [1] [1]` on the unit input `[1]` has degree `0`: both gcds are units
(`cgcdFFCoreWf_one_isUnit`), so the step is a unit-by-unit division. A constant step stops the split
recursion. -/
theorem cdegG_cstepGWf_one : cdegG (CPolyG.cstepGWf ([CField.one] : CPolyG β) [CField.one]) = 0 := by
  rw [CPolyG.cstepGWf]
  set g1 := CFracGcdCoreWf.cgcdFFCoreWf ([CField.one] : CPolyG β)
    (CPolyG.cmonomialDeriv [CField.one] [CField.one]) with hg1
  set g2 := CFracGcdCoreWf.cgcdFFCoreWf ([CField.one] : CPolyG β) (CPolyG.cderivG [CField.one]) with hg2
  have hd1 : cdegG g1 = 0 := by
    rw [hg1, cdegG_eq_natDegree]; exact natDegree_eq_zero_of_isUnit (cgcdFFCoreWf_one_isUnit _)
  have hd2 : cdegG g2 = 0 := by
    rw [hg2, cdegG_eq_natDegree]; exact natDegree_eq_zero_of_isUnit (cgcdFFCoreWf_one_isUnit _)
  have hg2u : IsUnit (toPolyG g2) := by rw [hg2]; exact cgcdFFCoreWf_one_isUnit _
  have hg20 : CPolyG.cnormG g2 ≠ [] := by
    intro he; have hz : toPolyG g2 = 0 := (CPolyG.cnormG_eq_nil_iff g2).mp he
    rw [hz] at hg2u; exact not_isUnit_zero hg2u
  exact cdegG_cdivWf_zero_of_unit_divisor_wf g1 g2 hd1 hg20 hd2

/-- `cSplitFactorFastGWf [1] [1] = ([1], [1])`: the fuel-free split factorization of the unit `[1]` is
trivial (the step is constant, so the recursion never fires). -/
theorem cSplitFactorFastGWf_one_eq :
    CPolyG.cSplitFactorFastGWf ([CField.one] : CPolyG β) [CField.one]
      = ([CField.one], [CField.one]) := by
  rw [CPolyG.cSplitFactorFastGWf, if_pos cdegG_cstepGWf_one]

/-- `cdegG (cSpecialPolyGWf [1]) = 0`: the special part of the primitive monomial `[1]` is constant — the
`hprim` clause of the fuel-free tower RDE residual for the recursive instance (`Dt = [1]`). -/
theorem cdegG_cSpecialPolyGWf_one_eq_zero :
    cdegG (CPolyG.cSpecialPolyGWf ([CField.one] : CPolyG β)) = 0 := by
  rw [CPolyG.cSpecialPolyGWf, cSplitFactorFastGWf_one_eq, cdegG_eq_natDegree]
  have hassoc := associated_toPolyG_cmonicG ([CField.one] : CPolyG β)
  rw [toPolyG_cone_eq_one_wf] at hassoc
  exact natDegree_eq_zero_of_isUnit (associated_one_iff_isUnit.mp hassoc)

end Hprim

/-! ### Restatement -/

example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β] [CTowerGcdWitnessWf β] :
    cdegG (CPolyG.cSpecialPolyGWf ([CField.one] : CPolyG β)) = 0 :=
  cdegG_cSpecialPolyGWf_one_eq_zero

/-! ### Axiom audit (the Hprim discharges are axiom-clean, NO `native_decide`) -/

#print axioms cgcdFFCoreWf_one_isUnit
#print axioms cdegG_cSpecialPolyGWf_one_eq_zero

end DeepWiki.SymbolicIntegration
