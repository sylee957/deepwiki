import DeepWiki.SymbolicIntegration.Engine.Hermite.Reduction
import DeepWiki.SymbolicIntegration.Engine.Hermite.ValuationTower

/-! # Tower Hermite reduction realization

The tower Hermite reducer realizes the `LawfulHermiteReduction` interface: the field identity,
squarefree leftover denominator, and properness clauses are assembled from the corresponding tower
and squarefree-decomposition facts. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

variable {α : Type*} [CField α] [CDiffField α]

/-- Dense realization of the representation-neutral transcendental Hermite-reduction operation. -/
instance instCHermiteReductionDense [CPolySquarefree DensePoly α] :
    CHermiteReduction DensePoly α where
  compute Dt a d :=
    let out := DensePoly.cHermiteReduceTower Dt a d
    { rationalNum := out.1.1
      rationalDen := out.1.2
      remainderNum := out.2.1
      remainderDen := out.2.2 }

section Selected

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
  [CPolySquarefree DensePoly α]

/-- A lawful selected squarefree decomposition makes the Hermite leftover denominator squarefree. -/
theorem cHermiteReduceTower_squarefree_of_decomposition (Dt a d : DensePoly α)
    (hdecomp : LawfulSquarefreeDecomposition d (CPoly.squarefreeYun d)) :
    Squarefree (toPoly (cHermiteReduceTower Dt a d).2.2) := by
  rw [show toPoly (cHermiteReduceTower Dt a d).2.2 =
      ((CPoly.squarefreeYun d).map DensePoly.toPoly).prod from by
    rw [cHermiteReduceTower]
    simp only [denote]
    simp]
  have hmap : (CPoly.squarefreeYun d).map CPoly.toPoly =
      (CPoly.squarefreeYun d).map DensePoly.toPoly := by
    apply List.map_congr_left
    intro p _
    exact toPoly_list_eq p
  rw [← hmap]
  exact hdecomp.prod_squarefree

end Selected

section SelectedRealization

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CPolySquarefree DensePoly α]

/-- Semantic contracts assemble the selected tower Hermite output into `LawfulHermiteReduction`. -/
theorem cHermiteReduceTower_lawful_of_contracts (Dt a d : DensePoly α)
    (hfield : towerFractionFieldDeriv Dt
        (am α (toPoly (cHermiteReduceTower Dt a d).1.1)
          / am α (toPoly (cHermiteReduceTower Dt a d).1.2))
      + am α (toPoly (cHermiteReduceTower Dt a d).2.1)
          / am α (toPoly (cHermiteReduceTower Dt a d).2.2)
      = am α (toPoly a) / am α (toPoly d))
    (hdecomp : LawfulSquarefreeDecomposition d (CPoly.squarefreeYun d))
    (hproper : (toPoly (cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (cHermiteReduceTower Dt a d).2.2).degree) :
    LawfulHermiteReduction Dt a d (cHermiteReduceTower Dt a d).1.1
      (cHermiteReduceTower Dt a d).1.2 (cHermiteReduceTower Dt a d).2.1
      (cHermiteReduceTower Dt a d).2.2 where
  field_identity := by
    simpa only [towerFractionFieldDerivP, towerFractionFieldDeriv, toPoly_list_eq] using hfield
  squarefree := by
    simpa only [toPoly_list_eq] using cHermiteReduceTower_squarefree_of_decomposition Dt a d hdecomp
  proper := by simpa only [toPoly_list_eq] using hproper

/-- The selected squarefree contract supplies the decomposition clause of the Hermite realization. -/
theorem cHermiteReduceTower_lawful_of_selected_squarefree [CharZero (CFieldSpec.K α)]
    [LawfulCPolySquarefree DensePoly α] (Dt a d : DensePoly α)
    (hfield : towerFractionFieldDeriv Dt
        (am α (toPoly (cHermiteReduceTower Dt a d).1.1)
          / am α (toPoly (cHermiteReduceTower Dt a d).1.2))
      + am α (toPoly (cHermiteReduceTower Dt a d).2.1)
          / am α (toPoly (cHermiteReduceTower Dt a d).2.2)
      = am α (toPoly a) / am α (toPoly d))
    (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hproper : (toPoly (cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (cHermiteReduceTower Dt a d).2.2).degree) :
    LawfulHermiteReduction Dt a d (cHermiteReduceTower Dt a d).1.1
      (cHermiteReduceTower Dt a d).1.2 (cHermiteReduceTower Dt a d).2.1
      (cHermiteReduceTower Dt a d).2.2 :=
  cHermiteReduceTower_lawful_of_contracts Dt a d hfield
    (LawfulCPolySquarefree.compute_lawful' d
      (by simpa only [toPoly_list_eq] using hd0)
      (by simpa only [toPoly_list_eq] using hpp)) hproper

end SelectedRealization

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α]

/-- `cHermiteReduceTower` is a lawful Hermite reduction of `a/d` under differential normality. -/
theorem cHermiteReduceTowerG_lawfulHermiteReduction [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPoly (cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (cHermiteReduceTower Dt a d).2.2).degree) :
    LawfulHermiteReduction Dt a d (cHermiteReduceTower Dt a d).1.1
      (cHermiteReduceTower Dt a d).1.2 (cHermiteReduceTower Dt a d).2.1
      (cHermiteReduceTower Dt a d).2.2 := by
  letI : Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) := ⟨hgcd⟩
  apply cHermiteReduceTower_lawful_of_selected_squarefree Dt a d ?_ hd0 hpp hproper
  have hcap := cHermiteReduceTowerG_field_identity hgcd Dt a d hd0 hpp hcopgcd
  rwa [toPolyG_hNum'_eq_2_1 hgcd Dt a d hd0 hpp hcopgcd] at hcap

end DeepWiki.SymbolicIntegration
