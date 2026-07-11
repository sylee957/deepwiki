import DeepWiki.SymbolicIntegration.Engine.Hermite.ReductionRealization
import DeepWiki.SymbolicIntegration.Engine.LrtResidueResultantDischarge.GenuineMonomial

/-! # Lawful dense transcendental Hermite reduction

The selected dense loop satisfies the representation-neutral Hermite contract on differential
normal-squarefree denominators in the low-derivation-degree regime. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial DensePoly CFrac Classical
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

omit [CFieldSpec α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] in
/-- The generic dense Hermite result unfolds to the selected tower-loop output. -/
private theorem hermiteResult_dense (Dt a d : DensePoly α) [CPolySquarefree DensePoly α] :
    hermiteResult Dt a d =
      { rationalNum := (cHermiteReduceTower Dt a d).1.1
        rationalDen := (cHermiteReduceTower Dt a d).1.2
        remainderNum := (cHermiteReduceTower Dt a d).2.1
        remainderDen := (cHermiteReduceTower Dt a d).2.2 } :=
  rfl

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- Semantic normal-squarefreeness discharges the repeated-factor gcd frontier of dense Hermite reduction. -/
theorem hcopgcd_of_isNormalSqfree
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt d : DensePoly α) (hd : toPoly d ≠ 0)
    (hnormal : @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (toPoly Dt)⟩ (toPoly d)) :
    ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0 := by
  intro x hx
  have hpp : (toPoly d).primPart ≠ 0 := Polynomial.primPart_ne_zero _
  have hxzip : x ∈ (cSqfreeYunFF d).zipIdx := List.mem_of_mem_filter hx
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hxzip))
  apply natDegree_cgcdWf_eq_zero_of_isCoprime
  simp only [denote]
  refine IsCoprime.mul_left ?_ ?_
  · rw [← hget]
    exact isCoprime_cofactor_yunFactor hgcd d hd hpp x.2 hidx
  · have hsf : Squarefree (toPoly x.1) := by
      rw [← hget]
      exact cSqfreeYunFFG_squarefree hgcd d hd hpp x.2 hidx
    have hpow : toPoly x.1 ^ (x.2 + 1) ∣ toPoly d := by
      rw [← hget, Nat.add_comm]
      exact cSqfreeYunFFG_pow_dvd hgcd d hd hpp x.2 hidx
    have hdvd : toPoly x.1 ∣ toPoly d := by
      have hp := (pow_dvd_pow (toPoly x.1) (show 1 ≤ x.2 + 1 by omega)).trans hpow
      simpa only [pow_one] using hp
    exact (hnormal (toPoly x.1) hsf hdvd).symm

/-- The fraction-free dense Hermite loop realizes the generic Hermite contract. -/
instance instLawfulCHermiteReductionDenseWf
    [hgcdFact : Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))] :
    @LawfulCHermiteReduction DensePoly CPoly.instList α _ _ _ _ _ instEngineList
      (@instCHermiteReductionDense α _ _ inferInstance) where
  rationalDen_nonzero Dt a d hd _ := by
    rw [hermiteResult_dense]
    rw [toPoly_list_eq] at hd
    simpa only [toPoly_list_eq] using
      toPolyG_cHermiteReduceTowerG_den_ne_zero hgcdFact.out Dt a d hd
        (Polynomial.primPart_ne_zero _)
  remainderDen_nonzero Dt a d hd := by
    rw [hermiteResult_dense]
    rw [toPoly_list_eq] at hd
    simpa only [toPoly_list_eq] using
      (toPolyG_cHermiteReduceTowerG_Dstar_monic hgcdFact.out Dt a d hd).ne_zero
  field_identity Dt a d hd hnormal := by
    rw [hermiteResult_dense]
    rw [toPoly_list_eq] at hd
    have hnormal' : @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (toPoly Dt)⟩
        (toPoly d) := by
      rw [← toPoly_list_eq Dt, ← toPoly_list_eq d]
      exact hnormal
    have hcop := hcopgcd_of_isNormalSqfree hgcdFact.out Dt d hd hnormal'
    have hfield := cHermiteReduceTowerG_field_identity hgcdFact.out Dt a d hd
      (Polynomial.primPart_ne_zero _) hcop
    rw [toPolyG_hNum'_eq_2_1 hgcdFact.out Dt a d hd (Polynomial.primPart_ne_zero _) hcop]
      at hfield
    simpa only [towerFractionFieldDerivP, towerFractionFieldDeriv, toPoly_list_eq] using hfield
  remainder_squarefree Dt a d hd := by
    rw [hermiteResult_dense]
    rw [toPoly_list_eq] at hd
    simpa only [toPoly_list_eq] using
      toPolyG_cHermiteReduceTowerG_Dstar_squarefree hgcdFact.out Dt a d hd
        (Polynomial.primPart_ne_zero _)
  remainder_proper Dt a d hd hnormal hproper hdegree := by
    rw [hermiteResult_dense]
    rw [toPoly_list_eq] at hd
    have hnormal' : @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (toPoly Dt)⟩
        (toPoly d) := by
      rw [← toPoly_list_eq Dt, ← toPoly_list_eq d]
      exact hnormal
    have hproper' : (toPoly a).degree < (toPoly d).degree := by
      simpa only [← toPoly_list_eq] using hproper
    have hdegree' : (toPoly Dt).natDegree ≤ 1 := by
      simpa only [← toPoly_list_eq] using hdegree
    simpa only [toPoly_list_eq] using
      hAD_degree_of_hcopgcd hgcdFact.out Dt a d hd (Polynomial.primPart_ne_zero _)
        hdegree' hproper' (hcopgcd_of_isNormalSqfree hgcdFact.out Dt d hd hnormal')

end DeepWiki.SymbolicIntegration
