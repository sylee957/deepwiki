import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LazardRiobooTragerCorrectness

/-! # The Rothstein–Trager instance-boundary record

`RtData` bundles everything a downstream engine consumes about the residue gcd at a
residue candidate — the gcd value, its nonzeroness, its degree as the residue
multiplicity, the degree bound, and the similarity of the specialized LRT output branch.
The record is produced here, in the abstract layer's own instance context, so engines
never re-elaborate `gcd` against foreign `Decidable` instances. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial

variable {K : Type*} [Field K]

open scoped Classical in
/-- The instance-boundary record for the LRT output at a residue candidate `a`: a gcd
value that is nonzero, of degree the residue multiplicity (bounded by `deg D`), with the
specialized LRT output branch similar to it. -/
structure RtData (A D : K[X]) (a : K) where
  /-- The residue gcd. -/
  gcdVal : K[X]
  /-- The residue gcd is nonzero. -/
  ne_zero : gcdVal ≠ 0
  /-- The residue gcd's degree is the residue multiplicity. -/
  natDegree_eq : gcdVal.natDegree = (rtResultant A D).rootMultiplicity a
  /-- The residue gcd's degree is bounded by `deg D`. -/
  natDegree_le : gcdVal.natDegree ≤ D.natDegree
  /-- The specialized LRT output branch is similar to the residue gcd. -/
  output_sim : IsSimilar
    ((if (rtResultant A D).rootMultiplicity a = D.natDegree then D.map (C : K →+* K[X])
      else lrtSubresultant A D ((rtResultant A D).rootMultiplicity a)).map
      (Polynomial.evalRingHom a))
    gcdVal

open scoped Classical in
/-- Produce the instance-boundary record from separability and properness: the gcd value
is the baked residue gcd `rtLogGcd A D a`. -/
noncomputable def rtData [IsAlgClosed K] (A D : K[X]) (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) (a : K) : RtData A D a := by
  have hD0 : D ≠ 0 := fun h => by simp [h] at hA
  have hdeg : (rtLogGcd A D a).natDegree = (rtResultant A D).rootMultiplicity a := by
    rw [rtLogGcd]
    exact (rootMultiplicity_rtResultant_eq_natDegree_gcd A D hD hA a).symm
  refine ⟨rtLogGcd A D a, ?_, hdeg, ?_, ?_⟩
  · rw [rtLogGcd]
    intro h0
    exact hD0 ((gcd_eq_zero_iff _ _).mp h0).1
  · rw [hdeg]
    exact rootMultiplicity_rtResultant_le A D hD hA a
  · rw [rtLogGcd]
    exact lazardRiobooTrager_output_isSimilar_gcd A D hD hA a

open scoped Classical in
/-- The produced record's gcd value is the baked residue gcd, definitionally. -/
theorem rtData_gcdVal [IsAlgClosed K] (A D : K[X]) (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) (a : K) :
    (rtData A D hD hA a).gcdVal = rtLogGcd A D a := rfl

open scoped Classical in
/-- Record satellite: the residue multiplicity is at most `deg D`. -/
theorem RtData.rootMultiplicity_le {A D : K[X]} {a : K} (r : RtData A D a) :
    (rtResultant A D).rootMultiplicity a ≤ D.natDegree := by
  rw [← r.natDegree_eq]
  exact r.natDegree_le

end DeepWiki.SymbolicIntegration
