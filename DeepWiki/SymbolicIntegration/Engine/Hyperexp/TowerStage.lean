import DeepWiki.SymbolicIntegration.Engine.Hyperexp.RischLevel
import DeepWiki.SymbolicIntegration.Engine.Tower.Compositional

/-! # Hyperexponential stages in finite compositional towers

The semantic hyperexponential Risch level packages directly as one certified dense tower stage at
any depth; its sparse form is then supplied by the common tower adapter.
-/

namespace DeepWiki.SymbolicIntegration

/-- Package a semantic hyperexponential level as a certified dense stage at depth `n`. -/
noncomputable def hyperexpDenseRischStage (n : ℕ)
    (R : CPolynomialReduction DensePoly (DenseFracTower n))
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly (DenseFracTower n))
    [LawfulCPolynomialReduction R] [CompleteCPolynomialReduction R polynomialDomain]
    [CCanonicalRepresentation DensePoly (DenseFracTower n)]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n)]
    [CRischField (DenseFracTower n)] [CRischFieldSpec (DenseFracTower n)]
    [CPolyGcd DensePoly (DenseFracTower n)] [CPolySquarefree DensePoly (DenseFracTower n)]
    [CPolyResultant DensePoly] [CResidueSource DensePoly (DenseFracTower n)]
    (hfield : CRischFieldComplete (DenseFracTower n)) : DenseRischStage n := by
  let level := hyperexpRischLevel R kind
  let domain := hyperexpRischLevelSemanticCompleteDomain R kind polynomialDomain
  letI : LawfulCRischLevel level domain := by
    dsimp only [level, domain]
    infer_instance
  letI : LawfulGenuineCRischLevel level domain := by
    dsimp only [level, domain]
    infer_instance
  letI : CompleteCRischLevel level domain := by
    dsimp only [level, domain]
    exact completeCRischLevelHyperexpSemantic R kind polynomialDomain hfield
  exact ⟨level, domain, inferInstance, inferInstance, inferInstance⟩

/-- **Hyperexponential sound-and-complete at every tower depth `n`.** Over the concrete fraction tower
`DenseFracTower n`, the assembled hyperexponential Risch level succeeds **iff** the input is genuinely
elementary-integrable — the whole-tower form of `hyperexpRischLevel_succeeds_iff_integrable`, at an
arbitrary depth, relative to the field-RDE completeness `CRischFieldComplete (DenseFracTower n)` at that
level (the honest recursion hypothesis, discharged up the tower by the RDE tower-induction). This is the
§5.9 decision procedure holding at *every* level of a mixed transcendental tower, not only the base. -/
theorem hyperexpRischLevel_succeeds_iff_integrable_tower (n : ℕ)
    (R : CPolynomialReduction DensePoly (DenseFracTower n))
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly (DenseFracTower n))
    [LawfulCPolynomialReduction R] [CompleteCPolynomialReduction R polynomialDomain]
    [CCanonicalRepresentation DensePoly (DenseFracTower n)]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n)]
    [CRischField (DenseFracTower n)] [CRischFieldSpec (DenseFracTower n)]
    [CPolyGcd DensePoly (DenseFracTower n)] [CPolySquarefree DensePoly (DenseFracTower n)]
    [CPolyResultant DensePoly] [CResidueSource DensePoly (DenseFracTower n)]
    (hfield : CRischFieldComplete (DenseFracTower n))
    (Dt a d : DensePoly (DenseFracTower n))
    (hdomain : hyperexpRischLevelSemanticCompleteDomain R kind polynomialDomain Dt a d)
    (hd : CPoly.toPoly d ≠ 0) :
    IsRischLevelIntegrable Dt a d ↔
      ∃ fuel res,
        (hyperexpRischLevel (α := DenseFracTower n) R kind).integrate fuel Dt a d = some res :=
  hyperexpRischLevel_succeeds_iff_integrable R kind polynomialDomain hfield Dt a d hdomain hd

/-- The sparse hyperexponential stage is the certified adapter of the selected dense stage. -/
noncomputable def hyperexpSparseRischStage (n : ℕ)
    (R : CPolynomialReduction DensePoly (DenseFracTower n))
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly (DenseFracTower n))
    [LawfulCPolynomialReduction R] [CompleteCPolynomialReduction R polynomialDomain]
    [CCanonicalRepresentation DensePoly (DenseFracTower n)]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n)]
    [CRischField (DenseFracTower n)] [CRischFieldSpec (DenseFracTower n)]
    [CPolyGcd DensePoly (DenseFracTower n)] [CPolySquarefree DensePoly (DenseFracTower n)]
    [CPolyResultant DensePoly] [CResidueSource DensePoly (DenseFracTower n)]
    (hfield : CRischFieldComplete (DenseFracTower n)) : SparseRischStage n :=
  (hyperexpDenseRischStage n R kind polynomialDomain hfield).toSparse

end DeepWiki.SymbolicIntegration
