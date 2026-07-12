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
