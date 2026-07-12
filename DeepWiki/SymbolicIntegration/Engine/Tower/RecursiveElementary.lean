import DeepWiki.SymbolicIntegration.Engine.RischLevel
import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv

/-! # Recursive elementary coefficient adapter

Lifts a dense lower Risch level to coefficient-field elementary integration and certificate-checks
the lifted rational and logarithmic result in the represented fraction field.
-/

namespace DeepWiki.SymbolicIntegration

universe u v

open DensePoly CFrac

variable {β : Type u} [CField β] [CFieldSpec.{u,v} β] [CDiffField β]
  [CDiffFieldSpec.{u,v} β] [CFieldDomain β DensePoly] [Algebra ℚ (CFieldSpec.K β)]

/-- Lift a lower dense Risch result into elementary-antiderivative data over `DenseFrac β`. -/
def liftRischResultToCoefficient (res : IntegralResult β) :
    CoefficientIntegralResult (DenseFrac β) where
  rational := CField.div (CFrac.ofPoly res.rational.1) (CFrac.ofPoly res.rational.2)
  logs := res.logs.map fun cv => (CFrac.ofPoly [cv.1], CFrac.ofPoly cv.2)

/-- Raw coefficient candidate obtained by running a lower dense Risch level with `D(t) = 1`. -/
def recursiveElementaryCandidateOfRischLevel (L : CRischLevel DensePoly β) (fuel : ℕ) :
    CRecursiveElementaryIntegrator (DenseFrac β) where
  integrate c :=
    (L.integrate fuel [CCommRing.one] (CFrac.num c) (CFrac.den c)).map
      liftRischResultToCoefficient

/-- Certificate-checked elementary coefficient integration supplied by a lower dense Risch level. -/
def recursiveElementaryOfRischLevel (L : CRischLevel DensePoly β) (fuel : ℕ) :
    CRecursiveElementaryIntegrator (DenseFrac β) :=
  checkedRecursiveElementaryIntegrator (recursiveElementaryCandidateOfRischLevel L fuel)

/-- The checked lower-level adapter is sound independently of its candidate generator. -/
instance instLawfulCRecursiveElementaryIntegratorOfRischLevel
    (L : CRischLevel DensePoly β) (fuel : ℕ) :
    LawfulCRecursiveElementaryIntegrator (recursiveElementaryOfRischLevel L fuel) := by
  unfold recursiveElementaryOfRischLevel
  infer_instance

/-- Exact executable-acceptance domain of the checked lower-level coefficient adapter. -/
def recursiveElementaryOfRischLevelDomain (L : CRischLevel DensePoly β) (fuel : ℕ) :
    RecursiveElementaryDomain (α := DenseFrac β) := fun c =>
  ∃ res : IntegralResult β,
    L.integrate fuel [CCommRing.one] (CFrac.num c) (CFrac.den c) = some res ∧
      coefficientIntegralResultCheck c (liftRischResultToCoefficient res) = true

/-- Semantic domain where the lower level returns a genuine lifted elementary antiderivative. -/
def recursiveElementaryOfRischLevelSemanticDomain (L : CRischLevel DensePoly β) (fuel : ℕ) :
    RecursiveElementaryDomain (α := DenseFrac β) := fun c =>
  ∃ res : IntegralResult β,
    L.integrate fuel [CCommRing.one] (CFrac.num c) (CFrac.den c) = some res ∧
      IsCoefficientIntegralResult c (liftRischResultToCoefficient res)

/-- The lower-level adapter is relatively complete on its exact certificate-acceptance domain. -/
instance instCompleteCRecursiveElementaryIntegratorOfRischLevel
    (L : CRischLevel DensePoly β) (fuel : ℕ) :
    CompleteCRecursiveElementaryIntegrator (recursiveElementaryOfRischLevel L fuel)
      (recursiveElementaryOfRischLevelDomain L fuel) where
  complete c hdomain _ := by
    obtain ⟨res, hrun, hcheck⟩ := hdomain
    refine ⟨liftRischResultToCoefficient res, ?_⟩
    simp [recursiveElementaryOfRischLevel, checkedRecursiveElementaryIntegrator,
      recursiveElementaryCandidateOfRischLevel, hrun, hcheck]

/-- Semantic lifted-result certificates imply completeness of the checked lower-level adapter. -/
instance instCompleteCRecursiveElementaryIntegratorOfRischLevelSemantic
    (L : CRischLevel DensePoly β) (fuel : ℕ) :
    CompleteCRecursiveElementaryIntegrator (recursiveElementaryOfRischLevel L fuel)
      (recursiveElementaryOfRischLevelSemanticDomain L fuel) where
  complete c hdomain _ := by
    obtain ⟨res, hrun, hresult⟩ := hdomain
    refine ⟨liftRischResultToCoefficient res, ?_⟩
    have hcheck := coefficientIntegralResultCheck_of_isCoefficientIntegralResult c _ hresult
    simp [recursiveElementaryOfRischLevel, checkedRecursiveElementaryIntegrator,
      recursiveElementaryCandidateOfRischLevel, hrun, hcheck]

end DeepWiki.SymbolicIntegration
