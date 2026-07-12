import DeepWiki.SymbolicIntegration.Engine.RischLevel
import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv

/-! # Recursive elementary coefficient adapter

Lifts a dense lower Risch level to coefficient-field elementary integration and certificate-checks
the lifted rational and logarithmic result in the represented fraction field.
-/

namespace DeepWiki.SymbolicIntegration

universe u

open DensePoly CFrac Polynomial
open scoped Differential

variable {β : Type u} [CField β] [CFieldSpec.{u,u} β] [CDiffField β]
  [CDiffFieldSpec.{u,u} β] [CFieldDomain β DensePoly] [Algebra ℚ (CFieldSpec.K β)]

/-- Lift a lower dense Risch result into elementary-antiderivative data over `DenseFrac β`. -/
def liftRischResultToCoefficient (res : IntegralResult β) :
    CoefficientIntegralResult (DenseFrac β) where
  rational := CField.div (CFrac.ofPoly res.rational.1) (CFrac.ofPoly res.rational.2)
  logs := res.logs.map fun cv => (CFrac.ofPoly [cv.1], CFrac.ofPoly cv.2)

/-- The iterated `DenseFrac` derivation is the represented tower derivation with `D(t) = 1`. -/
theorem toK_cderiv_denseFrac (x : DenseFrac β) :
    CFieldSpec.toK (CDiffField.cderiv x) =
      towerFractionFieldDerivP ([CCommRing.one] : DensePoly β) (CFieldSpec.toK x) := by
  rw [CDiffFieldSpec.toK_cderiv]
  change extendDeriv (Differential.implicitDeriv
      (CPoly.toPoly (CPoly.one : DensePoly β))) _ =
    towerFractionFieldDerivP ([CCommRing.one] : DensePoly β) _
  rw [towerFractionFieldDerivP]
  rfl

/-- Differentiating an embedded polynomial agrees with the represented monomial derivative. -/
theorem toK_cderiv_denseFrac_ofPoly (p : DensePoly β) :
    CFieldSpec.toK (CDiffField.cderiv (CFrac.ofPoly (F := DenseFrac) p)) =
      CFrac.am β (CPoly.toPoly
        (CPolyEngine.monomialDeriv ([CCommRing.one] : DensePoly β) p)) := by
  rw [toK_cderiv_denseFrac, CFrac.toK_ofPoly, towerFractionFieldDerivP, extendDeriv_algebraMap]
  simp only [CPolyEngine.toPoly_monomialDeriv]

omit [CDiffField β] [CDiffFieldSpec β] [Algebra ℚ (CFieldSpec.K β)] in
/-- A represented dense fraction denotes its numerator divided by its denominator. -/
theorem toK_denseFrac_eq_fieldFrac (x : DenseFrac β) :
    CFieldSpec.toK x = fieldFracP (CFrac.num x) (CFrac.den x) := by
  change CFrac.toRatFunc x = _
  rw [CFrac.toRatFunc_eq_div]

omit [CDiffField β] [CDiffFieldSpec β] [Algebra ℚ (CFieldSpec.K β)] in
/-- The lifted rational part denotes the lower Risch result's represented fraction. -/
theorem toK_liftRischResult_rational (res : IntegralResult β) :
    CFieldSpec.toK (liftRischResultToCoefficient res).rational =
      fieldFracP res.rational.1 res.rational.2 := by
  simp [liftRischResultToCoefficient, fieldFracP, CFieldSpec.toK_div, CFrac.toK_ofPoly]

/-- Lifting lower logarithms preserves their represented logarithmic-derivative sum. -/
theorem coefficientLogSum_liftRischLogs (logs : List (β × DensePoly β)) :
    coefficientLogSum (α := DenseFrac β)
        (logs.map fun cv =>
          (CFrac.ofPoly (F := DenseFrac) [cv.1], CFrac.ofPoly (F := DenseFrac) cv.2)) =
      logResidueSumP ([CCommRing.one] : DensePoly β) logs := by
  induction logs with
  | nil => simp [coefficientLogSum]
  | cons cv rest ih =>
      rw [List.map_cons, coefficientLogSum_cons, logResidueSumP_cons]
      rw [CFrac.toK_ofPoly, toK_cderiv_denseFrac, CFrac.toK_ofPoly,
        towerFractionFieldDerivP_logDeriv, ih]
      simp only [toPoly_list_eq]
      simp

/-- A genuine lower Risch certificate is a genuine elementary coefficient result after lifting. -/
theorem isCoefficientIntegralResult_liftRischResult (c : DenseFrac β) (res : IntegralResult β)
    (hintegral : IsIntegralResultP ([CCommRing.one] : DensePoly β)
      (CFrac.num c) (CFrac.den c) res)
    (hconstants : ∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0)
    (hargs : ∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0) :
    IsCoefficientIntegralResult c (liftRischResultToCoefficient res) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [toK_cderiv_denseFrac, toK_liftRischResult_rational]
    rw [liftRischResultToCoefficient, coefficientLogSum_liftRischLogs,
      toK_denseFrac_eq_fieldFrac]
    exact hintegral
  · intro lifted hlifted
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hlifted
    rw [toK_cderiv_denseFrac_ofPoly]
    rw [CPolyEngine.toPoly_monomialDeriv]
    have hsourceConstant := hconstants source hsource
    have hsingleton : CPoly.toPoly ([source.1] : DensePoly β) =
        Polynomial.C (CFieldSpec.toK source.1) := by
      rw [toPoly_list_eq]
      simp only [denote, mul_zero, add_zero]
    rw [hsingleton]
    have hderivZero : (CFieldSpec.toK source.1)′ = 0 := by
      rw [← CDiffFieldSpec.toK_cderiv]
      exact hsourceConstant
    rw [Differential.implicitDeriv_C, hderivZero]
    rw [Polynomial.C_0]
    exact map_zero (CFrac.am β)
  · intro lifted hlifted
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hlifted
    rw [CFrac.toK_ofPoly]
    exact CFrac.am_ne_zero (hargs source hsource)

/-- Raw coefficient candidate obtained by running a lower dense Risch level with `D(t) = 1`. -/
def recursiveElementaryCandidateOfRischLevel (L : CRischLevel DensePoly β) :
    CRecursiveElementaryIntegrator (DenseFrac β) where
  integrate fuel c :=
    (L.integrate fuel [CCommRing.one] (CFrac.num c) (CFrac.den c)).map
      liftRischResultToCoefficient

/-- Certificate-checked elementary coefficient integration supplied by a lower dense Risch level. -/
def recursiveElementaryOfRischLevel (L : CRischLevel DensePoly β) :
    CRecursiveElementaryIntegrator (DenseFrac β) :=
  checkedRecursiveElementaryIntegrator (recursiveElementaryCandidateOfRischLevel L)

/-- The checked lower-level adapter is sound independently of its candidate generator. -/
instance instLawfulCRecursiveElementaryIntegratorOfRischLevel
    (L : CRischLevel DensePoly β) :
    LawfulCRecursiveElementaryIntegrator (recursiveElementaryOfRischLevel L) := by
  unfold recursiveElementaryOfRischLevel
  infer_instance

/-- Exact executable-acceptance domain of the checked lower-level coefficient adapter. -/
def recursiveElementaryOfRischLevelDomain (L : CRischLevel DensePoly β) :
    RecursiveElementaryDomain (α := DenseFrac β) := fun c =>
  ∃ fuel res,
    L.integrate fuel [CCommRing.one] (CFrac.num c) (CFrac.den c) = some res ∧
      coefficientIntegralResultCheck c (liftRischResultToCoefficient res) = true

/-- Semantic domain where the lower level returns a genuine lifted elementary antiderivative. -/
def recursiveElementaryOfRischLevelSemanticDomain (L : CRischLevel DensePoly β) :
    RecursiveElementaryDomain (α := DenseFrac β) := fun c =>
  ∃ fuel res,
    L.integrate fuel [CCommRing.one] (CFrac.num c) (CFrac.den c) = some res ∧
      IsCoefficientIntegralResult c (liftRischResultToCoefficient res)

/-- Lower-level domain stated entirely in the genuine `IsIntegralResultP` vocabulary. -/
def recursiveElementaryOfRischLevelGenuineDomain (L : CRischLevel DensePoly β) :
    RecursiveElementaryDomain (α := DenseFrac β) := fun c =>
  ∃ fuel res,
    L.integrate fuel [CCommRing.one] (CFrac.num c) (CFrac.den c) = some res ∧
      IsIntegralResultP ([CCommRing.one] : DensePoly β) (CFrac.num c) (CFrac.den c) res ∧
      (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0)

/-- The lower-level adapter is relatively complete on its exact certificate-acceptance domain. -/
instance instCompleteCRecursiveElementaryIntegratorOfRischLevel
    (L : CRischLevel DensePoly β) :
    CompleteCRecursiveElementaryIntegrator (recursiveElementaryOfRischLevel L)
      (recursiveElementaryOfRischLevelDomain L) where
  complete c hdomain _ := by
    obtain ⟨fuel, res, hrun, hcheck⟩ := hdomain
    refine ⟨fuel, liftRischResultToCoefficient res, ?_⟩
    simp [recursiveElementaryOfRischLevel, checkedRecursiveElementaryIntegrator,
      recursiveElementaryCandidateOfRischLevel, hrun, hcheck]

/-- Semantic lifted-result certificates imply completeness of the checked lower-level adapter. -/
instance instCompleteCRecursiveElementaryIntegratorOfRischLevelSemantic
    (L : CRischLevel DensePoly β) :
    CompleteCRecursiveElementaryIntegrator (recursiveElementaryOfRischLevel L)
      (recursiveElementaryOfRischLevelSemanticDomain L) where
  complete c hdomain _ := by
    obtain ⟨fuel, res, hrun, hresult⟩ := hdomain
    refine ⟨fuel, liftRischResultToCoefficient res, ?_⟩
    have hcheck := coefficientIntegralResultCheck_of_isCoefficientIntegralResult c _ hresult
    simp [recursiveElementaryOfRischLevel, checkedRecursiveElementaryIntegrator,
      recursiveElementaryCandidateOfRischLevel, hrun, hcheck]

/-- Genuine lower Risch results make the checked coefficient adapter relatively complete. -/
instance instCompleteCRecursiveElementaryIntegratorOfRischLevelGenuine
    (L : CRischLevel DensePoly β) :
    CompleteCRecursiveElementaryIntegrator (recursiveElementaryOfRischLevel L)
      (recursiveElementaryOfRischLevelGenuineDomain L) where
  complete c hdomain _ := by
    obtain ⟨fuel, res, hrun, hintegral, hconstants, hargs⟩ := hdomain
    refine ⟨fuel, liftRischResultToCoefficient res, ?_⟩
    have hresult := isCoefficientIntegralResult_liftRischResult c res hintegral hconstants hargs
    have hcheck := coefficientIntegralResultCheck_of_isCoefficientIntegralResult c _ hresult
    simp [recursiveElementaryOfRischLevel, checkedRecursiveElementaryIntegrator,
      recursiveElementaryCandidateOfRischLevel, hrun, hcheck]

/-- A complete genuinely lawful lower level eventually supplies an accepted coefficient result. -/
theorem recursiveElementaryOfRischLevel_eventually_succeeds
    (L : CRischLevel DensePoly β) (domain : RischLevelDomain DensePoly β)
    [LawfulCRischLevel L domain] [LawfulGenuineCRischLevel L domain]
    [CompleteCRischLevel L domain]
    (c : DenseFrac β)
    (hdomain : domain [CCommRing.one] (CFrac.num c) (CFrac.den c))
    (hintegrable : IsRischLevelIntegrable ([CCommRing.one] : DensePoly β)
      (CFrac.num c) (CFrac.den c)) :
    ∃ fuel out, (recursiveElementaryOfRischLevel L).integrate fuel c = some out := by
  have hden : CPoly.toPoly (CFrac.den c) ≠ 0 := CFrac.toPoly_den_ne_zero_generic c
  obtain ⟨fuel, res, hrun⟩ := CompleteCRischLevel.relative_complete
    (L := L) (domain := domain) [CCommRing.one] (CFrac.num c) (CFrac.den c)
      hdomain hden hintegrable
  have hintegral := LawfulCRischLevel.sound (L := L) (domain := domain)
    fuel [CCommRing.one] (CFrac.num c) (CFrac.den c) res hdomain hden hrun
  have hconstants := LawfulGenuineCRischLevel.coefficients_constant
    (L := L) (domain := domain) fuel [CCommRing.one] (CFrac.num c) (CFrac.den c) res
      hdomain hden hrun
  have hargs := LawfulGenuineCRischLevel.arguments_nonzero
    (L := L) (domain := domain) fuel [CCommRing.one] (CFrac.num c) (CFrac.den c) res
      hdomain hden hrun
  have hresult := isCoefficientIntegralResult_liftRischResult c res hintegral hconstants hargs
  have hcheck := coefficientIntegralResultCheck_of_isCoefficientIntegralResult c _ hresult
  refine ⟨fuel, liftRischResultToCoefficient res, ?_⟩
  simp [recursiveElementaryOfRischLevel, checkedRecursiveElementaryIntegrator,
    recursiveElementaryCandidateOfRischLevel, hrun, hcheck]

/-- Compositional coefficient domain induced by a lower Risch level: the embedded coefficient lies
in the lower level's domain and has a genuine Liouville-form antiderivative there. -/
def recursiveElementaryOfRischLevelCompositionalDomain
    (domain : RischLevelDomain DensePoly β) : RecursiveElementaryDomain (α := DenseFrac β) := fun c =>
  domain [CCommRing.one] (CFrac.num c) (CFrac.den c) ∧
    IsRischLevelIntegrable ([CCommRing.one] : DensePoly β) (CFrac.num c) (CFrac.den c)

/-- Relative completeness of a genuinely lawful lower Risch level lifts compositionally to its
certificate-checked recursive elementary coefficient adapter. -/
theorem completeCRecursiveElementaryIntegratorOfRischLevelCompositional
    (L : CRischLevel DensePoly β) (domain : RischLevelDomain DensePoly β)
    [LawfulCRischLevel L domain] [LawfulGenuineCRischLevel L domain]
    [CompleteCRischLevel L domain] :
    CompleteCRecursiveElementaryIntegrator (recursiveElementaryOfRischLevel L)
      (recursiveElementaryOfRischLevelCompositionalDomain domain) where
  complete c hdomain _ :=
    recursiveElementaryOfRischLevel_eventually_succeeds L domain c hdomain.1 hdomain.2

end DeepWiki.SymbolicIntegration
