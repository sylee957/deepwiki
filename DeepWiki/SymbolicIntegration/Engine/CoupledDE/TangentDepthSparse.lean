import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentPolynomial
import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentSpecial
import DeepWiki.SymbolicIntegration.Engine.RischLevelConvert
import DeepWiki.SymbolicIntegration.Engine.Tower.LrtDepth
import DeepWiki.SymbolicIntegration.Engine.Tower.RecursiveElementary

/-! # Depth-indexed sparse recursive tangent levels

Selects the generic recursive tangent Risch level at every sparse polynomial boundary of the dense
fraction tower. The lower level is converted to dense only at the `DenseFrac` coefficient adapter,
where represented fractions require dense numerator and denominator polynomials.
-/

namespace DeepWiki.SymbolicIntegration

/-- Concrete nonrecursive leaves required by one sparse tangent level at tower depth `n`. -/
structure SparseTangentLevelLeaves (n : ℕ) where
  /-- Canonical decomposition selected for this coefficient carrier. -/
  canonical : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n)
  /-- Denotational contract for the selected canonical decomposition. -/
  lawfulCanonical : let _ : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := canonical
    LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := DenseFracTower n)
  /-- Candidate normal reducer, certified by the tangent-level checker. -/
  normal : CNormalReduction CPoly.SparsePoly (DenseFracTower n)
  /-- Coupled coefficient-system solver for the tangent case. -/
  coupled : CTangentCoefficientSolver (DenseFracTower n)

/-- Concrete leaves and coefficient recursion selecting one sparse tangent level at tower depth `n`. -/
structure SparseTangentLevelCapabilities (n : ℕ) extends SparseTangentLevelLeaves n where
  /-- Elementary integrator used for coefficients at this tower depth. -/
  coefficient : CRecursiveElementaryIntegrator (DenseFracTower n)

/-- The concrete recursive sparse tangent Risch operation selected by one depth capability. -/
noncomputable def sparseTangentLevel (C : SparseTangentLevelCapabilities n) :
    CRischLevel CPoly.SparsePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  exact sparseRecursiveTangentRischLevel DensePoly.towerPolynomialReduction
    DensePoly.towerPolynomialReduction .nonlinear C.normal C.coupled C.coefficient

/-- The exact composition domain for a selected sparse tangent level. -/
noncomputable def sparseTangentLevelDomain (C : SparseTangentLevelCapabilities n) :
    RischLevelDomain CPoly.SparsePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  exact sparseRecursiveTangentRischLevelCompleteDomain DensePoly.towerPolynomialReduction
    DensePoly.towerPolynomialReduction .nonlinear DensePoly.nonlinearPolynomialReductionDomain
    C.normal C.coupled C.coefficient

/-- Compositional stage domain for a sparse tangent level with explicit recursive subdomains. -/
noncomputable def sparseTangentLevelCompositionalDomain (C : SparseTangentLevelCapabilities n)
    (solverDomain : TangentCoefficientDomain (α := DenseFracTower n))
    (coefficientDomain : RecursiveElementaryDomain (α := DenseFracTower n)) :
    RischLevelDomain CPoly.SparsePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  exact sparseRecursiveTowerTangentRischLevelCompositionalDomain
    DensePoly.towerPolynomialReduction DensePoly.nonlinearPolynomialReductionDomain C.normal C.coupled
    solverDomain coefficientDomain

/-- The canonical decomposition selected by a sparse tangent capability. -/
noncomputable def sparseTangentCanonicalResult (C : SparseTangentLevelCapabilities n)
    (Dt a d : CPoly.SparsePoly (DenseFracTower n)) :
    CanonicalRepresentationResult CPoly.SparsePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  exact canonicalResult Dt a d

/-- A tangent monomial puts the sparse canonical polynomial branch in the selected nonlinear domain. -/
theorem sparseTangentLevel_canonicalPolynomial_domain (C : SparseTangentLevelCapabilities n)
    {Dt a d : CPoly.SparsePoly (DenseFracTower n)} (h : IsTangentMonomial Dt) :
    DensePoly.nonlinearPolynomialReductionDomain .nonlinear Dt
      (sparseTangentCanonicalResult C Dt a d).polynomial :=
  h.nonlinearPolynomialReductionDomain

/-- A tangent monomial gives the sparse canonical polynomial branch a nonlinear normal form. -/
theorem sparseTangentLevel_canonicalPolynomial_reduction_exists
    (C : SparseTangentLevelCapabilities n) {Dt a d : CPoly.SparsePoly (DenseFracTower n)}
    (h : IsTangentMonomial Dt) :
    ∃ out : PolynomialReductionResult CPoly.SparsePoly (DenseFracTower n),
      IsPolynomialReduction .nonlinear Dt (sparseTangentCanonicalResult C Dt a d).polynomial out :=
  h.nonlinearReduction_exists

/-- The soundness domain for a sparse tangent level after installing its canonical stage. -/
noncomputable def sparseTangentLevelSoundDomain (C : SparseTangentLevelCapabilities n) :
    RischLevelDomain CPoly.SparsePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  exact oneLevelRischSoundDomain
    (checkedNormalReductionDomain (P := CPoly.SparsePoly) (α := DenseFracTower n))

/-- A selected sparse tangent level is sound solely from its lawful stage contracts. -/
theorem sparseTangentLevel_sound (C : SparseTangentLevelCapabilities n) (fuel : ℕ)
    (Dt a d : CPoly.SparsePoly (DenseFracTower n))
    (res : IntegralResult (DenseFracTower n) CPoly.SparsePoly)
    (hdomain : sparseTangentLevelSoundDomain C Dt a d)
    (hden : CPoly.toPoly d ≠ 0)
    (hrun : (sparseTangentLevel C).integrate fuel Dt a d = some res) :
    IsIntegralResultP Dt a d res := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := DenseFracTower n) := C.lawfulCanonical
  unfold sparseTangentLevelSoundDomain at hdomain
  unfold sparseTangentLevel at hrun
  exact (instLawfulCRischLevelSparseRecursiveTangent DensePoly.towerPolynomialReduction
    DensePoly.towerPolynomialReduction .nonlinear C.normal C.coupled C.coefficient).sound
      fuel Dt a d res hdomain hden hrun

/-- Every successful selected sparse tangent level returns genuine elementary logarithmic terms. -/
theorem sparseTangentLevel_logs_genuine (C : SparseTangentLevelCapabilities n) (fuel : ℕ)
    (Dt a d : CPoly.SparsePoly (DenseFracTower n))
    (res : IntegralResult (DenseFracTower n) CPoly.SparsePoly)
    (hdomain : sparseTangentLevelSoundDomain C Dt a d)
    (hden : CPoly.toPoly d ≠ 0)
    (hrun : (sparseTangentLevel C).integrate fuel Dt a d = some res) :
    (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0) := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := DenseFracTower n) :=
    C.lawfulCanonical
  unfold sparseTangentLevelSoundDomain at hdomain
  unfold sparseTangentLevel at hrun
  constructor
  · exact (instLawfulGenuineCRischLevelSparseRecursiveTangent DensePoly.towerPolynomialReduction
      DensePoly.towerPolynomialReduction .nonlinear C.normal C.coupled C.coefficient).coefficients_constant
        fuel Dt a d res
        hdomain hden hrun
  · exact (instLawfulGenuineCRischLevelSparseRecursiveTangent DensePoly.towerPolynomialReduction
      DensePoly.towerPolynomialReduction .nonlinear C.normal C.coupled C.coefficient).arguments_nonzero
        fuel Dt a d res
        hdomain hden hrun

/-- A selected sparse tangent level is relatively complete on its explicit stage domain. -/
theorem sparseTangentLevel_complete (C : SparseTangentLevelCapabilities n)
    (Dt a d : CPoly.SparsePoly (DenseFracTower n))
    (hdomain : sparseTangentLevelDomain C Dt a d) (hden : CPoly.toPoly d ≠ 0)
    (hintegrable : IsRischLevelIntegrable Dt a d) :
    ∃ fuel res, (sparseTangentLevel C).integrate fuel Dt a d = some res := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := DenseFracTower n) := C.lawfulCanonical
  unfold sparseTangentLevel sparseTangentLevelDomain at *
  exact (instCompleteCRischLevelSparseRecursiveTangent DensePoly.towerPolynomialReduction
    DensePoly.towerPolynomialReduction .nonlinear DensePoly.nonlinearPolynomialReductionDomain
    C.normal C.coupled C.coefficient).relative_complete Dt a d hdomain hden hintegrable

/-- A sparse tangent level is complete on the transported compositional tangent domain. -/
theorem sparseTangentLevel_compositional_complete (C : SparseTangentLevelCapabilities n)
    (solverDomain : TangentCoefficientDomain (α := DenseFracTower n))
    [LawfulCTangentCoefficientSolver C.coupled]
    [CompleteCTangentCoefficientSolver C.coupled solverDomain]
    (coefficientDomain : RecursiveElementaryDomain (α := DenseFracTower n))
    [LawfulCRecursiveElementaryIntegrator C.coefficient]
    [CompleteCRecursiveElementaryIntegrator C.coefficient coefficientDomain]
    (Dt a d : CPoly.SparsePoly (DenseFracTower n))
    (hdomain : sparseTangentLevelCompositionalDomain C solverDomain coefficientDomain Dt a d)
    (hden : CPoly.toPoly d ≠ 0) (hintegrable : IsRischLevelIntegrable Dt a d) :
    ∃ fuel res, (sparseTangentLevel C).integrate fuel Dt a d = some res := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := DenseFracTower n) :=
    C.lawfulCanonical
  unfold sparseTangentLevel sparseTangentLevelCompositionalDomain at *
  exact (instCompleteCRischLevelSparseRecursiveTowerTangentCompositional
    DensePoly.towerPolynomialReduction DensePoly.nonlinearPolynomialReductionDomain C.normal C.coupled
    solverDomain C.coefficient coefficientDomain).relative_complete Dt a d hdomain hden hintegrable

/-- Build the next sparse tangent capability from the preceding level's dense fraction adapter. -/
noncomputable def SparseTangentLevelCapabilities.step (below : SparseTangentLevelCapabilities n)
    (next : SparseTangentLevelLeaves (n + 1)) :
    SparseTangentLevelCapabilities (n + 1) where
  toSparseTangentLevelLeaves := next
  coefficient := recursiveElementaryOfRischLevel
    (convertRischLevel (Q := DensePoly) (sparseTangentLevel below))

/-- Genuine completeness of a sparse level makes its dense successor coefficient adapter succeed. -/
theorem SparseTangentLevelCapabilities.step_coefficient_eventually_succeeds
    (below : SparseTangentLevelCapabilities n) (next : SparseTangentLevelLeaves (n + 1))
    (c : DenseFracTower (n + 1))
    (hdomain : convertRischLevelDomain (Q := DensePoly) (sparseTangentLevelDomain below)
      [CCommRing.one] (CFrac.num c) (CFrac.den c))
    (hintegrable : IsRischLevelIntegrable ([CCommRing.one] : DensePoly (DenseFracTower n))
      (CFrac.num c) (CFrac.den c)) :
    ∃ fuel out, ((below.step next).coefficient).integrate fuel c = some out := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := below.canonical
  letI : LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := DenseFracTower n) :=
    below.lawfulCanonical
  let sparseLevel := sparseTangentLevel below
  let sparseDomain := sparseTangentLevelDomain below
  letI : LawfulCRischLevel sparseLevel sparseDomain := by
    dsimp [sparseLevel, sparseDomain]
    unfold sparseTangentLevel sparseTangentLevelDomain
    infer_instance
  letI : LawfulGenuineCRischLevel sparseLevel sparseDomain := by
    dsimp [sparseLevel, sparseDomain]
    unfold sparseTangentLevel sparseTangentLevelDomain
    infer_instance
  letI : CompleteCRischLevel sparseLevel sparseDomain := by
    dsimp [sparseLevel, sparseDomain]
    unfold sparseTangentLevel sparseTangentLevelDomain
    infer_instance
  change ∃ fuel out, (recursiveElementaryOfRischLevel
    (convertRischLevel (Q := DensePoly) sparseLevel)).integrate fuel c = some out
  exact recursiveElementaryOfRischLevel_eventually_succeeds
    (convertRischLevel (Q := DensePoly) sparseLevel)
    (convertRischLevelDomain (Q := DensePoly) sparseDomain) c hdomain hintegrable

/-- Inductive selection data for sparse recursive tangent levels over the dense fraction tower. -/
structure SparseTangentTowerCapabilities where
  /-- The selected constant-field sparse tangent level. -/
  base : SparseTangentLevelCapabilities 0
  /-- Nonrecursive stage leaves selected at each successor depth. -/
  stepLeaves : ∀ n, SparseTangentLevelLeaves (n + 1)

/-- Select sparse recursive tangent capabilities at every dense fraction-tower depth. -/
noncomputable def sparseTangentTowerCapabilities (C : SparseTangentTowerCapabilities) :
    (n : ℕ) → SparseTangentLevelCapabilities n
  | 0 => C.base
  | n + 1 =>
      (sparseTangentTowerCapabilities C n).step (C.stepLeaves n)

/-- The recursively selected sparse tangent operation at depth `n`. -/
noncomputable def sparseTangentTower (C : SparseTangentTowerCapabilities) (n : ℕ) :
    CRischLevel CPoly.SparsePoly (DenseFracTower n) :=
  sparseTangentLevel (sparseTangentTowerCapabilities C n)

/-- Soundness of the recursively selected sparse tangent level at every tower depth. -/
theorem sparseTangentTower_sound (C : SparseTangentTowerCapabilities) (n fuel : ℕ)
    (Dt a d : CPoly.SparsePoly (DenseFracTower n))
    (res : IntegralResult (DenseFracTower n) CPoly.SparsePoly)
    (hdomain : sparseTangentLevelSoundDomain (sparseTangentTowerCapabilities C n) Dt a d)
    (hden : CPoly.toPoly d ≠ 0)
    (hrun : (sparseTangentTower C n).integrate fuel Dt a d = some res) :
    IsIntegralResultP Dt a d res := by
  exact sparseTangentLevel_sound (sparseTangentTowerCapabilities C n) fuel Dt a d res hdomain hden hrun

/-- Every successful recursively selected sparse tangent level returns genuine elementary logarithms. -/
theorem sparseTangentTower_logs_genuine (C : SparseTangentTowerCapabilities) (n fuel : ℕ)
    (Dt a d : CPoly.SparsePoly (DenseFracTower n))
    (res : IntegralResult (DenseFracTower n) CPoly.SparsePoly)
    (hdomain : sparseTangentLevelSoundDomain (sparseTangentTowerCapabilities C n) Dt a d)
    (hden : CPoly.toPoly d ≠ 0)
    (hrun : (sparseTangentTower C n).integrate fuel Dt a d = some res) :
    (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0) := by
  exact sparseTangentLevel_logs_genuine (sparseTangentTowerCapabilities C n)
    fuel Dt a d res hdomain hden hrun

/-- Relative completeness of the recursively selected sparse tangent level at every tower depth. -/
theorem sparseTangentTower_complete (C : SparseTangentTowerCapabilities) (n : ℕ)
    (Dt a d : CPoly.SparsePoly (DenseFracTower n))
    (hdomain : sparseTangentLevelDomain (sparseTangentTowerCapabilities C n) Dt a d)
    (hden : CPoly.toPoly d ≠ 0) (hintegrable : IsRischLevelIntegrable Dt a d) :
    ∃ fuel res, (sparseTangentTower C n).integrate fuel Dt a d = some res := by
  exact sparseTangentLevel_complete (sparseTangentTowerCapabilities C n) Dt a d hdomain hden hintegrable

end DeepWiki.SymbolicIntegration
