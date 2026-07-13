import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentPolynomial
import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentSpecial
import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec
import DeepWiki.SymbolicIntegration.Engine.Tower.Compositional
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.Tower.RecursiveElementary
import DeepWiki.SymbolicIntegration.Engine.CanonicalReconstructionCharZero

/-! # Depth-indexed recursive tangent levels

Selects the generic recursive tangent Risch level at every dense fraction-tower depth. The
coefficient recursion remains an explicit step capability, so no concrete solver leaks into the
generic stage composition.
-/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- Concrete nonrecursive leaves required by one tangent level at dense tower depth `n`. -/
structure DenseTangentLevelLeaves (n : ℕ) where
  /-- Canonical decomposition selected for this coefficient carrier. -/
  canonical : CCanonicalRepresentation DensePoly (DenseFracTower n)
  /-- Denotational contract for the selected canonical decomposition. -/
  lawfulCanonical : let _ : CCanonicalRepresentation DensePoly (DenseFracTower n) := canonical
    LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n)
  /-- Candidate normal reducer, certified by the tangent-level checker. -/
  normal : CNormalReduction DensePoly (DenseFracTower n)
  /-- Coupled coefficient-system solver for the tangent case. -/
  coupled : CTangentCoefficientSolver (DenseFracTower n)

/-- Concrete leaves and coefficient recursion selecting one tangent level at dense tower depth `n`. -/
structure DenseTangentLevelCapabilities (n : ℕ) extends DenseTangentLevelLeaves n where
  /-- Elementary integrator used for coefficients at this tower depth. -/
  coefficient : CRecursiveElementaryIntegrator (DenseFracTower n)

/-- The concrete recursive tangent Risch operation selected by one depth capability. -/
noncomputable def denseTangentLevel (C : DenseTangentLevelCapabilities n) :
    CRischLevel DensePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  exact recursiveTangentRischLevel DensePoly.towerPolynomialReduction .nonlinear C.normal C.coupled
    C.coefficient

/-- The exact composition domain for a selected recursive tangent level. -/
noncomputable def denseTangentLevelDomain (C : DenseTangentLevelCapabilities n) :
    RischLevelDomain DensePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  exact recursiveTangentRischLevelCompleteDomain DensePoly.towerPolynomialReduction .nonlinear
    DensePoly.nonlinearPolynomialReductionDomain C.normal C.coupled C.coefficient

/-- Compositional stage domain for a dense tangent level with explicit solver and coefficient domains. -/
noncomputable def denseTangentLevelCompositionalDomain (C : DenseTangentLevelCapabilities n)
    (solverDomain : TangentCoefficientDomain (α := DenseFracTower n))
    (coefficientDomain : RecursiveElementaryDomain (α := DenseFracTower n)) :
    RischLevelDomain DensePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  exact recursiveTowerTangentRischLevelCompositionalDomain C.normal C.coupled solverDomain
    coefficientDomain

/-- Package a tangent level with its semantic recursive domains as one certified dense tower stage. -/
noncomputable def denseTangentCompositionalStage (C : DenseTangentLevelCapabilities n)
    (solverDomain : TangentCoefficientDomain (α := DenseFracTower n))
    [LawfulCTangentCoefficientSolver C.coupled]
    [CompleteCTangentCoefficientSolver C.coupled solverDomain]
    (coefficientDomain : RecursiveElementaryDomain (α := DenseFracTower n))
    [LawfulCRecursiveElementaryIntegrator C.coefficient]
    [CompleteCRecursiveElementaryIntegrator C.coefficient coefficientDomain] : DenseRischStage n := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n) :=
    C.lawfulCanonical
  let level := denseTangentLevel C
  let domain := denseTangentLevelCompositionalDomain C solverDomain coefficientDomain
  letI : LawfulCRischLevel level domain := by
    dsimp [level, domain]
    unfold denseTangentLevel denseTangentLevelCompositionalDomain
    infer_instance
  letI : LawfulGenuineCRischLevel level domain := by
    dsimp [level, domain]
    unfold denseTangentLevel denseTangentLevelCompositionalDomain
    infer_instance
  letI : CompleteCRischLevel level domain := by
    dsimp [level, domain]
    unfold denseTangentLevel denseTangentLevelCompositionalDomain
    infer_instance
  exact ⟨level, domain, inferInstance, inferInstance, inferInstance⟩

/-- The sparse tangent stage is the certified conversion of the selected dense tangent stage. -/
noncomputable def sparseTangentCompositionalStage (C : DenseTangentLevelCapabilities n)
    (solverDomain : TangentCoefficientDomain (α := DenseFracTower n))
    [LawfulCTangentCoefficientSolver C.coupled]
    [CompleteCTangentCoefficientSolver C.coupled solverDomain]
    (coefficientDomain : RecursiveElementaryDomain (α := DenseFracTower n))
    [LawfulCRecursiveElementaryIntegrator C.coefficient]
    [CompleteCRecursiveElementaryIntegrator C.coefficient coefficientDomain] : SparseRischStage n :=
  (denseTangentCompositionalStage C solverDomain coefficientDomain).toSparse

/-- The canonical decomposition selected by a dense tangent capability. -/
noncomputable def denseTangentCanonicalResult (C : DenseTangentLevelCapabilities n)
    (Dt a d : DensePoly (DenseFracTower n)) : CanonicalRepresentationResult DensePoly
      (DenseFracTower n) := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  exact canonicalResult Dt a d

/-- A tangent monomial puts the dense canonical polynomial branch in the selected nonlinear domain. -/
theorem denseTangentLevel_canonicalPolynomial_domain (C : DenseTangentLevelCapabilities n)
    {Dt a d : DensePoly (DenseFracTower n)} (h : IsTangentMonomial Dt) :
    DensePoly.nonlinearPolynomialReductionDomain .nonlinear Dt
      (denseTangentCanonicalResult C Dt a d).polynomial :=
  h.nonlinearPolynomialReductionDomain

/-- A tangent monomial gives the dense canonical polynomial branch a nonlinear normal form. -/
theorem denseTangentLevel_canonicalPolynomial_reduction_exists (C : DenseTangentLevelCapabilities n)
    {Dt a d : DensePoly (DenseFracTower n)} (h : IsTangentMonomial Dt) :
    ∃ out : PolynomialReductionResult DensePoly (DenseFracTower n),
      IsPolynomialReduction .nonlinear Dt (denseTangentCanonicalResult C Dt a d).polynomial out :=
  h.nonlinearReduction_exists

/-- A selected dense tangent level is sound solely from its lawful stage contracts. -/
theorem denseTangentLevel_sound (C : DenseTangentLevelCapabilities n) (fuel : ℕ)
    [CFracGcdCoreWf (DenseFracTower n)]
    (Dt a d : DensePoly (DenseFracTower n)) (res : IntegralResult (DenseFracTower n))
    (hdomain : oneLevelRischSoundDomain tangentNormalDomain Dt a d)
    (hden : CPoly.toPoly d ≠ 0)
    (hrun : (denseTangentLevel C).integrate fuel Dt a d = some res) :
    IsIntegralResultP Dt a d res := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n) := C.lawfulCanonical
  unfold denseTangentLevel at hrun
  exact (instLawfulCRischLevelRecursiveTangent DensePoly.towerPolynomialReduction .nonlinear
    C.normal C.coupled C.coefficient).sound fuel Dt a d res hdomain hden hrun

/-- Every successful selected dense tangent level returns genuine elementary logarithmic terms. -/
theorem denseTangentLevel_logs_genuine (C : DenseTangentLevelCapabilities n) (fuel : ℕ)
    [CFracGcdCoreWf (DenseFracTower n)]
    (Dt a d : DensePoly (DenseFracTower n)) (res : IntegralResult (DenseFracTower n))
    (hdomain : oneLevelRischSoundDomain tangentNormalDomain Dt a d)
    (hden : CPoly.toPoly d ≠ 0)
    (hrun : (denseTangentLevel C).integrate fuel Dt a d = some res) :
    (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0) := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n) :=
    C.lawfulCanonical
  unfold denseTangentLevel at hrun
  constructor
  · exact (instLawfulGenuineCRischLevelRecursiveTangent DensePoly.towerPolynomialReduction .nonlinear
      C.normal C.coupled C.coefficient).coefficients_constant fuel Dt a d res
        hdomain hden hrun
  · exact (instLawfulGenuineCRischLevelRecursiveTangent DensePoly.towerPolynomialReduction .nonlinear
      C.normal C.coupled C.coefficient).arguments_nonzero fuel Dt a d res
        hdomain hden hrun

/-- A selected dense tangent level is relatively complete on its explicit stage domain. -/
theorem denseTangentLevel_complete (C : DenseTangentLevelCapabilities n)
    (Dt a d : DensePoly (DenseFracTower n))
    (hdomain : denseTangentLevelDomain C Dt a d) (hden : CPoly.toPoly d ≠ 0)
    (hintegrable : IsRischLevelIntegrable Dt a d) :
    ∃ fuel res, (denseTangentLevel C).integrate fuel Dt a d = some res := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n) := C.lawfulCanonical
  unfold denseTangentLevel denseTangentLevelDomain at *
  exact (instCompleteCRischLevelRecursiveTangent DensePoly.towerPolynomialReduction .nonlinear
    DensePoly.nonlinearPolynomialReductionDomain C.normal C.coupled C.coefficient).relative_complete
      Dt a d hdomain hden hintegrable

/-- A dense tangent level is complete on the explicit compositional tangent-special domain. -/
theorem denseTangentLevel_compositional_complete (C : DenseTangentLevelCapabilities n)
    (solverDomain : TangentCoefficientDomain (α := DenseFracTower n))
    [LawfulCTangentCoefficientSolver C.coupled]
    [CompleteCTangentCoefficientSolver C.coupled solverDomain]
    (coefficientDomain : RecursiveElementaryDomain (α := DenseFracTower n))
    [LawfulCRecursiveElementaryIntegrator C.coefficient]
    [CompleteCRecursiveElementaryIntegrator C.coefficient coefficientDomain]
    (Dt a d : DensePoly (DenseFracTower n))
    (hdomain : denseTangentLevelCompositionalDomain C solverDomain coefficientDomain Dt a d)
    (hden : CPoly.toPoly d ≠ 0) (hintegrable : IsRischLevelIntegrable Dt a d) :
    ∃ fuel res, (denseTangentLevel C).integrate fuel Dt a d = some res := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n) := C.lawfulCanonical
  unfold denseTangentLevel denseTangentLevelCompositionalDomain at *
  exact (instCompleteCRischLevelRecursiveTowerTangentCompositional C.normal C.coupled
    solverDomain C.coefficient coefficientDomain).relative_complete Dt a d hdomain hden hintegrable

/-- Build the next tangent capability by certificate-checking the preceding selected Risch level. -/
noncomputable def DenseTangentLevelCapabilities.step (below : DenseTangentLevelCapabilities n)
    (next : DenseTangentLevelLeaves (n + 1)) :
    DenseTangentLevelCapabilities (n + 1) where
  toDenseTangentLevelLeaves := next
  coefficient := recursiveElementaryOfRischLevel (denseTangentLevel below)

/-- Genuine completeness of a selected level makes its successor coefficient adapter eventually succeed. -/
theorem DenseTangentLevelCapabilities.step_coefficient_eventually_succeeds
    (below : DenseTangentLevelCapabilities n) (next : DenseTangentLevelLeaves (n + 1))
    (c : DenseFracTower (n + 1))
    (hdomain : denseTangentLevelDomain below [CCommRing.one] (CFrac.num c) (CFrac.den c))
    (hintegrable : IsRischLevelIntegrable ([CCommRing.one] : DensePoly (DenseFracTower n))
      (CFrac.num c) (CFrac.den c)) :
    ∃ fuel out, ((below.step next).coefficient).integrate fuel c = some out := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := below.canonical
  letI : LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n) :=
    below.lawfulCanonical
  letI : LawfulCRischLevel (denseTangentLevel below) (denseTangentLevelDomain below) := by
    unfold denseTangentLevel denseTangentLevelDomain
    infer_instance
  letI : LawfulGenuineCRischLevel (denseTangentLevel below)
      (denseTangentLevelDomain below) := by
    unfold denseTangentLevel denseTangentLevelDomain
    infer_instance
  letI : CompleteCRischLevel (denseTangentLevel below) (denseTangentLevelDomain below) := by
    unfold denseTangentLevel denseTangentLevelDomain
    infer_instance
  change ∃ fuel out,
    (recursiveElementaryOfRischLevel (denseTangentLevel below)).integrate fuel c = some out
  exact recursiveElementaryOfRischLevel_eventually_succeeds
    (denseTangentLevel below) (denseTangentLevelDomain below) c hdomain hintegrable

/-- Inductive selection data for recursive tangent levels over the dense fraction tower. -/
structure DenseTangentTowerCapabilities where
  /-- The selected constant-field tangent level. -/
  base : DenseTangentLevelCapabilities 0
  /-- Nonrecursive stage leaves selected at each successor depth. -/
  stepLeaves : ∀ n, DenseTangentLevelLeaves (n + 1)

/-- Select recursive tangent capabilities at every dense fraction-tower depth. -/
noncomputable def denseTangentTowerCapabilities (C : DenseTangentTowerCapabilities) :
    (n : ℕ) → DenseTangentLevelCapabilities n
  | 0 => C.base
  | n + 1 =>
      (denseTangentTowerCapabilities C n).step (C.stepLeaves n)

/-- The recursively selected tangent operation at depth `n`. -/
noncomputable def denseTangentTower (C : DenseTangentTowerCapabilities) (n : ℕ) :
    CRischLevel DensePoly (DenseFracTower n) :=
  denseTangentLevel (denseTangentTowerCapabilities C n)

/-- Soundness of the recursively selected tangent level at every tower depth. -/
theorem denseTangentTower_sound (C : DenseTangentTowerCapabilities) (n fuel : ℕ)
    [CFracGcdCoreWf (DenseFracTower n)]
    (Dt a d : DensePoly (DenseFracTower n)) (res : IntegralResult (DenseFracTower n))
    (hdomain : oneLevelRischSoundDomain tangentNormalDomain Dt a d)
    (hden : CPoly.toPoly d ≠ 0)
    (hrun : (denseTangentTower C n).integrate fuel Dt a d = some res) :
    IsIntegralResultP Dt a d res := by
  exact denseTangentLevel_sound (denseTangentTowerCapabilities C n) fuel Dt a d res hdomain hden hrun

/-- Every successful recursively selected dense tangent level returns genuine elementary logarithms. -/
theorem denseTangentTower_logs_genuine (C : DenseTangentTowerCapabilities) (n fuel : ℕ)
    [CFracGcdCoreWf (DenseFracTower n)]
    (Dt a d : DensePoly (DenseFracTower n)) (res : IntegralResult (DenseFracTower n))
    (hdomain : oneLevelRischSoundDomain tangentNormalDomain Dt a d)
    (hden : CPoly.toPoly d ≠ 0)
    (hrun : (denseTangentTower C n).integrate fuel Dt a d = some res) :
    (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0) := by
  exact denseTangentLevel_logs_genuine (denseTangentTowerCapabilities C n)
    fuel Dt a d res hdomain hden hrun

/-- Relative completeness of the recursively selected tangent level at every tower depth. -/
theorem denseTangentTower_complete (C : DenseTangentTowerCapabilities) (n : ℕ)
    (Dt a d : DensePoly (DenseFracTower n))
    (hdomain : denseTangentLevelDomain (denseTangentTowerCapabilities C n) Dt a d)
    (hden : CPoly.toPoly d ≠ 0) (hintegrable : IsRischLevelIntegrable Dt a d) :
    ∃ fuel res, (denseTangentTower C n).integrate fuel Dt a d = some res := by
  exact denseTangentLevel_complete (denseTangentTowerCapabilities C n) Dt a d hdomain hden hintegrable

/-- **Hypertangent sound-and-complete at every tower depth `n`.** Over `DenseFracTower n`, the
recursively-selected hypertangent Risch level is a sound-and-complete decision procedure: a successful
run yields a genuine integral result with genuine logarithmic terms (soundness, on the sound domain),
and every genuinely integrable input succeeds (completeness, on the level domain). The whole-tower §5.10
analogue of `hyperexpRischLevel_succeeds_iff_integrable_tower`, assembled from `denseTangentTower_sound`
/`_logs_genuine`/`_complete`. Soundness and completeness carry their respective domain hypotheses
(the two directions use the sound vs. level domain, as at the primitive capstone). -/
theorem denseTangentTower_soundAndComplete (C : DenseTangentTowerCapabilities) (n : ℕ)
    [CFracGcdCoreWf (DenseFracTower n)]
    (Dt a d : DensePoly (DenseFracTower n)) (hden : CPoly.toPoly d ≠ 0) :
    (∀ fuel res, (denseTangentTower C n).integrate fuel Dt a d = some res →
        oneLevelRischSoundDomain tangentNormalDomain Dt a d →
        IsIntegralResultP Dt a d res ∧
          (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
          (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0)) ∧
      (denseTangentLevelDomain (denseTangentTowerCapabilities C n) Dt a d →
        IsRischLevelIntegrable Dt a d →
        ∃ fuel res, (denseTangentTower C n).integrate fuel Dt a d = some res) :=
  ⟨fun fuel res hrun hdomain =>
      ⟨denseTangentTower_sound C n fuel Dt a d res hdomain hden hrun,
        denseTangentTower_logs_genuine C n fuel Dt a d res hdomain hden hrun⟩,
    fun hdomain hintegrable => denseTangentTower_complete C n Dt a d hdomain hden hintegrable⟩

/-- **Fraction-integrand form** of the whole-tower hypertangent sound-and-complete theorem: at depth
`n`, the integrand is a single `CFrac` fraction `frac` (num + certified-nonzero denom), so no `den ≠ 0`
hypothesis — carried by the fraction. Wraps `denseTangentTower_soundAndComplete`. -/
theorem denseTangentTower_soundAndComplete_frac (C : DenseTangentTowerCapabilities) (n : ℕ)
    {F : (β : Type) → [CField β] → Type} [CFrac F DensePoly] [LawfulCFrac F DensePoly]
    [CFracGcdCoreWf (DenseFracTower n)]
    (Dt : DensePoly (DenseFracTower n)) (frac : F (DenseFracTower n)) :
    (∀ fuel res, (denseTangentTower C n).integrate fuel Dt (CFrac.num frac) (CFrac.den frac) = some res →
        oneLevelRischSoundDomain tangentNormalDomain Dt (CFrac.num frac) (CFrac.den frac) →
        IsIntegralResultP Dt (CFrac.num frac) (CFrac.den frac) res ∧
          (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
          (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0)) ∧
      (denseTangentLevelDomain (denseTangentTowerCapabilities C n) Dt (CFrac.num frac) (CFrac.den frac) →
        IsRischLevelIntegrable Dt (CFrac.num frac) (CFrac.den frac) →
        ∃ fuel res, (denseTangentTower C n).integrate fuel Dt
          (CFrac.num frac) (CFrac.den frac) = some res) :=
  denseTangentTower_soundAndComplete C n Dt (CFrac.num frac) (CFrac.den frac)
    (CFrac.toPoly_den_ne_zero_generic frac)

end DeepWiki.SymbolicIntegration
