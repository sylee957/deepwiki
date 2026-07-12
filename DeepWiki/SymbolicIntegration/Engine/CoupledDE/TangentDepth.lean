import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentSpecial
import DeepWiki.SymbolicIntegration.Engine.Tower.LrtDepth
import DeepWiki.SymbolicIntegration.Engine.Tower.RecursiveElementary

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
  /-- Polynomial-reduction stage selected at this depth. -/
  polynomial : CPolynomialReduction DensePoly (DenseFracTower n)
  /-- Monomial kind consumed by the selected polynomial reduction. -/
  kind : PolynomialReductionKind
  /-- Relative-completeness domain of the polynomial stage. -/
  polynomialDomain : PolynomialReductionDomain DensePoly (DenseFracTower n)
  /-- Denotational soundness of the selected polynomial stage. -/
  lawfulPolynomial : LawfulCPolynomialReduction polynomial
  /-- Relative completeness of the selected polynomial stage. -/
  completePolynomial : CompleteCPolynomialReduction polynomial polynomialDomain
  /-- Candidate normal reducer, certified by the tangent-level checker. -/
  normal : CNormalReduction DensePoly (DenseFracTower n)
  /-- Coupled coefficient-system solver for the tangent case. -/
  coupled : CTangentCoefficientSolver (DenseFracTower n)
  /-- Finite bounds used by the recursive tangent special realization. -/
  config : TangentSpecialConfig

/-- Concrete leaves and coefficient recursion selecting one tangent level at dense tower depth `n`. -/
structure DenseTangentLevelCapabilities (n : ℕ) extends DenseTangentLevelLeaves n where
  /-- Elementary integrator used for coefficients at this tower depth. -/
  coefficient : CRecursiveElementaryIntegrator (DenseFracTower n)

/-- The concrete recursive tangent Risch operation selected by one depth capability. -/
noncomputable def denseTangentLevel (C : DenseTangentLevelCapabilities n) :
    CRischLevel DensePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  exact recursiveTangentRischLevel C.polynomial C.kind C.normal C.coupled C.config C.coefficient

/-- The exact composition domain for a selected recursive tangent level. -/
noncomputable def denseTangentLevelDomain (C : DenseTangentLevelCapabilities n) :
    RischLevelDomain DensePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  exact recursiveTangentRischLevelCompleteDomain C.polynomial C.kind C.polynomialDomain C.normal
    C.coupled C.config C.coefficient

/-- A selected dense tangent level is sound solely from its lawful stage contracts. -/
theorem denseTangentLevel_sound (C : DenseTangentLevelCapabilities n) (fuel : ℕ)
    (Dt a d : DensePoly (DenseFracTower n)) (res : IntegralResult (DenseFracTower n))
    (hdomain : oneLevelRischSoundDomain tangentNormalDomain Dt a d)
    (hden : CPoly.toPoly d ≠ 0)
    (hrun : (denseTangentLevel C).integrate fuel Dt a d = some res) :
    IsIntegralResultP Dt a d res := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n) := C.lawfulCanonical
  letI : LawfulCPolynomialReduction C.polynomial := C.lawfulPolynomial
  unfold denseTangentLevel at hrun
  exact (instLawfulCRischLevelRecursiveTangent C.polynomial C.kind C.normal C.coupled C.config C.coefficient).sound
    fuel Dt a d res hdomain hden hrun

/-- Every successful selected dense tangent level returns genuine elementary logarithmic terms. -/
theorem denseTangentLevel_logs_genuine (C : DenseTangentLevelCapabilities n) (fuel : ℕ)
    (Dt a d : DensePoly (DenseFracTower n)) (res : IntegralResult (DenseFracTower n))
    (hdomain : oneLevelRischSoundDomain tangentNormalDomain Dt a d)
    (hden : CPoly.toPoly d ≠ 0)
    (hrun : (denseTangentLevel C).integrate fuel Dt a d = some res) :
    (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0) := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n) :=
    C.lawfulCanonical
  letI : LawfulCPolynomialReduction C.polynomial := C.lawfulPolynomial
  unfold denseTangentLevel at hrun
  constructor
  · exact (instLawfulGenuineCRischLevelRecursiveTangent C.polynomial C.kind C.normal
      C.coupled C.config C.coefficient).coefficients_constant fuel Dt a d res
        hdomain hden hrun
  · exact (instLawfulGenuineCRischLevelRecursiveTangent C.polynomial C.kind C.normal
      C.coupled C.config C.coefficient).arguments_nonzero fuel Dt a d res
        hdomain hden hrun

/-- A selected dense tangent level is relatively complete on its explicit stage domain. -/
theorem denseTangentLevel_complete (C : DenseTangentLevelCapabilities n)
    (Dt a d : DensePoly (DenseFracTower n))
    (hdomain : denseTangentLevelDomain C Dt a d) (hden : CPoly.toPoly d ≠ 0)
    (hintegrable : IsRischLevelIntegrable Dt a d) :
    ∃ fuel res, (denseTangentLevel C).integrate fuel Dt a d = some res := by
  letI : CCanonicalRepresentation DensePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n) := C.lawfulCanonical
  letI : LawfulCPolynomialReduction C.polynomial := C.lawfulPolynomial
  letI : CompleteCPolynomialReduction C.polynomial C.polynomialDomain := C.completePolynomial
  unfold denseTangentLevel denseTangentLevelDomain at *
  exact (instCompleteCRischLevelRecursiveTangent C.polynomial C.kind C.polynomialDomain C.normal
    C.coupled C.config C.coefficient).relative_complete Dt a d hdomain hden hintegrable

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
  letI : LawfulCPolynomialReduction below.polynomial := below.lawfulPolynomial
  letI : CompleteCPolynomialReduction below.polynomial below.polynomialDomain :=
    below.completePolynomial
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
    (Dt a d : DensePoly (DenseFracTower n)) (res : IntegralResult (DenseFracTower n))
    (hdomain : oneLevelRischSoundDomain tangentNormalDomain Dt a d)
    (hden : CPoly.toPoly d ≠ 0)
    (hrun : (denseTangentTower C n).integrate fuel Dt a d = some res) :
    IsIntegralResultP Dt a d res := by
  exact denseTangentLevel_sound (denseTangentTowerCapabilities C n) fuel Dt a d res hdomain hden hrun

/-- Every successful recursively selected dense tangent level returns genuine elementary logarithms. -/
theorem denseTangentTower_logs_genuine (C : DenseTangentTowerCapabilities) (n fuel : ℕ)
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

end DeepWiki.SymbolicIntegration
