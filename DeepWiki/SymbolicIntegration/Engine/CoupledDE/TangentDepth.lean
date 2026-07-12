import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentSpecial
import DeepWiki.SymbolicIntegration.Engine.Tower.LrtDepth

/-! # Depth-indexed recursive tangent levels

Selects the generic recursive tangent Risch level at every dense fraction-tower depth. The
coefficient recursion remains an explicit step capability, so no concrete solver leaks into the
generic stage composition.
-/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- Concrete leaves required to select one recursive tangent level at dense tower depth `n`. -/
structure DenseTangentLevelCapabilities (n : ℕ) where
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

/-- Inductive selection data for recursive tangent levels over the dense fraction tower. -/
structure DenseTangentTowerCapabilities where
  /-- The selected constant-field tangent level. -/
  base : DenseTangentLevelCapabilities 0
  /-- Extend a selected level by choosing the next depth's coefficient operation and stage leaves. -/
  step : ∀ n, DenseTangentLevelCapabilities n → DenseTangentLevelCapabilities (n + 1)

/-- Select recursive tangent capabilities at every dense fraction-tower depth. -/
noncomputable def denseTangentTowerCapabilities (C : DenseTangentTowerCapabilities) :
    (n : ℕ) → DenseTangentLevelCapabilities n
  | 0 => C.base
  | n + 1 => C.step n (denseTangentTowerCapabilities C n)

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

/-- Relative completeness of the recursively selected tangent level at every tower depth. -/
theorem denseTangentTower_complete (C : DenseTangentTowerCapabilities) (n : ℕ)
    (Dt a d : DensePoly (DenseFracTower n))
    (hdomain : denseTangentLevelDomain (denseTangentTowerCapabilities C n) Dt a d)
    (hden : CPoly.toPoly d ≠ 0) (hintegrable : IsRischLevelIntegrable Dt a d) :
    ∃ fuel res, (denseTangentTower C n).integrate fuel Dt a d = some res := by
  exact denseTangentLevel_complete (denseTangentTowerCapabilities C n) Dt a d hdomain hden hintegrable

end DeepWiki.SymbolicIntegration
