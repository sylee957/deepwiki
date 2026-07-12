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
  /-- Polynomial-reduction stage selected at this depth. -/
  polynomial : CPolynomialReduction CPoly.SparsePoly (DenseFracTower n)
  /-- Monomial kind consumed by the selected polynomial reduction. -/
  kind : PolynomialReductionKind
  /-- Relative-completeness domain of the polynomial stage. -/
  polynomialDomain : PolynomialReductionDomain CPoly.SparsePoly (DenseFracTower n)
  /-- Denotational soundness of the selected polynomial stage. -/
  lawfulPolynomial : LawfulCPolynomialReduction polynomial
  /-- Relative completeness of the selected polynomial stage. -/
  completePolynomial : CompleteCPolynomialReduction polynomial polynomialDomain
  /-- Candidate normal reducer, certified by the tangent-level checker. -/
  normal : CNormalReduction CPoly.SparsePoly (DenseFracTower n)
  /-- Coupled coefficient-system solver for the tangent case. -/
  coupled : CTangentCoefficientSolver (DenseFracTower n)
  /-- Finite bounds used by the recursive tangent special realization. -/
  config : TangentSpecialConfig

/-- Concrete leaves and coefficient recursion selecting one sparse tangent level at tower depth `n`. -/
structure SparseTangentLevelCapabilities (n : ℕ) extends SparseTangentLevelLeaves n where
  /-- Elementary integrator used for coefficients at this tower depth. -/
  coefficient : CRecursiveElementaryIntegrator (DenseFracTower n)

/-- The concrete recursive sparse tangent Risch operation selected by one depth capability. -/
noncomputable def sparseTangentLevel (C : SparseTangentLevelCapabilities n) :
    CRischLevel CPoly.SparsePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  exact sparseRecursiveTangentRischLevel C.polynomial C.kind C.normal C.coupled C.config C.coefficient

/-- The exact composition domain for a selected sparse tangent level. -/
noncomputable def sparseTangentLevelDomain (C : SparseTangentLevelCapabilities n) :
    RischLevelDomain CPoly.SparsePoly (DenseFracTower n) := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  exact sparseRecursiveTangentRischLevelCompleteDomain C.polynomial C.kind C.polynomialDomain C.normal
    C.coupled C.config C.coefficient

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
  letI : LawfulCPolynomialReduction C.polynomial := C.lawfulPolynomial
  unfold sparseTangentLevelSoundDomain at hdomain
  unfold sparseTangentLevel at hrun
  exact (instLawfulCRischLevelSparseRecursiveTangent C.polynomial C.kind C.normal C.coupled C.config
    C.coefficient).sound fuel Dt a d res hdomain hden hrun

/-- A selected sparse tangent level is relatively complete on its explicit stage domain. -/
theorem sparseTangentLevel_complete (C : SparseTangentLevelCapabilities n)
    (Dt a d : CPoly.SparsePoly (DenseFracTower n))
    (hdomain : sparseTangentLevelDomain C Dt a d) (hden : CPoly.toPoly d ≠ 0)
    (hintegrable : IsRischLevelIntegrable Dt a d) :
    ∃ fuel res, (sparseTangentLevel C).integrate fuel Dt a d = some res := by
  letI : CCanonicalRepresentation CPoly.SparsePoly (DenseFracTower n) := C.canonical
  letI : LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := DenseFracTower n) := C.lawfulCanonical
  letI : LawfulCPolynomialReduction C.polynomial := C.lawfulPolynomial
  letI : CompleteCPolynomialReduction C.polynomial C.polynomialDomain := C.completePolynomial
  unfold sparseTangentLevel sparseTangentLevelDomain at *
  exact (instCompleteCRischLevelSparseRecursiveTangent C.polynomial C.kind C.polynomialDomain C.normal
    C.coupled C.config C.coefficient).relative_complete Dt a d hdomain hden hintegrable

/-- Build the next sparse tangent capability from the preceding level's dense fraction adapter. -/
noncomputable def SparseTangentLevelCapabilities.step (below : SparseTangentLevelCapabilities n)
    (fuel : ℕ) (next : SparseTangentLevelLeaves (n + 1)) :
    SparseTangentLevelCapabilities (n + 1) where
  toSparseTangentLevelLeaves := next
  coefficient := recursiveElementaryOfRischLevel
    (convertRischLevel (Q := DensePoly) (sparseTangentLevel below)) fuel

/-- Inductive selection data for sparse recursive tangent levels over the dense fraction tower. -/
structure SparseTangentTowerCapabilities where
  /-- The selected constant-field sparse tangent level. -/
  base : SparseTangentLevelCapabilities 0
  /-- Search budget passed to the preceding Risch level at each successor depth. -/
  coefficientFuel : ℕ → ℕ
  /-- Nonrecursive stage leaves selected at each successor depth. -/
  stepLeaves : ∀ n, SparseTangentLevelLeaves (n + 1)

/-- Select sparse recursive tangent capabilities at every dense fraction-tower depth. -/
noncomputable def sparseTangentTowerCapabilities (C : SparseTangentTowerCapabilities) :
    (n : ℕ) → SparseTangentLevelCapabilities n
  | 0 => C.base
  | n + 1 =>
      (sparseTangentTowerCapabilities C n).step (C.coefficientFuel n) (C.stepLeaves n)

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

/-- Relative completeness of the recursively selected sparse tangent level at every tower depth. -/
theorem sparseTangentTower_complete (C : SparseTangentTowerCapabilities) (n : ℕ)
    (Dt a d : CPoly.SparsePoly (DenseFracTower n))
    (hdomain : sparseTangentLevelDomain (sparseTangentTowerCapabilities C n) Dt a d)
    (hden : CPoly.toPoly d ≠ 0) (hintegrable : IsRischLevelIntegrable Dt a d) :
    ∃ fuel res, (sparseTangentTower C n).integrate fuel Dt a d = some res := by
  exact sparseTangentLevel_complete (sparseTangentTowerCapabilities C n) Dt a d hdomain hden hintegrable

end DeepWiki.SymbolicIntegration
