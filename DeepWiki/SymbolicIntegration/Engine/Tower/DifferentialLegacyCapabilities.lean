import DeepWiki.SymbolicIntegration.Engine.Tower.DifferentialTranscendental

/-! # Legacy engine parts as an explicit-differential capability bundle

The presentation-indexed contract consumes a `DifferentialOneLevelCapabilities` bundle at each
depth.  This module assembles that bundle from the existing (implicit-`CDiffField`) engine
operations through the certified `.ofLegacy` adapters, in the `ofCDiffField` differential context.

The construction is deliberately restricted to the legacy `t′ = 1` derivative: the five adapters
promote solvers written against the global `[CDiffField]` differential, so the resulting bundle is
sound only where the selected coefficient derivative is the inherited one.  It is the concrete
inhabitant that makes the all-primitive presentation an actual integration level rather than only a
structural interface, and it matches the explicit engine data consumed by the static dense stage.
-/

namespace DeepWiki.SymbolicIntegration

open DynamicPolynomialReduction

universe u

variable {α : Type u} [CField α] [CFieldSpec.{u,u} α] [CDiffField α] [CDiffFieldSpec α]
variable [Algebra ℚ (CFieldSpec.K α)]

/-- The checked dynamic polynomial reducer is lawful in the legacy `ofCDiffField` context. -/
@[reducible] noncomputable def checkedLawfulOfCDiffField :
    LawfulCDifferentialPolynomialReduction (P := DensePoly)
      (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)).derivation
      (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)).differential
      (checked (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)).derivation) := by
  letI : LawfulCFieldDerivation α
      (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)).derivation
      (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)).differential :=
    LawfulCFieldDerivation.ofCDiffField α
  exact checkedLawful _ _

/-- Assemble a full one-level capability bundle in the legacy `ofCDiffField` context.

The polynomial branch is the checked dynamic reducer; its completeness domain is supplied
explicitly because no global relative-completeness theorem is available for it.  The special,
normal, and postprocessor branches are promoted from a legacy `CMonomialCase`/`CNormalReduction`
through the certified `.ofLegacy` adapters, and the canonical split from a legacy
`CCanonicalRepresentation`. -/
noncomputable def DifferentialOneLevelCapabilities.ofLegacy
    (M : CMonomialCase DensePoly α) (N : CNormalReduction DensePoly α)
    (specialDomain : MonomialSpecialDomain DensePoly α)
    (normalDomain : NormalReductionDomain DensePoly α)
    (polynomialDomain : DifferentialPolynomialReductionDomain DensePoly α)
    [CCanonicalRepresentation DensePoly α] [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)]
    [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M] [CompleteCMonomialCase M specialDomain]
    [LawfulCNormalReduction N normalDomain] [LawfulGenuineCNormalReduction N normalDomain]
    [CompleteCNormalReduction N normalDomain]
    (polynomialComplete :
      letI : LawfulCDifferentialPolynomialReduction (P := DensePoly)
          (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)).derivation
          (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)).differential
          (checked (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)).derivation) :=
        checkedLawfulOfCDiffField
      CompleteCDifferentialPolynomialReduction (P := DensePoly)
        (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)).derivation
        (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)).differential
        (checked (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)).derivation)
        polynomialDomain) :
    DifferentialOneLevelCapabilities
      (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := α)) :=
  { canonical := CCanonicalRepresentation.asDifferential (P := DensePoly) (α := α)
    canonicalLawful := LawfulCDifferentialCanonicalRepresentation.ofLegacy (P := DensePoly) (α := α)
    polynomial := checked _
    polynomialDomain := polynomialDomain
    polynomialLawful := checkedLawfulOfCDiffField
    polynomialComplete := polynomialComplete
    special := CMonomialCase.asDifferentialSpecial M
    specialDomain := specialDomain
    specialLawful := LawfulCDifferentialMonomialSpecial.ofLegacy M
    specialComplete := CompleteCDifferentialMonomialSpecial.ofLegacy M specialDomain
    normal := CNormalReduction.asDifferential N
    normalDomain := normalDomain
    normalLawful := LawfulCDifferentialNormalReduction.ofLegacy N normalDomain
    normalComplete := CompleteCDifferentialNormalReduction.ofLegacy N normalDomain
    postprocessor := CMonomialCase.asDifferentialNormalPostprocessor M
    postprocessorLawful := LawfulCDifferentialNormalPostprocessor.ofLegacy M
    postprocessorComplete := CompleteCDifferentialNormalPostprocessor.ofLegacy M specialDomain }

/-! ## Inhabiting the all-primitive presentation

The all-primitive presentation `DifferentialTowerPresentation.primitive N` selects the inherited
`t′ = 1` derivative at every depth, so its context reduces definitionally to `ofCDiffField`.  The
legacy capability bundle therefore builds a genuine presentation-indexed level through the common
`ofCapabilities` composition, with no reliance on the `asPrimitivePresentationLevel` compatibility
shim.  The required engine data is exactly what the static dense stage already consumes. -/

/-- The all-primitive presentation context at any depth is the legacy `ofCDiffField` context. -/
theorem primitive_context_eq (N n : ℕ) (hn : n ≤ N) :
    (DifferentialTowerPresentation.primitive N).context n hn =
      MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := DenseFracTower n) :=
  rfl

/-- Build an all-primitive presentation level at depth `n` from legacy engine data.

This is the genuine composition path: the five certified branches are assembled by
`DifferentialOneLevelCapabilities.ofLegacy` and installed through
`DifferentialTranscendentalLevel.ofCapabilities`, selecting the primitive `t′ = 1` derivative.  It
inhabits the common contract for the primitive presentation without the static-stage shim. -/
noncomputable def primitivePresentationLevel (N n : ℕ) (hn : n ≤ N)
    (M : CMonomialCase DensePoly (DenseFracTower n))
    (Nrm : CNormalReduction DensePoly (DenseFracTower n))
    (specialDomain : MonomialSpecialDomain DensePoly (DenseFracTower n))
    (normalDomain : NormalReductionDomain DensePoly (DenseFracTower n))
    (polynomialDomain : DifferentialPolynomialReductionDomain DensePoly (DenseFracTower n))
    (kind : PolynomialReductionKind)
    [CCanonicalRepresentation DensePoly (DenseFracTower n)]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n)]
    [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M] [CompleteCMonomialCase M specialDomain]
    [LawfulCNormalReduction Nrm normalDomain] [LawfulGenuineCNormalReduction Nrm normalDomain]
    [CompleteCNormalReduction Nrm normalDomain]
    (polynomialComplete :
      letI : LawfulCDifferentialPolynomialReduction (P := DensePoly)
          (MonomialDifferentialContext.ofCDiffField
            (P := DensePoly) (α := DenseFracTower n)).derivation
          (MonomialDifferentialContext.ofCDiffField
            (P := DensePoly) (α := DenseFracTower n)).differential
          (checked (MonomialDifferentialContext.ofCDiffField
            (P := DensePoly) (α := DenseFracTower n)).derivation) :=
        checkedLawfulOfCDiffField
      CompleteCDifferentialPolynomialReduction (P := DensePoly)
        (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := DenseFracTower n)).derivation
        (MonomialDifferentialContext.ofCDiffField
          (P := DensePoly) (α := DenseFracTower n)).differential
        (checked (MonomialDifferentialContext.ofCDiffField
          (P := DensePoly) (α := DenseFracTower n)).derivation)
        polynomialDomain) :
    DifferentialTranscendentalLevel (DifferentialTowerPresentation.primitive N) n hn :=
  DifferentialTranscendentalLevel.ofCapabilities (DifferentialTowerPresentation.primitive N) n hn
    (DifferentialOneLevelCapabilities.ofLegacy M Nrm specialDomain normalDomain polynomialDomain
      polynomialComplete)
    kind

/-- A finite all-primitive presentation tower built from a per-depth primitive-level builder.

Because the primitive presentation ignores its predecessor's derivative (each level uses the same
inherited `t′ = 1`), the successor step reconstructs the level directly from the supplied depth
builder.  The resulting `DifferentialTranscendentalTowerScheme` exposes finite-tower soundness and
relative completeness for the primitive presentation through the common induction theorems.

The builder supplies each level through the certified composition (`primitivePresentationLevel`), so
the whole tower is inhabited without the static-stage shim. -/
noncomputable def primitivePresentationTowerScheme (N : ℕ)
    (level : ∀ n (hn : n ≤ N),
      DifferentialTranscendentalLevel (DifferentialTowerPresentation.primitive N) n hn) :
    DifferentialTranscendentalTowerScheme (DifferentialTowerPresentation.primitive N) where
  base := level 0 (Nat.zero_le N)
  step n hn _ := level (n + 1) hn

/-! ## The completion contract, restated for the inhabited primitive tower

The following anonymous examples pin the required end state against its intended meaning: an
inhabited all-primitive tower's accepted results satisfy the selected differential identity with
constant logarithmic coefficients and nonzero logarithmic arguments, and its local relative-
completeness assumptions compose to a single finite-tower completeness statement. -/

/-- Finite-tower soundness: every accepted result at every depth satisfies the selected
differential identity and the genuine-log conditions (`IsPresentationIntegralResult` unfolds to
exactly the differential identity ∧ logs-constant ∧ arguments-nonzero triple). -/
example (N : ℕ)
    (level : ∀ n (hn : n ≤ N),
      DifferentialTranscendentalLevel (DifferentialTowerPresentation.primitive N) n hn)
    (n : ℕ) (hn : n ≤ N) (fuel : ℕ)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (result : RemainderResult (IntegralResult (DenseFracTower n)) (Unit × Unit))
    (hdomain :
      ((primitivePresentationTowerScheme N level).level n hn).stage.stage.domain input)
    (hrun :
      ((primitivePresentationTowerScheme N level).level n hn).stage.stage.run fuel input =
        some result) :
    IsPresentationIntegralResult (DifferentialTowerPresentation.primitive N) n hn input
      result.output :=
  (primitivePresentationTowerScheme N level).stage_sound n hn fuel input result hdomain hrun

/-- Finite-tower relative completeness: every in-domain integrable input eventually succeeds, so
the composed local completeness assumptions yield tower completeness. -/
example (N : ℕ)
    (level : ∀ n (hn : n ≤ N),
      DifferentialTranscendentalLevel (DifferentialTowerPresentation.primitive N) n hn)
    (n : ℕ) (hn : n ≤ N)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (hdomain :
      ((primitivePresentationTowerScheme N level).level n hn).stage.stage.domain input)
    (hintegrable : ((primitivePresentationTowerScheme N level).level n hn).Integrable input) :
    ∃ fuel result,
      ((primitivePresentationTowerScheme N level).level n hn).stage.stage.run fuel input =
        some result :=
  (primitivePresentationTowerScheme N level).stage_complete n hn input hdomain hintegrable

/-- The primitive presentation instantiates the common contract at `t′ = 1`: the selected monomial
derivative is the unit polynomial at every successor. -/
example (N n : ℕ) (hn : n + 1 ≤ N) :
    (DifferentialTowerPresentation.primitive N).monomialDerivative n hn = CPoly.one :=
  rfl

/-! ## The exponential and tangent presentations instantiate the same contract

The three selected derivatives share the one presentation-indexed interface.  Given the certified
base and top levels — the differential-explicit monomial solvers for `t′ = t` and `t′ = t² + 1` are
the remaining engine content, supplied here as hypotheses — the common `oneStepScheme` builds a
`DifferentialTranscendentalTowerScheme` whose soundness and completeness are the same composition
theorems the primitive tower uses.  The selected monomial derivative is `t` (resp. `t² + 1`), never
silently `1`. -/

/-- The exponential presentation selects `t′ = t`, and its one-step scheme is sound through the
common composition theorem. -/
example
    (base : DifferentialTranscendentalLevel DifferentialTowerPresentation.exponentialOneStep 0
      (Nat.zero_le 1))
    (top : DifferentialTranscendentalLevel DifferentialTowerPresentation.exponentialOneStep 1
      (Nat.le_refl 1))
    (n : ℕ) (hn : n ≤ 1) (fuel : ℕ)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (result : RemainderResult (IntegralResult (DenseFracTower n)) (Unit × Unit))
    (hdomain :
      ((exponentialOneStepScheme base top).level n hn).stage.stage.domain input)
    (hrun :
      ((exponentialOneStepScheme base top).level n hn).stage.stage.run fuel input = some result) :
    IsPresentationIntegralResult DifferentialTowerPresentation.exponentialOneStep n hn input
      result.output :=
  (exponentialOneStepScheme base top).stage_sound n hn fuel input result hdomain hrun

/-- The exponential monomial derivative is `t` (the polynomial `[0, 1]`), not `1`. -/
example (hn : (0 : ℕ) + 1 ≤ 1) :
    DifferentialTowerPresentation.exponentialOneStep.monomialDerivative 0 hn = ([0, 1] : DensePoly ℚ) :=
  rfl

/-- The tangent presentation selects `t′ = t² + 1`, and its one-step scheme is relatively complete
through the common composition theorem. -/
example
    (base : DifferentialTranscendentalLevel DifferentialTowerPresentation.tangentOneStep 0
      (Nat.zero_le 1))
    (top : DifferentialTranscendentalLevel DifferentialTowerPresentation.tangentOneStep 1
      (Nat.le_refl 1))
    (n : ℕ) (hn : n ≤ 1)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (hdomain : ((tangentOneStepScheme base top).level n hn).stage.stage.domain input)
    (hintegrable : ((tangentOneStepScheme base top).level n hn).Integrable input) :
    ∃ fuel result,
      ((tangentOneStepScheme base top).level n hn).stage.stage.run fuel input = some result :=
  (tangentOneStepScheme base top).stage_complete n hn input hdomain hintegrable

/-- The tangent monomial derivative is `t² + 1` (the polynomial `[1, 0, 1]`), not `1`. -/
example (hn : (0 : ℕ) + 1 ≤ 1) :
    DifferentialTowerPresentation.tangentOneStep.monomialDerivative 0 hn =
      ([1, 0, 1] : DensePoly ℚ) :=
  rfl

end DeepWiki.SymbolicIntegration
