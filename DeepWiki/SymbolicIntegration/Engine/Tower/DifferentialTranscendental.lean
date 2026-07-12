import DeepWiki.SymbolicIntegration.Engine.DifferentialOneLevel
import DeepWiki.SymbolicIntegration.Engine.Tower.RecursiveMonomialDifferential

/-! # Presentation-indexed compositional transcendental towers

The legacy tower result fixes constants through the global `[CDiffField]` derivative.  This module
instead indexes every level contract by a `DifferentialTowerPresentation`, so primitive,
exponential, and tangent extensions retain their selected derivative throughout finite-tower
soundness and relative-completeness recursion.
-/

namespace DeepWiki.SymbolicIntegration

/-- The explicit differential context selected by a finite tower presentation at one depth. -/
noncomputable def DifferentialTowerPresentation.context
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N) :
    MonomialDifferentialContext (P := DensePoly) (DenseFracTower n) :=
  MonomialDifferentialContext.ofTowerPresentation T n hn

/-- A genuine one-level result interpreted with the derivative selected at its tower depth. -/
def IsPresentationIntegralResult (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (result : IntegralResult (DenseFracTower n)) : Prop :=
  IsGenuineDifferentialOneLevelResult (T.context n hn) input.toOneLevelInput result

/-- The executable capabilities and local proofs needed by one explicit-differential level. -/
structure DifferentialOneLevelCapabilities
    {α : Type u} [CField α] [CFieldSpec.{u,u} α]
    (C : MonomialDifferentialContext (P := DensePoly) α) where
  /-- Canonically split the input into polynomial, special, and normal branches. -/
  canonical : CDifferentialCanonicalRepresentation DensePoly α C.derivation
  /-- The canonical split reconstructs its source fraction and preserves denominator certificates. -/
  canonicalLawful :
    letI : CDifferentialCanonicalRepresentation DensePoly α C.derivation := canonical
    LawfulCDifferentialCanonicalRepresentation C
  /-- Reduce the polynomial branch for the selected coefficient derivative. -/
  polynomial : DynamicPolynomialReduction.CDifferentialPolynomialReduction DensePoly α C.derivation
  /-- The semantic domain on which polynomial reduction is relatively complete. -/
  polynomialDomain : DynamicPolynomialReduction.DifferentialPolynomialReductionDomain DensePoly α
  /-- The polynomial reduction output satisfies its selected differential identity. -/
  polynomialLawful :
    DynamicPolynomialReduction.LawfulCDifferentialPolynomialReduction C.derivation C.differential polynomial
  /-- Polynomial reduction is relatively complete on its selected domain. -/
  polynomialComplete :
    letI : DynamicPolynomialReduction.LawfulCDifferentialPolynomialReduction
      C.derivation C.differential polynomial :=
      polynomialLawful
    DynamicPolynomialReduction.CompleteCDifferentialPolynomialReduction
      C.derivation C.differential polynomial polynomialDomain
  /-- Integrate the selected polynomial-special branch. -/
  special : CDifferentialMonomialSpecial DensePoly α C.derivation
  /-- The semantic domain on which special integration is relatively complete. -/
  specialDomain : MonomialSpecialDomain DensePoly α
  /-- Accepted special results satisfy the selected differential identity and genuine-log laws. -/
  specialLawful :
    letI : CDifferentialMonomialSpecial DensePoly α C.derivation := special
    LawfulCDifferentialMonomialSpecial C
  /-- Special integration is relatively complete on its selected domain. -/
  specialComplete :
    letI : CDifferentialMonomialSpecial DensePoly α C.derivation := special
    letI : LawfulCDifferentialMonomialSpecial C := specialLawful
    CompleteCDifferentialMonomialSpecial C specialDomain
  /-- Reduce the normal/Hermite branch. -/
  normal : CDifferentialNormalReduction DensePoly α C.derivation
  /-- The semantic domain on which normal reduction is relatively complete. -/
  normalDomain : DifferentialNormalReductionDomain DensePoly α
  /-- Accepted normal results satisfy the selected differential identity and genuine-log laws. -/
  normalLawful :
    letI : CDifferentialNormalReduction DensePoly α C.derivation := normal
    LawfulCDifferentialNormalReduction C normalDomain
  /-- Normal reduction is relatively complete on its selected domain. -/
  normalComplete :
    letI : CDifferentialNormalReduction DensePoly α C.derivation := normal
    letI : LawfulCDifferentialNormalReduction C normalDomain := normalLawful
    CompleteCDifferentialNormalReduction C normalDomain
  /-- Apply the selected monomial-specific correction to a normal result. -/
  postprocessor : CDifferentialNormalPostprocessor DensePoly α C.derivation
  /-- The correction preserves the certified normal-result invariant. -/
  postprocessorLawful :
    letI : CDifferentialNormalPostprocessor DensePoly α C.derivation := postprocessor
    LawfulCDifferentialNormalPostprocessor C
  /-- Every certified normal result admits a selected correction. -/
  postprocessorComplete :
    letI : CDifferentialNormalPostprocessor DensePoly α C.derivation := postprocessor
    letI : LawfulCDifferentialNormalPostprocessor C := postprocessorLawful
    CompleteCDifferentialNormalPostprocessor C

namespace DifferentialOneLevelCapabilities

/-- Replace a capability bundle's monomial branch by one that explicitly consumes a lower coefficient stage. -/
noncomputable def withRecursiveMonomialCase
    {α : Type u} [CField α] [CFieldSpec.{u,u} α]
    (C : MonomialDifferentialContext (P := DensePoly) α)
    (K : DifferentialOneLevelCapabilities C)
    (M : CDifferentialRecursiveMonomialCase C)
    (I : CRecursiveElementaryIntegratorWith α C.derivation)
    (coefficientDomain : RecursiveElementaryDomainWith α)
    [LawfulCDifferentialRecursiveMonomialCase M]
    [CompleteCDifferentialRecursiveMonomialCase M coefficientDomain K.specialDomain]
    (hI : LawfulCRecursiveElementaryIntegratorWith C.derivation C.differential I)
    (hIComplete : @CompleteCRecursiveElementaryIntegratorWith α _ _
      C.derivation C.differential I coefficientDomain hI) :
    DifferentialOneLevelCapabilities C :=
  { canonical := K.canonical
    canonicalLawful := K.canonicalLawful
    polynomial := K.polynomial
    polynomialDomain := K.polynomialDomain
    polynomialLawful := K.polynomialLawful
    polynomialComplete := K.polynomialComplete
    special := M.asSpecial I
    specialDomain := K.specialDomain
    specialLawful := by
      exact LawfulCDifferentialRecursiveMonomialCase.specialLawful (C := M) I hI
    specialComplete := by
      exact CompleteCDifferentialRecursiveMonomialCase.specialComplete (C := M)
        (coefficientDomain := coefficientDomain) (specialDomain := K.specialDomain) I hI hIComplete
    normal := K.normal
    normalDomain := K.normalDomain
    normalLawful := K.normalLawful
    normalComplete := K.normalComplete
    postprocessor := M.asPostprocessor
    postprocessorLawful := by
      exact LawfulCDifferentialRecursiveMonomialCase.postprocessorLawful (C := M)
    postprocessorComplete := by
      exact CompleteCDifferentialRecursiveMonomialCase.postprocessorComplete (C := M)
        (coefficientDomain := coefficientDomain) (specialDomain := K.specialDomain) }

/-- Export all one-level capabilities as the common proof-carrying tower stage. -/
noncomputable def asRischStage
    {α : Type u} [CField α] [CFieldSpec.{u,u} α]
    (C : MonomialDifferentialContext (P := DensePoly) α)
    (K : DifferentialOneLevelCapabilities C) (kind : PolynomialReductionKind) :
    letI : CDifferentialCanonicalRepresentation DensePoly α C.derivation := K.canonical
    letI : LawfulCDifferentialCanonicalRepresentation C := by exact K.canonicalLawful
    RemainderIntegrationStage (RischStageInput DensePoly α) (IntegralResult α) (Unit × Unit)
      (fun input => IsDifferentialOneLevelIntegrable C kind input.toOneLevelInput)
      (fun input result _ => IsGenuineDifferentialOneLevelResult C input.toOneLevelInput result) := by
  letI : CDifferentialCanonicalRepresentation DensePoly α C.derivation := K.canonical
  letI : LawfulCDifferentialCanonicalRepresentation C := K.canonicalLawful
  letI : DynamicPolynomialReduction.CDifferentialPolynomialReduction DensePoly α C.derivation :=
    K.polynomial
  letI : DynamicPolynomialReduction.LawfulCDifferentialPolynomialReduction
      C.derivation C.differential K.polynomial :=
    K.polynomialLawful
  letI : DynamicPolynomialReduction.CompleteCDifferentialPolynomialReduction
      C.derivation C.differential K.polynomial
      K.polynomialDomain := K.polynomialComplete
  letI : CDifferentialMonomialSpecial DensePoly α C.derivation := K.special
  letI : LawfulCDifferentialMonomialSpecial C := K.specialLawful
  letI : CompleteCDifferentialMonomialSpecial C K.specialDomain := K.specialComplete
  letI : CDifferentialNormalReduction DensePoly α C.derivation := K.normal
  letI : LawfulCDifferentialNormalReduction C K.normalDomain := K.normalLawful
  letI : CompleteCDifferentialNormalReduction C K.normalDomain := K.normalComplete
  letI : CDifferentialNormalPostprocessor DensePoly α C.derivation := K.postprocessor
  letI : LawfulCDifferentialNormalPostprocessor C := K.postprocessorLawful
  letI : CompleteCDifferentialNormalPostprocessor C := K.postprocessorComplete
  exact K.polynomial.asRischStageRemainderStage C K.canonical kind K.polynomialDomain
    K.specialDomain K.normalDomain

/-- Every accepted capability-stage result satisfies the selected differential identity and genuine-log laws. -/
theorem asRischStage_sound
    {α : Type u} [CField α] [CFieldSpec.{u,u} α]
    (C : MonomialDifferentialContext (P := DensePoly) α)
    (K : DifferentialOneLevelCapabilities C) (kind : PolynomialReductionKind)
    (fuel : ℕ) (input : RischStageInput DensePoly α)
    (result : RemainderResult (IntegralResult α) (Unit × Unit))
    (hdomain : (K.asRischStage C kind).stage.domain input)
    (hrun : (K.asRischStage C kind).stage.run fuel input = some result) :
    IsGenuineDifferentialOneLevelResult C input.toOneLevelInput result.output :=
  (K.asRischStage C kind).sound fuel input result hdomain hrun

/-- Every integrable input accepted by the capability-stage domain eventually succeeds. -/
theorem asRischStage_complete
    {α : Type u} [CField α] [CFieldSpec.{u,u} α]
    (C : MonomialDifferentialContext (P := DensePoly) α)
    (K : DifferentialOneLevelCapabilities C) (kind : PolynomialReductionKind) :
    letI : CDifferentialCanonicalRepresentation DensePoly α C.derivation := K.canonical
    letI : LawfulCDifferentialCanonicalRepresentation C := K.canonicalLawful
    ∀ input : RischStageInput DensePoly α,
      (K.asRischStage C kind).stage.domain input →
      IsDifferentialOneLevelIntegrable C kind input.toOneLevelInput →
      ∃ fuel result, (K.asRischStage C kind).stage.run fuel input = some result := by
  letI : CDifferentialCanonicalRepresentation DensePoly α C.derivation := K.canonical
  letI : LawfulCDifferentialCanonicalRepresentation C := K.canonicalLawful
  intro input hdomain hintegrable
  exact (K.asRischStage C kind).complete input hdomain hintegrable

end DifferentialOneLevelCapabilities

/-- A tower input uses the monomial derivative selected at its presentation depth. -/
def IsPresentationMonomialInput (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n + 1 ≤ N)
    (input : RischStageInput DensePoly (DenseFracTower n)) : Prop :=
  input.Dt = T.monomialDerivative n hn

/-- Restrict a complete one-level capability bundle to the monomial selected by a presentation. -/
noncomputable def DifferentialOneLevelCapabilities.asPresentationMonomialStage
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N) (hsucc : n + 1 ≤ N)
    (K : DifferentialOneLevelCapabilities (T.context n hn)) (kind : PolynomialReductionKind) :
    letI : CDifferentialCanonicalRepresentation DensePoly (DenseFracTower n)
      (T.context n hn).derivation := K.canonical
    letI : LawfulCDifferentialCanonicalRepresentation (T.context n hn) := by
      exact K.canonicalLawful
    RemainderIntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (IntegralResult (DenseFracTower n)) (Unit × Unit)
      (fun input => IsPresentationMonomialInput T n hsucc input ∧
        IsDifferentialOneLevelIntegrable (T.context n hn) kind input.toOneLevelInput)
      (fun input result _ => IsPresentationIntegralResult T n hn input result) := by
  letI : CDifferentialCanonicalRepresentation DensePoly (DenseFracTower n)
      (T.context n hn).derivation := K.canonical
  letI : LawfulCDifferentialCanonicalRepresentation (T.context n hn) := K.canonicalLawful
  exact (K.asRischStage (T.context n hn) kind).restrictInput
    (IsPresentationMonomialInput T n hsucc)

/-- A guarded presentation stage preserves the selected-depth differential invariant. -/
theorem DifferentialOneLevelCapabilities.asPresentationMonomialStage_sound
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N) (hsucc : n + 1 ≤ N)
    (K : DifferentialOneLevelCapabilities (T.context n hn)) (kind : PolynomialReductionKind) :
    letI : CDifferentialCanonicalRepresentation DensePoly (DenseFracTower n)
      (T.context n hn).derivation := K.canonical
    letI : LawfulCDifferentialCanonicalRepresentation (T.context n hn) := K.canonicalLawful
    ∀ fuel input result,
      (K.asPresentationMonomialStage T n hn hsucc kind).stage.domain input →
      (K.asPresentationMonomialStage T n hn hsucc kind).stage.run fuel input = some result →
      IsPresentationIntegralResult T n hn input result.output := by
  letI : CDifferentialCanonicalRepresentation DensePoly (DenseFracTower n)
      (T.context n hn).derivation := K.canonical
  letI : LawfulCDifferentialCanonicalRepresentation (T.context n hn) := K.canonicalLawful
  intro fuel input result hdomain hrun
  exact (K.asPresentationMonomialStage T n hn hsucc kind).sound fuel input result hdomain hrun

/-- Every integrable guarded presentation input eventually returns a certified result. -/
theorem DifferentialOneLevelCapabilities.asPresentationMonomialStage_complete
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N) (hsucc : n + 1 ≤ N)
    (K : DifferentialOneLevelCapabilities (T.context n hn)) (kind : PolynomialReductionKind) :
    letI : CDifferentialCanonicalRepresentation DensePoly (DenseFracTower n)
      (T.context n hn).derivation := K.canonical
    letI : LawfulCDifferentialCanonicalRepresentation (T.context n hn) := K.canonicalLawful
    ∀ input,
      (K.asPresentationMonomialStage T n hn hsucc kind).stage.domain input →
      (IsPresentationMonomialInput T n hsucc input ∧
        IsDifferentialOneLevelIntegrable (T.context n hn) kind input.toOneLevelInput) →
      ∃ fuel result, (K.asPresentationMonomialStage T n hn hsucc kind).stage.run fuel input = some result := by
  letI : CDifferentialCanonicalRepresentation DensePoly (DenseFracTower n)
      (T.context n hn).derivation := K.canonical
  letI : LawfulCDifferentialCanonicalRepresentation (T.context n hn) := K.canonicalLawful
  intro input hdomain hintegrable
  exact (K.asPresentationMonomialStage T n hn hsucc kind).complete input hdomain hintegrable

/-- The coefficient-field context selected before adjoining a primitive monomial. -/
noncomputable abbrev primitiveOneStepCoefficientContext :=
  DifferentialTowerPresentation.primitiveOneStep.context 0 (Nat.zero_le 1)

/-- The coefficient-field context selected before adjoining an exponential monomial. -/
noncomputable abbrev exponentialOneStepCoefficientContext :=
  DifferentialTowerPresentation.exponentialOneStep.context 0 (Nat.zero_le 1)

/-- The coefficient-field context selected before adjoining a tangent monomial. -/
noncomputable abbrev tangentOneStepCoefficientContext :=
  DifferentialTowerPresentation.tangentOneStep.context 0 (Nat.zero_le 1)

/-- The complete one-level primitive stage selected by `t′ = 1`. -/
noncomputable def primitiveOneStepStage
    (K : DifferentialOneLevelCapabilities primitiveOneStepCoefficientContext)
    (kind : PolynomialReductionKind) :=
  K.asPresentationMonomialStage DifferentialTowerPresentation.primitiveOneStep 0 (Nat.zero_le 1)
    (Nat.le_refl 1) kind

/-- The complete one-level exponential stage selected by `t′ = t`. -/
noncomputable def exponentialOneStepStage
    (K : DifferentialOneLevelCapabilities exponentialOneStepCoefficientContext)
    (kind : PolynomialReductionKind) :=
  K.asPresentationMonomialStage DifferentialTowerPresentation.exponentialOneStep 0 (Nat.zero_le 1)
    (Nat.le_refl 1) kind

/-- The complete one-level tangent stage selected by `t′ = t² + 1`. -/
noncomputable def tangentOneStepStage
    (K : DifferentialOneLevelCapabilities tangentOneStepCoefficientContext)
    (kind : PolynomialReductionKind) :=
  K.asPresentationMonomialStage DifferentialTowerPresentation.tangentOneStep 0 (Nat.zero_le 1)
    (Nat.le_refl 1) kind

/-- A certified presentation-indexed integration level at one finite tower depth. -/
structure DifferentialTranscendentalLevel (T : DifferentialTowerPresentation N)
    (n : ℕ) (hn : n ≤ N) where
  /-- Semantic integrability predicate selected for this depth. -/
  Integrable : RischStageInput DensePoly (DenseFracTower n) → Prop
  /-- Executable level with its selected-differential remainder invariant. -/
  stage : RemainderIntegrationStage
    (RischStageInput DensePoly (DenseFracTower n)) (IntegralResult (DenseFracTower n)) (Unit × Unit)
    Integrable (fun input result _ => IsPresentationIntegralResult T n hn input result)

namespace DifferentialTranscendentalLevel

/-- Build a presentation-indexed level from any stage already certified in that presentation's context. -/
def ofStage (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N)
    (Integrable : RischStageInput DensePoly (DenseFracTower n) → Prop)
    (stage : RemainderIntegrationStage
      (RischStageInput DensePoly (DenseFracTower n)) (IntegralResult (DenseFracTower n)) (Unit × Unit)
      Integrable (fun input result _ => IsPresentationIntegralResult T n hn input result)) :
    DifferentialTranscendentalLevel T n hn :=
  ⟨Integrable, stage⟩

/-- Build a certified tower level by installing the five explicit one-level capabilities. -/
noncomputable def ofCapabilities (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N)
    (K : DifferentialOneLevelCapabilities (T.context n hn)) (kind : PolynomialReductionKind) :
    DifferentialTranscendentalLevel T n hn := by
  letI : CDifferentialCanonicalRepresentation DensePoly (DenseFracTower n)
      (T.context n hn).derivation := K.canonical
  letI : LawfulCDifferentialCanonicalRepresentation (T.context n hn) := K.canonicalLawful
  exact ofStage T n hn
    (fun input => IsDifferentialOneLevelIntegrable (T.context n hn) kind input.toOneLevelInput)
    (K.asRischStage (T.context n hn) kind)

/-- Build a presentation-indexed level whose special and normal branches consume explicit coefficient recursion. -/
noncomputable def ofRecursiveMonomialCase
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N)
    (K : DifferentialOneLevelCapabilities (T.context n hn))
    (M : CDifferentialRecursiveMonomialCase (T.context n hn))
    (I : CRecursiveElementaryIntegratorWith (DenseFracTower n) (T.context n hn).derivation)
    (coefficientDomain : RecursiveElementaryDomainWith (DenseFracTower n))
    (kind : PolynomialReductionKind)
    [LawfulCDifferentialRecursiveMonomialCase M]
    [CompleteCDifferentialRecursiveMonomialCase M coefficientDomain K.specialDomain]
    [LawfulCRecursiveElementaryIntegratorWith (T.context n hn).derivation
      (T.context n hn).differential I]
    [CompleteCRecursiveElementaryIntegratorWith (T.context n hn).derivation
      (T.context n hn).differential I coefficientDomain] :
    DifferentialTranscendentalLevel T n hn :=
  ofCapabilities T n hn
    (K.withRecursiveMonomialCase (T.context n hn) M I coefficientDomain inferInstance inferInstance) kind

/-- Every accepted presentation-indexed level result satisfies its selected derivative invariant. -/
theorem sound (L : DifferentialTranscendentalLevel T n hn) (fuel : ℕ)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (result : RemainderResult (IntegralResult (DenseFracTower n)) (Unit × Unit))
    (hdomain : L.stage.stage.domain input) (hrun : L.stage.stage.run fuel input = some result) :
    IsPresentationIntegralResult T n hn input result.output :=
  L.stage.sound fuel input result hdomain hrun

/-- Every integrable in-domain presentation input eventually returns a certified result. -/
theorem complete (L : DifferentialTranscendentalLevel T n hn)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (hdomain : L.stage.stage.domain input) (hintegrable : L.Integrable input) :
    ∃ fuel result, L.stage.stage.run fuel input = some result :=
  L.stage.complete input hdomain hintegrable

end DifferentialTranscendentalLevel

/-- View a certified dense static Risch stage as an adapter to the all-primitive presentation.

This is deliberately limited to `DifferentialTowerPresentation.primitive`: a static
`DenseFracTower` stage uses the carrier's inherited unit-monomial coefficient derivative. -/
noncomputable def DenseRischStage.asPrimitivePresentationLevel
    (S : DenseRischStage n) (N : ℕ) (hn : n ≤ N) :
    DifferentialTranscendentalLevel (DifferentialTowerPresentation.primitive N) n hn := by
  refine DifferentialTranscendentalLevel.ofStage (DifferentialTowerPresentation.primitive N) n hn
    (fun input => IsRischLevelIntegrable input.Dt input.num input.den) ?_
  let legacy := S.asRemainderIntegrationStage
  refine { stage := ?_ }
  refine
    { run := fun fuel input =>
        (legacy.stage.run fuel input).map fun result => ⟨result.output, ((), ())⟩
      domain := legacy.stage.domain
      sound := ?_
      complete := ?_ }
  · intro fuel input result hdomain hrun
    obtain ⟨output, houtput, rfl⟩ := Option.map_eq_some_iff.mp hrun
    obtain ⟨hintegral, hconstants, harguments⟩ :=
      legacy.sound fuel input output hdomain houtput
    change IsGenuineDifferentialOneLevelResult
      (MonomialDifferentialContext.ofCDiffField (P := DensePoly) (α := DenseFracTower n))
      input.toOneLevelInput output.output
    refine ⟨(isDifferentialIntegralResultP_ofCDiffField_iff input.Dt input.num input.den output.output).mpr
      hintegral, ?_, harguments⟩
    intro cv hcv
    change @Differential.deriv _ _ CDiffFieldSpec.diffK (CFieldSpec.toK cv.1) = 0
    rw [← CDiffFieldSpec.toK_cderiv]
    exact hconstants cv hcv
  · intro input hdomain hintegrable
    obtain ⟨fuel, output, hrun⟩ := legacy.complete input hdomain hintegrable
    exact ⟨fuel, ⟨output.output, ((), ())⟩, by simp [hrun]⟩

/-- A finite presentation-indexed tower builds every successor from the complete lower level. -/
structure DifferentialTranscendentalTowerScheme (T : DifferentialTowerPresentation N) where
  /-- Certified base level. -/
  base : DifferentialTranscendentalLevel T 0 (Nat.zero_le N)
  /-- Construct a successor level from the preceding certified level. -/
  step : ∀ n (hn : n + 1 ≤ N),
    DifferentialTranscendentalLevel T n (Nat.le_trans (Nat.le_succ n) hn) →
      DifferentialTranscendentalLevel T (n + 1) hn

namespace DifferentialTranscendentalTowerScheme

/-- The presentation-indexed level selected recursively at a finite tower depth. -/
noncomputable def level {N : ℕ} {T : DifferentialTowerPresentation N}
    (S : DifferentialTranscendentalTowerScheme (N := N) T) :
    ∀ n (hn : n ≤ N), DifferentialTranscendentalLevel (N := N) T n hn
  | 0, _ => S.base
  | n + 1, hn => S.step n hn (S.level n (Nat.le_trans (Nat.le_succ n) hn))

/-- Finite-tower soundness for the selected presentation derivative at every depth. -/
theorem stage_sound {N : ℕ} {T : DifferentialTowerPresentation N}
    (S : DifferentialTranscendentalTowerScheme (N := N) T)
    (n : ℕ) (hn : n ≤ N) (fuel : ℕ)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (result : RemainderResult (IntegralResult (DenseFracTower n)) (Unit × Unit))
    (hdomain : (S.level n hn).stage.stage.domain input)
    (hrun : (S.level n hn).stage.stage.run fuel input = some result) :
    IsPresentationIntegralResult T n hn input result.output :=
  (S.level n hn).sound fuel input result hdomain hrun

/-- Finite-tower relative completeness for the selected presentation derivative at every depth. -/
theorem stage_complete {N : ℕ} {T : DifferentialTowerPresentation N}
    (S : DifferentialTranscendentalTowerScheme (N := N) T)
    (n : ℕ) (hn : n ≤ N)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (hdomain : (S.level n hn).stage.stage.domain input)
    (hintegrable : (S.level n hn).Integrable input) :
    ∃ fuel result, (S.level n hn).stage.stage.run fuel input = some result :=
  (S.level n hn).complete input hdomain hintegrable

end DifferentialTranscendentalTowerScheme

/-- Adapt a finite prefix of a static dense Risch tower to the all-primitive presentation.

The static scheme chooses each dense implementation independently, so its predecessor argument is
intentionally ignored here. It is a compatibility migration path only; mixed towers must instead
use `DifferentialCoefficientTowerScheme` and its explicit successor bridge. -/
noncomputable def DenseRischTowerScheme.asPrimitivePresentationTowerScheme
    (S : DenseRischTowerScheme) (N : ℕ) :
    DifferentialTranscendentalTowerScheme (DifferentialTowerPresentation.primitive N) where
  base := (S.stage 0).asPrimitivePresentationLevel N (Nat.zero_le N)
  step n hn _ := (S.stage (n + 1)).asPrimitivePresentationLevel N hn

/-- The selected context for a primitive one-step presentation. -/
noncomputable abbrev primitiveOneStepContext :=
  DifferentialTowerPresentation.primitiveOneStep.context 1 (Nat.le_refl 1)

/-- The selected context for an exponential one-step presentation. -/
noncomputable abbrev exponentialOneStepContext :=
  DifferentialTowerPresentation.exponentialOneStep.context 1 (Nat.le_refl 1)

/-- The selected context for a tangent one-step presentation. -/
noncomputable abbrev tangentOneStepContext :=
  DifferentialTowerPresentation.tangentOneStep.context 1 (Nat.le_refl 1)

/-- Build a certified height-one tower scheme from its base and selected top level. -/
noncomputable def oneStepScheme (T : DifferentialTowerPresentation 1)
    (base : DifferentialTranscendentalLevel T 0 (Nat.zero_le 1))
    (top : DifferentialTranscendentalLevel T 1 (Nat.le_refl 1)) :
    DifferentialTranscendentalTowerScheme T where
  base := base
  step
    | 0, _ => fun _ => top
    | n + 1, hn => False.elim (by omega)

/-- A finite certified primitive one-step tower scheme. -/
noncomputable def primitiveOneStepScheme
    (base : DifferentialTranscendentalLevel DifferentialTowerPresentation.primitiveOneStep 0
      (Nat.zero_le 1))
    (top : DifferentialTranscendentalLevel DifferentialTowerPresentation.primitiveOneStep 1
      (Nat.le_refl 1)) :
    DifferentialTranscendentalTowerScheme DifferentialTowerPresentation.primitiveOneStep :=
  oneStepScheme DifferentialTowerPresentation.primitiveOneStep base top

/-- A finite certified exponential one-step tower scheme. -/
noncomputable def exponentialOneStepScheme
    (base : DifferentialTranscendentalLevel DifferentialTowerPresentation.exponentialOneStep 0
      (Nat.zero_le 1))
    (top : DifferentialTranscendentalLevel DifferentialTowerPresentation.exponentialOneStep 1
      (Nat.le_refl 1)) :
    DifferentialTranscendentalTowerScheme DifferentialTowerPresentation.exponentialOneStep :=
  oneStepScheme DifferentialTowerPresentation.exponentialOneStep base top

/-- A finite certified tangent one-step tower scheme. -/
noncomputable def tangentOneStepScheme
    (base : DifferentialTranscendentalLevel DifferentialTowerPresentation.tangentOneStep 0
      (Nat.zero_le 1))
    (top : DifferentialTranscendentalLevel DifferentialTowerPresentation.tangentOneStep 1
      (Nat.le_refl 1)) :
    DifferentialTranscendentalTowerScheme DifferentialTowerPresentation.tangentOneStep :=
  oneStepScheme DifferentialTowerPresentation.tangentOneStep base top

end DeepWiki.SymbolicIntegration
