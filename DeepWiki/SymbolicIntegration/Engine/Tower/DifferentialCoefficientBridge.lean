import DeepWiki.SymbolicIntegration.Engine.Tower.DifferentialTranscendental

/-! # Checked successor coefficient bridges

A successor coefficient solver is obtained by running the preceding presentation-indexed level at
the selected monomial derivative, lifting its integral result, and certificate-checking that lift
against the successor derivation. The lift theorem is the sole representation-specific obligation.
-/

namespace DeepWiki.SymbolicIntegration

/-- Present a successor coefficient as a Risch input at the preceding presentation depth. -/
noncomputable def presentationCoefficientInput (T : DifferentialTowerPresentation N)
    (n : ℕ) (hn : n + 1 ≤ N) (c : DenseFracTower (n + 1)) :
    RischStageInput DensePoly (DenseFracTower n) where
  Dt := T.monomialDerivative n hn
  num := CFrac.num c
  den := CFrac.den c
  den_nonzero := CFrac.toPoly_den_ne_zero_generic c

/-- A certified lift from one presentation level into its successor coefficient field. -/
structure DifferentialCoefficientBridge (T : DifferentialTowerPresentation N)
    (n : ℕ) (hn : n + 1 ≤ N) where
  /-- The certified preceding level used to generate coefficient candidates. -/
  lower : DifferentialTranscendentalLevel T n (Nat.le_trans (Nat.le_succ n) hn)
  /-- Convert a preceding integral result into successor coefficient data. -/
  lift : IntegralResult (DenseFracTower n) → CoefficientIntegralResult (DenseFracTower (n + 1))
  /-- The lifted lower certificate is a valid elementary coefficient certificate at the successor. -/
  lift_sound : ∀ (c : DenseFracTower (n + 1)) (result : IntegralResult (DenseFracTower n)),
    IsPresentationIntegralResult T n (Nat.le_trans (Nat.le_succ n) hn)
      (presentationCoefficientInput T n hn c) result →
      IsCoefficientIntegralResultWith (T.derivation (n + 1) hn) (T.differential (n + 1) hn)
        c (lift result)

namespace DifferentialCoefficientBridge

/-- The raw successor coefficient candidate produced by the preceding presentation level. -/
noncomputable def raw (B : DifferentialCoefficientBridge T n hn) :
    CRecursiveElementaryIntegratorWith (DenseFracTower (n + 1)) (T.derivation (n + 1) hn) where
  integrate fuel c :=
    (B.lower.stage.stage.run fuel (presentationCoefficientInput T n hn c)).map fun result =>
      B.lift result.output

/-- The raw candidate guarded by the selected successor coefficient certificate. -/
noncomputable def checked (B : DifferentialCoefficientBridge T n hn) :
    CRecursiveElementaryIntegratorWith (DenseFracTower (n + 1)) (T.derivation (n + 1) hn) :=
  checkedRecursiveElementaryIntegratorWith (T.derivation (n + 1) hn) B.raw

/-- The exact certified acceptance domain of a checked successor coefficient bridge. -/
noncomputable def domain (B : DifferentialCoefficientBridge T n hn) :
    RecursiveElementaryDomainWith (DenseFracTower (n + 1)) :=
  checkedRecursiveElementaryIntegratorWithDomain (T.derivation (n + 1) hn)
    (T.differential (n + 1) hn) B.raw

/-- A successful lower-level run places the lifted candidate in the checked bridge domain. -/
theorem domain_of_lower_success (B : DifferentialCoefficientBridge T n hn)
    (fuel : ℕ) (c : DenseFracTower (n + 1)) (result : IntegralResult (DenseFracTower n))
    (hdomain : B.lower.stage.stage.domain (presentationCoefficientInput T n hn c))
    (hrun : B.lower.stage.stage.run fuel (presentationCoefficientInput T n hn c) = some ⟨result, ((), ())⟩) :
    B.domain c := by
  refine ⟨fuel, B.lift result, ?_, ?_⟩
  · simp [raw, hrun]
  · exact B.lift_sound c result
      (B.lower.sound fuel (presentationCoefficientInput T n hn c) ⟨result, ((), ())⟩ hdomain hrun)

/-- The checked bridge is a globally lawful explicit recursive coefficient solver. -/
@[reducible] noncomputable def lawful (B : DifferentialCoefficientBridge T n hn) :
    LawfulCRecursiveElementaryIntegratorWith (T.derivation (n + 1) hn)
      (T.differential (n + 1) hn) B.checked := by
  letI : LawfulCFieldDerivation (DenseFracTower (n + 1)) (T.derivation (n + 1) hn)
      (T.differential (n + 1) hn) := T.lawful (n + 1) hn
  exact instLawfulCRecursiveElementaryIntegratorWithChecked
    (T.derivation (n + 1) hn) (T.differential (n + 1) hn) B.raw

/-- The checked bridge is relatively complete on precisely its certified lifted-result domain. -/
@[reducible] noncomputable def complete (B : DifferentialCoefficientBridge T n hn) :
    @CompleteCRecursiveElementaryIntegratorWith (DenseFracTower (n + 1)) _ _
      (T.derivation (n + 1) hn) (T.differential (n + 1) hn) B.checked B.domain B.lawful := by
  letI : LawfulCFieldDerivation (DenseFracTower (n + 1)) (T.derivation (n + 1) hn)
      (T.differential (n + 1) hn) := T.lawful (n + 1) hn
  letI : LawfulCRecursiveElementaryIntegratorWith (T.derivation (n + 1) hn)
      (T.differential (n + 1) hn) B.checked := B.lawful
  exact instCompleteCRecursiveElementaryIntegratorWithChecked
    (T.derivation (n + 1) hn) (T.differential (n + 1) hn) B.raw

/-- Build the next presentation-indexed level by installing a checked lower coefficient bridge. -/
noncomputable def DifferentialTranscendentalLevel.successorOfCoefficientBridge
    (B : DifferentialCoefficientBridge T n hn)
    (K : DifferentialOneLevelCapabilities (T.context (n + 1) hn))
    (M : CDifferentialRecursiveMonomialCase (T.context (n + 1) hn))
    (kind : PolynomialReductionKind)
    [LawfulCDifferentialRecursiveMonomialCase M]
    [CompleteCDifferentialRecursiveMonomialCase M B.domain K.specialDomain] :
    DifferentialTranscendentalLevel T (n + 1) hn := by
  exact DifferentialTranscendentalLevel.ofCapabilities T (n + 1) hn
    (K.withRecursiveMonomialCase (T.context (n + 1) hn) M B.checked B.domain B.lawful B.complete)
    kind

/-- The data required to construct one successor level from its certified preceding level. -/
structure DifferentialCoefficientSuccessor
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n + 1 ≤ N)
    (lower : DifferentialTranscendentalLevel T n (Nat.le_trans (Nat.le_succ n) hn)) where
  /-- The checked coefficient bridge generated from the preceding level. -/
  bridge : DifferentialCoefficientBridge T n hn
  /-- The bridge is anchored at exactly the preceding level supplied by the tower recursion. -/
  bridge_lower : bridge.lower = lower
  /-- The non-monomial capabilities selected at the successor depth. -/
  capabilities : DifferentialOneLevelCapabilities (T.context (n + 1) hn)
  /-- The recursive special and normal operation selected at the successor depth. -/
  monomial : CDifferentialRecursiveMonomialCase (T.context (n + 1) hn)
  /-- The polynomial-reduction branch selected at the successor depth. -/
  kind : PolynomialReductionKind
  /-- The recursive monomial operation preserves its selected differential invariant. -/
  lawful : LawfulCDifferentialRecursiveMonomialCase monomial
  /-- The recursive monomial operation is relatively complete over the checked bridge domain. -/
  complete :
    letI : LawfulCDifferentialRecursiveMonomialCase monomial := lawful
    CompleteCDifferentialRecursiveMonomialCase monomial bridge.domain capabilities.specialDomain

namespace DifferentialCoefficientSuccessor

/-- Construct the successor level selected by bridge-aware recursive coefficient integration. -/
noncomputable def level
    {N : ℕ} {T : DifferentialTowerPresentation N} {n : ℕ} {hn : n + 1 ≤ N}
    {lower : DifferentialTranscendentalLevel T n (Nat.le_trans (Nat.le_succ n) hn)}
    (S : DifferentialCoefficientSuccessor T n hn lower) :
    DifferentialTranscendentalLevel T (n + 1) hn := by
  letI : LawfulCDifferentialRecursiveMonomialCase S.monomial := S.lawful
  letI : CompleteCDifferentialRecursiveMonomialCase S.monomial S.bridge.domain
      S.capabilities.specialDomain := S.complete
  exact DifferentialTranscendentalLevel.successorOfCoefficientBridge S.bridge S.capabilities
    S.monomial S.kind

end DifferentialCoefficientSuccessor

/-- A finite tower whose every successor obtains coefficient recursion from the preceding level. -/
structure DifferentialCoefficientTowerScheme (T : DifferentialTowerPresentation N) where
  /-- Certified base integration level. -/
  base : DifferentialTranscendentalLevel T 0 (Nat.zero_le N)
  /-- Build each strict successor from its certified preceding level. -/
  step : ∀ n (hn : n + 1 ≤ N)
    (lower : DifferentialTranscendentalLevel T n (Nat.le_trans (Nat.le_succ n) hn)),
    DifferentialCoefficientSuccessor T n hn lower

namespace DifferentialCoefficientTowerScheme

/-- Forget the bridge packaging to obtain the common finite presentation-indexed tower scheme. -/
noncomputable def asTowerScheme (S : DifferentialCoefficientTowerScheme T) :
    DifferentialTranscendentalTowerScheme T where
  base := S.base
  step n hn lower := (S.step n hn lower).level

/-- The bridge-aware scheme inherits finite-tower soundness from the common induction theorem. -/
theorem stage_sound {N : ℕ} {T : DifferentialTowerPresentation N}
    (S : DifferentialCoefficientTowerScheme T)
    (n : ℕ) (hn : n ≤ N) (fuel : ℕ)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (result : RemainderResult (IntegralResult (DenseFracTower n)) (Unit × Unit))
    (hdomain : (S.asTowerScheme.level n hn).stage.stage.domain input)
    (hrun : (S.asTowerScheme.level n hn).stage.stage.run fuel input = some result) :
    IsPresentationIntegralResult T n hn input result.output :=
  S.asTowerScheme.stage_sound n hn fuel input result hdomain hrun

/-- The bridge-aware scheme inherits finite-tower relative completeness from the common induction theorem. -/
theorem stage_complete {N : ℕ} {T : DifferentialTowerPresentation N}
    (S : DifferentialCoefficientTowerScheme T)
    (n : ℕ) (hn : n ≤ N)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (hdomain : (S.asTowerScheme.level n hn).stage.stage.domain input)
    (hintegrable : (S.asTowerScheme.level n hn).Integrable input) :
    ∃ fuel result, (S.asTowerScheme.level n hn).stage.stage.run fuel input = some result :=
  S.asTowerScheme.stage_complete n hn input hdomain hintegrable

end DifferentialCoefficientTowerScheme

end DifferentialCoefficientBridge

end DeepWiki.SymbolicIntegration
