import DeepWiki.SymbolicIntegration.Engine.Tower.DifferentialTranscendental
import DeepWiki.SymbolicIntegration.Engine.Tower.RecursiveElementary

/-! # Checked successor coefficient bridges

A successor coefficient solver is obtained by running the preceding presentation-indexed level at
the selected monomial derivative, lifting its integral result, and certificate-checking that lift
against the successor derivation. The lift theorem is the sole representation-specific obligation.
-/

namespace DeepWiki.SymbolicIntegration

/-- Cast a packaged successor semantic value into its preceding rational-function presentation. -/
noncomputable def denseFracTowerKSuccCast (n : ℕ) :
    CFieldSpec.K (DenseFracTower (n + 1)) → RatFunc (CFieldSpec.K (DenseFracTower n)) :=
  cast (denseFracTower_K_succ n)

/-- Present a successor coefficient as a Risch input at the preceding presentation depth. -/
noncomputable def presentationCoefficientInput (T : DifferentialTowerPresentation N)
    (n : ℕ) (hn : n + 1 ≤ N) (c : DenseFracTower (n + 1)) :
    RischStageInput DensePoly (DenseFracTower n) where
  Dt := T.monomialDerivative n hn
  num := CFrac.num c
  den := CFrac.den c
  den_nonzero := CFrac.toPoly_den_ne_zero_generic c

/-- Embed a preceding represented polynomial into its packaged successor fraction carrier. -/
noncomputable def towerOfPoly (n : ℕ) (p : DensePoly (DenseFracTower n)) :
    DenseFracTower (n + 1) :=
  CFrac.ofPoly (F := DenseFrac) p

/-- Lift logarithmic coefficient/argument pairs into the packaged successor fraction carrier. -/
noncomputable def liftTowerLogs (n : ℕ)
    (logs : List (DenseFracTower n × DensePoly (DenseFracTower n))) :
    List (DenseFracTower (n + 1) × DenseFracTower (n + 1)) :=
  logs.map fun cv => (towerOfPoly n [cv.1], towerOfPoly n cv.2)

/-- Lift a lower integral result into successor coefficient data. -/
noncomputable def liftRischResultToTowerCoefficient (n : ℕ)
    (res : IntegralResult (DenseFracTower n)) :
    CoefficientIntegralResult (DenseFracTower (n + 1)) where
  rational := CField.div (CFrac.ofPoly (F := DenseFrac) res.rational.1)
    (CFrac.ofPoly (F := DenseFrac) res.rational.2)
  logs := liftTowerLogs n res.logs

/-- The lifted rational part denotes the lower integral result's rational function in the packaged successor field. -/
theorem toK_liftRischResultToTowerCoefficient_rational (n : ℕ)
    (res : IntegralResult (DenseFracTower n)) :
    CFieldSpec.toK (liftRischResultToTowerCoefficient n res).rational =
      fieldFracP res.rational.1 res.rational.2 := by
  change CFieldSpec.toK (CField.div
    (CFrac.ofPoly (F := DenseFrac) res.rational.1)
    (CFrac.ofPoly (F := DenseFrac) res.rational.2)) = _
  rw [CFieldSpec.toK_div]
  rw [CFrac.toK_ofPoly, CFrac.toK_ofPoly]

/-- The successor presentation differentiates the lifted rational part by the preceding selected function-field derivative. -/
theorem differential_deriv_liftRischResultToTowerCoefficient_rational
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n + 1 ≤ N)
    (res : IntegralResult (DenseFracTower n)) :
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    let C := T.context n hprev
    @Differential.deriv _ _ (T.differential (n + 1) hn)
      (CFieldSpec.toK (liftRischResultToTowerCoefficient n res).rational) =
      C.fractionDeriv (T.monomialDerivative n hn)
        (fieldFracP res.rational.1 res.rational.2) := by
  let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
  let C := T.context n hprev
  letI : Differential (CFieldSpec.K (DenseFracTower n)) := T.differential n hprev
  letI : Differential (CRingSpec.R (DenseFracTower n)) := T.differential n hprev
  letI : Algebra ℚ (CRingSpec.R (DenseFracTower n)) := by
    change Algebra ℚ (CFieldSpec.K (DenseFracTower n))
    exact C.algebraQ
  rw [← DifferentialTowerPresentation.toK_cderiv T (n + 1) hn]
  rw [T.successorSemantics n hn]
  rw [toK_liftRischResultToTowerCoefficient_rational]
  rfl

/-- An embedded successor polynomial denotes its ordinary preceding function-field embedding. -/
theorem toK_towerOfPoly (n : ℕ) (p : DensePoly (DenseFracTower n)) :
    CFieldSpec.toK (towerOfPoly n p) =
      CFrac.am (DenseFracTower n) (CPoly.toPoly p) := by
  change CFrac.toRatFunc (CFrac.ofPoly (F := DenseFrac) p) = _
  exact CFrac.toRatFunc_ofPoly p

/-- The successor presentation differentiates an embedded polynomial by the preceding selected function-field derivative. -/
theorem differential_deriv_towerOfPoly
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n + 1 ≤ N)
    (p : DensePoly (DenseFracTower n)) :
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    let C := T.context n hprev
    @Differential.deriv _ _ (T.differential (n + 1) hn)
      (CFieldSpec.toK (towerOfPoly n p)) =
      C.fractionDeriv (T.monomialDerivative n hn)
        (CFrac.am (DenseFracTower n) (CPoly.toPoly p)) := by
  let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
  let C := T.context n hprev
  letI : Differential (CFieldSpec.K (DenseFracTower n)) := T.differential n hprev
  letI : Differential (CRingSpec.R (DenseFracTower n)) := T.differential n hprev
  letI : Algebra ℚ (CRingSpec.R (DenseFracTower n)) := by
    change Algebra ℚ (CFieldSpec.K (DenseFracTower n))
    exact C.algebraQ
  rw [← DifferentialTowerPresentation.toK_cderiv T (n + 1) hn]
  rw [T.successorSemantics n hn]
  unfold towerOfPoly
  change extendDeriv (Differential.implicitDeriv (CPoly.toPoly (T.monomialDerivative n hn)))
      (CFrac.toRatFunc (CFrac.ofPoly (F := DenseFrac) p)) = _
  rw [CFrac.toRatFunc_ofPoly]
  rfl

/-- One lifted coefficient logarithm has the preceding presentation's explicit log-residue value. -/
theorem coefficientLogTerm_towerOfPoly
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n + 1 ≤ N)
    (c : DenseFracTower n) (p : DensePoly (DenseFracTower n)) :
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    let C := T.context n hprev
    CFieldSpec.toK (towerOfPoly n [c]) *
        (@Differential.deriv _ _ (T.differential (n + 1) hn)
          (CFieldSpec.toK (towerOfPoly n p)) /
          CFieldSpec.toK (towerOfPoly n p)) =
      CFrac.am (DenseFracTower n) (Polynomial.C (CFieldSpec.toK c)) *
        (C.fractionDeriv (T.monomialDerivative n hn)
          (CFrac.am (DenseFracTower n) (CPoly.toPoly p)) /
          CFrac.am (DenseFracTower n) (CPoly.toPoly p)) := by
  let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
  let C := T.context n hprev
  rw [differential_deriv_towerOfPoly T n hn p]
  rw [toK_towerOfPoly n p]
  rw [toK_towerOfPoly n ([c] : DensePoly (DenseFracTower n))]
  rw [toPoly_list_eq]
  simp only [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil, toR_eq_toK, mul_zero, add_zero]
  rfl

/-- Lifting every lower logarithmic residue yields the successor coefficient logarithmic sum. -/
theorem coefficientLogSumWith_liftTowerLogs
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n + 1 ≤ N)
    (logs : List (DenseFracTower n × DensePoly (DenseFracTower n))) :
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    let C := T.context n hprev
    coefficientLogSumWith (T.derivation (n + 1) hn) (liftTowerLogs n logs) =
      differentialLogResidueSum C (T.monomialDerivative n hn) logs := by
  let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
  let C := T.context n hprev
  induction logs with
  | nil => rfl
  | cons cv rest ih =>
      change coefficientLogSumWith (T.derivation (n + 1) hn)
          ((towerOfPoly n [cv.1], towerOfPoly n cv.2) :: liftTowerLogs n rest) =
        differentialLogResidueSum C (T.monomialDerivative n hn) (cv :: rest)
      rw [coefficientLogSumWith_cons]
      have hsplit :
          differentialLogResidueSum C (T.monomialDerivative n hn) (cv :: rest) =
            CFrac.am (DenseFracTower n) (Polynomial.C (CFieldSpec.toK cv.1)) *
                (C.fractionDeriv (T.monomialDerivative n hn)
                  (CFrac.am (DenseFracTower n) (CPoly.toPoly cv.2)) /
                  CFrac.am (DenseFracTower n) (CPoly.toPoly cv.2)) +
              differentialLogResidueSum C (T.monomialDerivative n hn) rest := rfl
      rw [hsplit]
      rw [DifferentialTowerPresentation.toK_cderiv T (n + 1) hn (towerOfPoly n cv.2)]
      rw [coefficientLogTerm_towerOfPoly T n hn cv.1 cv.2, ih]
      rfl

/-- A genuine lower presentation result lifts to a genuine explicit coefficient result upstairs. -/
theorem isCoefficientIntegralResultWith_liftRischResultToTowerCoefficient
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n + 1 ≤ N)
    (c : DenseFracTower (n + 1)) (res : IntegralResult (DenseFracTower n))
    (hresult : IsPresentationIntegralResult T n (Nat.le_trans (Nat.le_succ n) hn)
      (presentationCoefficientInput T n hn c) res) :
    IsCoefficientIntegralResultWith (T.derivation (n + 1) hn)
      (T.differential (n + 1) hn) c (liftRischResultToTowerCoefficient n res) := by
  let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
  let C := T.context n hprev
  letI : Differential (CFieldSpec.K (DenseFracTower n)) := T.differential n hprev
  letI : Differential (CRingSpec.R (DenseFracTower n)) := T.differential n hprev
  letI : Algebra ℚ (CRingSpec.R (DenseFracTower n)) := by
    change Algebra ℚ (CFieldSpec.K (DenseFracTower n))
    exact C.algebraQ
  change IsGenuineDifferentialOneLevelResult C
      ⟨T.monomialDerivative n hn, CFrac.num c, CFrac.den c,
        CFrac.toPoly_den_ne_zero_generic c⟩ res at hresult
  obtain ⟨hintegral, hconstants, harguments⟩ := hresult
  refine ⟨?_, ?_, ?_⟩
  · change @Differential.deriv _ _ (T.differential (n + 1) hn)
        (CFieldSpec.toK (liftRischResultToTowerCoefficient n res).rational) +
          coefficientLogSumWith (T.derivation (n + 1) hn) (liftTowerLogs n res.logs) =
        CFieldSpec.toK c
    rw [coefficientLogSumWith_liftTowerLogs T n hn]
    rw [differential_deriv_liftRischResultToTowerCoefficient_rational T n hn]
    change C.fractionDeriv (T.monomialDerivative n hn)
        (fieldFracP res.rational.1 res.rational.2) +
          differentialLogResidueSum C (T.monomialDerivative n hn) res.logs =
        CFrac.toRatFunc c
    rw [CFrac.toRatFunc_eq_div]
    exact hintegral
  · intro lifted hlifted
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hlifted
    rw [differential_deriv_towerOfPoly T n hn ([source.1] : DensePoly (DenseFracTower n))]
    rw [toPoly_list_eq]
    simp only [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil, toR_eq_toK, mul_zero, add_zero]
    rw [MonomialDifferentialContext.fractionDeriv_algebraMap, Differential.implicitDeriv_C]
    rw [hconstants source hsource, Polynomial.C_0, map_zero]
    rfl
  · intro lifted hlifted
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hlifted
    rw [toK_towerOfPoly]
    exact CFrac.am_ne_zero (harguments source hsource)

/-- The legacy dense lift has the packaged successor tower's rational-function denotation. -/
theorem denseFracTower_toRatFunc_liftRischResult_rational
    (n : ℕ) (res : IntegralResult (DenseFracTower n)) :
    CFrac.toRatFunc (liftRischResultToCoefficient res).rational =
      fieldFracP res.rational.1 res.rational.2 := by
  exact toK_liftRischResult_rational res

/-- The successor presentation differentiates a lifted rational part by the preceding selected function-field derivative. -/
theorem differential_deriv_liftRischResult_rational
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n + 1 ≤ N)
    (res : IntegralResult (DenseFracTower n)) :
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    let C := T.context n hprev
    @Differential.deriv _ _ (T.differential (n + 1) hn)
      (CFieldSpec.toK (liftRischResultToCoefficient res).rational) =
      C.fractionDeriv (T.monomialDerivative n hn)
        (fieldFracP res.rational.1 res.rational.2) := by
  let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
  let C := T.context n hprev
  letI : Differential (CFieldSpec.K (DenseFracTower n)) := T.differential n hprev
  letI : Differential (CRingSpec.R (DenseFracTower n)) := T.differential n hprev
  letI : Algebra ℚ (CRingSpec.R (DenseFracTower n)) := by
    change Algebra ℚ (CFieldSpec.K (DenseFracTower n))
    exact C.algebraQ
  rw [← DifferentialTowerPresentation.toK_cderiv T (n + 1) hn]
  rw [T.successorSemantics n hn]
  change extendDeriv (Differential.implicitDeriv (CPoly.toPoly (T.monomialDerivative n hn)))
      (CFrac.toRatFunc (liftRischResultToCoefficient res).rational) = _
  rw [denseFracTower_toRatFunc_liftRischResult_rational n res]
  rw [MonomialDifferentialContext.fractionDeriv]
  rfl

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

/-- The canonical dense successor bridge lifts every genuine result from its preceding presentation level. -/
noncomputable def DifferentialCoefficientBridge.ofPresentationLevel
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n + 1 ≤ N)
    (lower : DifferentialTranscendentalLevel T n (Nat.le_trans (Nat.le_succ n) hn)) :
    DifferentialCoefficientBridge T n hn where
  lower := lower
  lift := liftRischResultToTowerCoefficient n
  lift_sound := isCoefficientIntegralResultWith_liftRischResultToTowerCoefficient T n hn

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
