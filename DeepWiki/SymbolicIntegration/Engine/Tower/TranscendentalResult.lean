import DeepWiki.SymbolicIntegration.Engine.Tower.AlgebraicCoefficient

/-! # Layered transcendental integration results

Separates ordinary and root-free logarithms created in the current monomial extension from inherited
coefficient-field logarithms. The layers use different derivations and cannot share one `IntegralResult.logs`
list. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- A full result over `DenseFrac β` with current ordinary/LRT logs and inherited coefficient logs. -/
structure TranscendentalIntegralResult (β : Type u) [CField β] where
  /-- Rational part in the current fraction field. -/
  rational : DenseFrac β
  /-- Logarithms whose polynomial arguments lie in the current monomial extension. -/
  localLogs : List (β × DensePoly β)
  /-- Root-free algebraic-residue logarithms whose arguments lie in the current monomial extension. -/
  localLrtLogs : List (DensePoly β × List (DensePoly β))
  /-- Logarithms inherited from coefficient-field recursion. -/
  inheritedLogs : List (AlgebraicCoefficientLog β)

variable {β : Type u} [CField β] [CFieldSpec.{u,u} β] [CDiffField β]

/-- Embed an ordinary one-level result, with all its logs local to the current extension. -/
def TranscendentalIntegralResult.ofIntegralResult (res : IntegralResult β) :
    TranscendentalIntegralResult β where
  rational := CField.div (CFrac.ofPoly res.rational.1) (CFrac.ofPoly res.rational.2)
  localLogs := res.logs
  localLrtLogs := []
  inheritedLogs := []

/-- Embed a root-free current-extension result without changing its algebraic-residue log family. -/
def TranscendentalIntegralResult.ofLrtResult (res : LrtResult β) :
    TranscendentalIntegralResult β where
  rational := CField.div (CFrac.ofPoly res.rational.1) (CFrac.ofPoly res.rational.2)
  localLogs := []
  localLrtLogs := res.logs
  inheritedLogs := []

/-- Embed an inherited coefficient result, with no new current-extension logarithms. -/
def TranscendentalIntegralResult.ofCoefficientResult (res : AlgebraicCoefficientIntegralResult β) :
    TranscendentalIntegralResult β where
  rational := res.rational
  localLogs := []
  localLrtLogs := []
  inheritedLogs := res.logs

omit [CDiffField β] in
/-- The rational part of an ordinary one-level result keeps its represented field denotation. -/
theorem toK_ofIntegralResult_rational [CFieldDomain β DensePoly]
    (res : IntegralResult β) :
    CFieldSpec.toK (TranscendentalIntegralResult.ofIntegralResult res).rational =
      fieldFracP res.rational.1 res.rational.2 := by
  simp [TranscendentalIntegralResult.ofIntegralResult, fieldFracP,
    CFieldSpec.toK_div, CFrac.toK_ofPoly]

omit [CDiffField β] in
/-- The rational part of a root-free result keeps its represented field denotation. -/
theorem toK_ofLrtResult_rational [CFieldDomain β DensePoly]
    (res : LrtResult β) :
    CFieldSpec.toK (TranscendentalIntegralResult.ofLrtResult res).rational =
      fieldFracP res.rational.1 res.rational.2 := by
  simp [TranscendentalIntegralResult.ofLrtResult, fieldFracP,
    CFieldSpec.toK_div, CFrac.toK_ofPoly]

/-- Derivative contribution of a local logarithm in an algebraically closed differential extension. -/
noncomputable def localLogTerm {E : Type*} [Field E]
    [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    (Dt : DensePoly β) (log : β × DensePoly β) : RatFunc E :=
  algebraMap E (RatFunc E) (algebraMap (CFieldSpec.K β) E (CFieldSpec.toK log.1)) *
    (towerDerivExt Dt (amGExt (E := E) (CPoly.toPoly log.2)) /
      amGExt (E := E) (CPoly.toPoly log.2))

/-- Derivative contribution of all current-extension logarithms. -/
noncomputable def localLogSum {E : Type*} [Field E]
    [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
  (Dt : DensePoly β) (logs : List (β × DensePoly β)) : RatFunc E :=
  (logs.map (localLogTerm (E := E) Dt)).sum

/-- The current-extension derivation of a represented polynomial is its base-changed monomial derivative. -/
theorem towerDerivExt_amGExt (Dt p : DensePoly β) {E : Type*} [Field E]
    [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    [CDiffFieldSpec β] [DifferentialAlgebra (CFieldSpec.K β) E] :
    towerDerivExt Dt (amGExt (E := E) (CPoly.toPoly p)) =
      amGExt (E := E) (CPoly.toPoly (CPolyEngine.monomialDeriv Dt p)) := by
  unfold towerDerivExt amGExt
  rw [extendDeriv_algebraMap, CPolyEngine.toPoly_monomialDeriv, ← implicitDeriv_map]
  simp only [toPoly_list_eq]

/-- A local logarithmic term is the base change of the ordinary represented logarithmic derivative. -/
theorem localLogTerm_eq_baseChange (Dt : DensePoly β) (log : β × DensePoly β)
    {E : Type*} [Field E] [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    [CDiffFieldSpec β] [DifferentialAlgebra (CFieldSpec.K β) E] :
    localLogTerm (E := E) Dt log =
      ratFuncBaseChange E
        (CFrac.am β (Polynomial.C (CFieldSpec.toK log.1)) *
          (CFrac.am β (CPoly.toPoly (CPolyEngine.monomialDeriv Dt log.2)) /
            CFrac.am β (CPoly.toPoly log.2))) := by
  unfold localLogTerm
  rw [map_mul, ratFuncBaseChange_amG, ratFuncBaseChange_amG_div,
    ← towerDerivExt_amGExt]
  simp [amGExt]

/-- The current-extension log sum is the base change of the ordinary represented log sum. -/
theorem localLogSum_eq_baseChange (Dt : DensePoly β) (logs : List (β × DensePoly β))
    {E : Type*} [Field E] [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    [CDiffFieldSpec β] [DifferentialAlgebra (CFieldSpec.K β) E] :
    localLogSum (E := E) Dt logs = ratFuncBaseChange E (logResidueSumP Dt logs) := by
  induction logs with
  | nil => simp [localLogSum, logResidueSumP]
  | cons log logs ih =>
    simp only [localLogSum, logResidueSumP, List.map_cons, List.sum_cons, map_add]
    rw [localLogTerm_eq_baseChange]
    have htail : (logs.map (localLogTerm (E := E) Dt)).sum =
        ratFuncBaseChange E
          (logs.map fun cv =>
            CFrac.am β (Polynomial.C (CFieldSpec.toK cv.1)) *
              (CFrac.am β (CPoly.toPoly (CPolyEngine.monomialDeriv Dt cv.2)) /
                CFrac.am β (CPoly.toPoly cv.2))).sum := by
      simpa [localLogSum, logResidueSumP] using ih
    rw [htail]

/-- The root-free local logs have constant algebraic residues. -/
def TranscendentalIntegralResult.LocalLrtLogsGenuine
    (logs : List (DensePoly β × List (DensePoly β))) : Prop :=
  logs.all (fun RS =>
    CPolyEngine.cisZero (CPolyEngine.mapDeriv (CPolyEngine.cmonic RS.1))) = true

/-- A layered result is a genuine Liouville result when each of its log layers is genuine. -/
def TranscendentalIntegralResult.LogsGenuine [CDiffFieldSpec β]
    (res : TranscendentalIntegralResult β) : Prop :=
  (∀ log ∈ res.localLogs,
    CFieldSpec.toK (CDiffField.cderiv log.1) = 0 ∧ CPoly.toPoly log.2 ≠ 0) ∧
  TranscendentalIntegralResult.LocalLrtLogsGenuine res.localLrtLogs ∧
  ∀ log ∈ res.inheritedLogs, log.IsGenuine

/-- Genuine ordinary one-level logarithms remain genuine in the local layer. -/
theorem TranscendentalIntegralResult.logsGenuine_ofIntegralResult [CDiffFieldSpec β]
    (res : IntegralResult β)
    (hconstants : ∀ log ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv log.1) = 0)
    (hargs : ∀ log ∈ res.logs, CPoly.toPoly log.2 ≠ 0) :
    (TranscendentalIntegralResult.ofIntegralResult res).LogsGenuine := by
  constructor
  · intro log hlog
    exact ⟨hconstants log hlog, hargs log hlog⟩
  constructor
  · rfl
  · simp [TranscendentalIntegralResult.ofIntegralResult]

/-- A genuine root-free result remains genuine in the current LRT layer. -/
theorem TranscendentalIntegralResult.logsGenuine_ofLrtResult [CDiffFieldSpec β]
    (res : LrtResult β) (hres : AllResiduesConstantLrt res) :
    (TranscendentalIntegralResult.ofLrtResult res).LogsGenuine := by
  constructor
  · simp [TranscendentalIntegralResult.ofLrtResult]
  constructor
  · exact hres
  · simp [TranscendentalIntegralResult.ofLrtResult]

/-- Denotational identity for a two-layer result at a current monomial derivative `Dt`. -/
def IsTranscendentalIntegralResult [CDiffFieldSpec β]
    (Dt anum aden : DensePoly β) (res : TranscendentalIntegralResult β) : Prop :=
  ∀ (E : Type u) [Field E] [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    [DifferentialAlgebra (CFieldSpec.K β) E] [IsAlgClosed E],
    towerDerivExt Dt
        (amGExt (E := E) (CPoly.toPoly (CFrac.num res.rational)) /
          amGExt (E := E) (CPoly.toPoly (CFrac.den res.rational))) +
      localLogSum (E := E) Dt res.localLogs +
      logResidueSumLrt (E := E) Dt res.localLrtLogs +
      algebraicCoefficientLogSum (E := E) ([CCommRing.one] : DensePoly β) res.inheritedLogs =
    amGExt (E := E) (CPoly.toPoly anum) /
      amGExt (E := E) (CPoly.toPoly aden)

/-- An ordinary one-level certificate transports to the two-layer result invariant with no inherited logs. -/
theorem isTranscendentalIntegralResult_ofIntegralResult [CDiffFieldSpec β]
    [CFieldDomain β DensePoly] [Algebra ℚ (CFieldSpec.K β)]
    (Dt anum aden : DensePoly β) (res : IntegralResult β)
    (hres : IsIntegralResultP Dt anum aden res) :
    IsTranscendentalIntegralResult Dt anum aden
      (TranscendentalIntegralResult.ofIntegralResult res) := by
  intro E _ _ _ _ _ _
  have hderiv :
      ratFuncBaseChange E
          (towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2)) =
        towerDerivExt Dt
          (amGExt (E := E) (CPoly.toPoly res.rational.1) /
            amGExt (E := E) (CPoly.toPoly res.rational.2)) := by
    simpa only [towerFractionFieldDerivP, towerFractionFieldDeriv, fieldFracP, toPoly_list_eq] using
      (ratFuncBaseChange_towerFractionFieldDerivG (E := E) Dt
        (CPoly.toPoly res.rational.1) (CPoly.toPoly res.rational.2))
  have hrational :
      amGExt (E := E)
          (CPoly.toPoly (CFrac.num (TranscendentalIntegralResult.ofIntegralResult res).rational)) /
        amGExt (E := E)
          (CPoly.toPoly (CFrac.den (TranscendentalIntegralResult.ofIntegralResult res).rational)) =
        amGExt (E := E) (CPoly.toPoly res.rational.1) /
          amGExt (E := E) (CPoly.toPoly res.rational.2) := by
    calc
      _ = ratFuncBaseChange E
          (CFieldSpec.toK (TranscendentalIntegralResult.ofIntegralResult res).rational) := by
        symm
        rw [toK_denseFrac_eq_fieldFrac, fieldFracP, ratFuncBaseChange_amG_div]
      _ = ratFuncBaseChange E (fieldFracP res.rational.1 res.rational.2) := by
        rw [toK_ofIntegralResult_rational]
      _ = _ := by
        rw [fieldFracP, ratFuncBaseChange_amG_div]
  have hbase := congrArg (ratFuncBaseChange E) hres
  rw [map_add, hderiv, ← localLogSum_eq_baseChange,
    ratFuncBaseChange_amG_div] at hbase
  rw [hrational]
  simp only [TranscendentalIntegralResult.ofIntegralResult, algebraicCoefficientLogSum,
    List.map_nil, List.sum_nil, logResidueSumLrtG_nil, add_zero]
  exact hbase

/-- A root-free current-extension certificate transports to the layered invariant with no other logs. -/
theorem isTranscendentalIntegralResult_ofLrtResult [CDiffFieldSpec β]
    [CFieldDomain β DensePoly] [Algebra ℚ (CFieldSpec.K β)]
    (Dt anum aden : DensePoly β) (res : LrtResult β)
    (hres : IsIntegralResultLrt Dt anum aden res) :
    IsTranscendentalIntegralResult Dt anum aden
      (TranscendentalIntegralResult.ofLrtResult res) := by
  intro E _ _ _ _ _ _
  have hrational :
      amGExt (E := E)
          (CPoly.toPoly (CFrac.num (TranscendentalIntegralResult.ofLrtResult res).rational)) /
        amGExt (E := E)
          (CPoly.toPoly (CFrac.den (TranscendentalIntegralResult.ofLrtResult res).rational)) =
        amGExt (E := E) (CPoly.toPoly res.rational.1) /
          amGExt (E := E) (CPoly.toPoly res.rational.2) := by
    calc
      _ = ratFuncBaseChange E
          (CFieldSpec.toK (TranscendentalIntegralResult.ofLrtResult res).rational) := by
        symm
        rw [toK_denseFrac_eq_fieldFrac, fieldFracP, ratFuncBaseChange_amG_div]
      _ = ratFuncBaseChange E (fieldFracP res.rational.1 res.rational.2) := by
        rw [toK_ofLrtResult_rational]
      _ = _ := by
        rw [fieldFracP, ratFuncBaseChange_amG_div]
  rw [hrational]
  simpa only [TranscendentalIntegralResult.ofLrtResult, localLogSum, algebraicCoefficientLogSum,
    List.map_nil, List.sum_nil, zero_add, add_zero, toPoly_list_eq] using hres E

end DeepWiki.SymbolicIntegration
