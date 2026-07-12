import DeepWiki.SymbolicIntegration.Engine.Hermite.Reduction
import DeepWiki.SymbolicIntegration.Engine.ResidueLogPart
import DeepWiki.SymbolicIntegration.Engine.IntegrationSpec

/-! # Representation-independent normal-part reduction

The normal branch composes transcendental Hermite reduction with the residue-logarithm operation. -/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

universe u v

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Prop-free operation for reducing the normal rational part of one Risch level. -/
structure CNormalReduction (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Reduce a represented normal fraction to a rational part and logarithmic terms. -/
  reduce : P α → P α → P α → Option (IntegralResult α P)

/-- Semantic domain predicate for a represented normal-reduction operation. -/
abbrev NormalReductionDomain (P : Type u → Type u) (α : Type u) := P α → P α → P α → Prop

/-- Compose Hermite reduction and residue-logarithm extraction for a normal rational part. -/
def reduceNormal [CHermiteReduction P α] [CResidueSource P α] [CResidueLogPart P α]
    (Dt a d : P α) : Option (IntegralResult α P) :=
  match CResidueLogPart.compute Dt (hermiteResult Dt a d).remainderNum
      (hermiteResult Dt a d).remainderDen with
  | none => none
  | some logs => some ⟨((hermiteResult Dt a d).rationalNum,
      (hermiteResult Dt a d).rationalDen), logs⟩

/-- Semantic certificate exported by a complete normal-part reduction. -/
structure CertifiedNormalResult (Dt a d : P α) (out : IntegralResult α P) : Prop where
  /-- The rational and logarithmic parts integrate the input fraction. -/
  integral : IsIntegralResultP Dt a d out
  /-- The represented rational denominator is nonzero. -/
  rationalDen_nonzero : CPoly.toPoly out.rational.2 ≠ 0
  /-- Every logarithmic coefficient is constant. -/
  coefficients_constant : ∀ cv ∈ out.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0
  /-- Every represented logarithm argument is nonzero. -/
  arguments_nonzero : ∀ cv ∈ out.logs, CPoly.toPoly cv.2 ≠ 0

/-- A represented normal fraction admits a certified normal-form antiderivative. -/
def IsNormalPartIntegrable (Dt a d : P α) : Prop :=
  ∃ out : IntegralResult α P, CertifiedNormalResult Dt a d out

/-- Denotation-level soundness contract for a normal-reduction operation. -/
class LawfulCNormalReduction (N : CNormalReduction P α)
    (domain : NormalReductionDomain P α) : Prop where
  /-- Every successful in-domain reduction integrates the input normal fraction. -/
  sound : ∀ (Dt a d : P α) (out : IntegralResult α P),
    domain Dt a d → CPoly.toPoly d ≠ 0 → N.reduce Dt a d = some out →
      IsIntegralResultP Dt a d out
  /-- Every successful in-domain reduction stores a nonzero rational denominator. -/
  rationalDen_nonzero : ∀ (Dt a d : P α) (out : IntegralResult α P),
    domain Dt a d → CPoly.toPoly d ≠ 0 → N.reduce Dt a d = some out →
      CPoly.toPoly out.rational.2 ≠ 0

/-- A lawful normal reducer whose successful logarithmic terms are genuine elementary terms. -/
class LawfulGenuineCNormalReduction (N : CNormalReduction P α)
    (domain : NormalReductionDomain P α) [LawfulCNormalReduction N domain] : Prop where
  /-- Every successful in-domain reduction has constant logarithmic coefficients. -/
  coefficients_constant : ∀ (Dt a d : P α) (out : IntegralResult α P),
    domain Dt a d → CPoly.toPoly d ≠ 0 → N.reduce Dt a d = some out →
      ∀ cv ∈ out.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0
  /-- Every successful in-domain reduction has nonzero logarithm arguments. -/
  arguments_nonzero : ∀ (Dt a d : P α) (out : IntegralResult α P),
    domain Dt a d → CPoly.toPoly d ≠ 0 → N.reduce Dt a d = some out →
      ∀ cv ∈ out.logs, CPoly.toPoly cv.2 ≠ 0

/-- Relative-completeness contract for a lawful normal-reduction operation. -/
class CompleteCNormalReduction (N : CNormalReduction P α)
    (domain : NormalReductionDomain P α) [LawfulCNormalReduction N domain] : Prop where
  /-- Every integrable in-domain normal fraction produces a certified result. -/
  relative_complete : ∀ (Dt a d : P α),
    domain Dt a d → CPoly.toPoly d ≠ 0 → IsNormalPartIntegrable Dt a d →
      ∃ out, N.reduce Dt a d = some out ∧ CertifiedNormalResult Dt a d out

/-- Executable certificate that a normal-reduction result has valid denominators, arguments, and identity. -/
def normalReductionCheck (Dt a d : P α) (out : IntegralResult α P) : Bool :=
  !CPolyEngine.cisZero d && !CPolyEngine.cisZero out.rational.2 &&
    out.logs.all (fun cv => !CPolyEngine.cisZero cv.2) &&
      out.logs.all (fun cv => CCommRing.isZero (CDiffField.cderiv cv.1)) &&
      CPoly.checkIdentity Dt out a d

/-- A passed normal-reduction certificate yields its semantic identity and a nonzero result denominator. -/
theorem normalReductionCheck_sound (Dt a d : P α) (out : IntegralResult α P)
    (hcheck : normalReductionCheck Dt a d out = true) :
    CPoly.toPoly out.rational.2 ≠ 0 ∧ IsIntegralResultP Dt a d out := by
  rw [normalReductionCheck, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨⟨hdBool, houtDenBool⟩, hargsBool⟩, _hconstantsBool⟩, hidentity⟩ := hcheck
  have hd : CPoly.toPoly d ≠ 0 := by
    intro hz
    have hzBool : CPolyEngine.cisZero d = true :=
      (LawfulCPolyEngine.cisZero_iff (P := P) d).mpr hz
    rw [hzBool] at hdBool
    contradiction
  have houtDen : CPoly.toPoly out.rational.2 ≠ 0 := by
    intro hz
    have hzBool : CPolyEngine.cisZero out.rational.2 = true :=
      (LawfulCPolyEngine.cisZero_iff (P := P) out.rational.2).mpr hz
    rw [hzBool] at houtDenBool
    contradiction
  have hargs : ∀ cv ∈ out.logs, CPoly.toPoly cv.2 ≠ 0 := by
    intro cv hcv hz
    have hcvBool := (List.all_eq_true.mp hargsBool) cv hcv
    have hzBool : CPolyEngine.cisZero cv.2 = true :=
      (LawfulCPolyEngine.cisZero_iff (P := P) cv.2).mpr hz
    rw [hzBool] at hcvBool
    contradiction
  exact ⟨houtDen, isIntegralResultP_of_checkIdentity Dt out a d houtDen hd hargs hidentity⟩

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- A passed normal-reduction certificate has constant coefficients and nonzero logarithm arguments. -/
theorem normalReductionCheck_logs_genuine (Dt a d : P α) (out : IntegralResult α P)
    (hcheck : normalReductionCheck Dt a d out = true) :
    (∀ cv ∈ out.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      (∀ cv ∈ out.logs, CPoly.toPoly cv.2 ≠ 0) := by
  rw [normalReductionCheck, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨⟨_hdBool, _houtDenBool⟩, hargsBool⟩, hconstantsBool⟩, _hidentity⟩ := hcheck
  constructor
  · intro cv hcv
    have hcvBool := (List.all_eq_true.mp hconstantsBool) cv hcv
    exact (CFieldSpec.isZero_iff (CDiffField.cderiv cv.1)).mp hcvBool
  · intro cv hcv hz
    have hcvBool := (List.all_eq_true.mp hargsBool) cv hcv
    have hzBool : CPolyEngine.cisZero cv.2 = true :=
      (LawfulCPolyEngine.cisZero_iff (P := P) cv.2).mpr hz
    rw [hzBool] at hcvBool
    contradiction

/-- Guard an arbitrary normal reducer by a complete executable result certificate. -/
def checkedNormalReduction (raw : CNormalReduction P α) : CNormalReduction P α where
  reduce Dt a d := do
    let out ← raw.reduce Dt a d
    if normalReductionCheck Dt a d out then some out else none

/-- Universal semantic domain of certificate-checked normal reduction. -/
def checkedNormalReductionDomain : NormalReductionDomain P α := fun _ _ _ => True

/-- Certificate checking turns any raw normal reducer into a lawful normal-reduction operation on every
selected domain. -/
instance instLawfulCNormalReductionChecked (raw : CNormalReduction P α)
    (domain : NormalReductionDomain P α) :
    LawfulCNormalReduction (checkedNormalReduction raw) domain where
  sound Dt a d out _ _ hrun := by
    simp only [checkedNormalReduction] at hrun
    rcases hraw : raw.reduce Dt a d with _ | candidate
    · simp [hraw] at hrun
    · rw [hraw] at hrun
      change (if normalReductionCheck Dt a d candidate then some candidate else none) = some out at hrun
      by_cases hcheck : normalReductionCheck Dt a d candidate = true
      · have hout : candidate = out := by simpa [hcheck] using hrun
        subst candidate
        exact (normalReductionCheck_sound Dt a d out hcheck).2
      · simp [hcheck] at hrun
  rationalDen_nonzero Dt a d out _ _ hrun := by
    simp only [checkedNormalReduction] at hrun
    rcases hraw : raw.reduce Dt a d with _ | candidate
    · simp [hraw] at hrun
    · rw [hraw] at hrun
      change (if normalReductionCheck Dt a d candidate then some candidate else none) = some out at hrun
      by_cases hcheck : normalReductionCheck Dt a d candidate = true
      · have hout : candidate = out := by simpa [hcheck] using hrun
        subst candidate
        exact (normalReductionCheck_sound Dt a d out hcheck).1
      · simp [hcheck] at hrun

/-- Certificate checking makes every accepted normal result genuinely elementary. -/
instance instLawfulGenuineCNormalReductionChecked (raw : CNormalReduction P α)
    (domain : NormalReductionDomain P α) :
    LawfulGenuineCNormalReduction (checkedNormalReduction raw) domain where
  coefficients_constant Dt a d out _ _ hrun := by
    simp only [checkedNormalReduction] at hrun
    rcases hraw : raw.reduce Dt a d with _ | candidate
    · simp [hraw] at hrun
    · rw [hraw] at hrun
      change (if normalReductionCheck Dt a d candidate then some candidate else none) = some out at hrun
      by_cases hcheck : normalReductionCheck Dt a d candidate = true
      · have hout : candidate = out := by simpa [hcheck] using hrun
        subst candidate
        exact (normalReductionCheck_logs_genuine Dt a d out hcheck).1
      · simp [hcheck] at hrun
  arguments_nonzero Dt a d out _ _ hrun := by
    simp only [checkedNormalReduction] at hrun
    rcases hraw : raw.reduce Dt a d with _ | candidate
    · simp [hraw] at hrun
    · rw [hraw] at hrun
      change (if normalReductionCheck Dt a d candidate then some candidate else none) = some out at hrun
      by_cases hcheck : normalReductionCheck Dt a d candidate = true
      · have hout : candidate = out := by simpa [hcheck] using hrun
        subst candidate
        exact (normalReductionCheck_logs_genuine Dt a d out hcheck).2
      · simp [hcheck] at hrun
/-- The exact acceptance domain of a certificate-checked normal reducer. -/
def checkedNormalReductionAcceptanceDomain (raw : CNormalReduction P α) :
    NormalReductionDomain P α := fun Dt a d =>
  IsNormalPartIntegrable Dt a d →
    ∃ out, raw.reduce Dt a d = some out ∧ normalReductionCheck Dt a d out = true ∧
      CertifiedNormalResult Dt a d out

/-- A certificate-checked normal reducer is complete on its explicit checked acceptance domain. -/
instance instCompleteCNormalReductionChecked (raw : CNormalReduction P α) :
    CompleteCNormalReduction (checkedNormalReduction raw)
      (checkedNormalReductionAcceptanceDomain raw) where
  relative_complete Dt a d hdomain _hd hintegrable := by
    obtain ⟨out, hraw, hcheck, hcert⟩ := hdomain hintegrable
    refine ⟨out, ?_, hcert⟩
    simp [checkedNormalReduction, hraw, hcheck]

/-- Successful lawful normal reduction integrates its input fraction. -/
theorem reduceNormal_sound [CHermiteReduction P α] [LawfulCHermiteReduction (P := P) (α := α)]
    [CResidueSource P α] [CResidueLogPart P α]
    [LawfulCResidueLogPart (P := P) (α := α)] (Dt a d : P α) (out : IntegralResult α P)
    (hd : CPoly.toPoly d ≠ 0)
    (hnormal : @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly d))
    (hproper : (CPoly.toPoly a).degree < (CPoly.toPoly d).degree)
    (hdegree : (CPoly.toPoly Dt).natDegree ≤ 1)
    (hrun : reduceNormal Dt a d = some out) :
    IsIntegralResultP Dt a d out := by
  cases hlogs : CResidueLogPart.compute Dt (hermiteResult Dt a d).remainderNum
      (hermiteResult Dt a d).remainderDen with
  | none => simp [reduceNormal, hlogs] at hrun
  | some logs =>
    simp only [reduceNormal, hlogs, Option.some.injEq] at hrun
    subst out
    have hherm := LawfulCHermiteReduction.result_lawful Dt a d hd hnormal hproper hdegree
    have hres := LawfulCResidueLogPart.sound Dt (hermiteResult Dt a d).remainderNum
      (hermiteResult Dt a d).remainderDen logs hlogs
    have hlog : logResidueSumP Dt logs =
        am α (CPoly.toPoly (hermiteResult Dt a d).remainderNum) /
          am α (CPoly.toPoly (hermiteResult Dt a d).remainderDen) := by
      simpa only [logResidueSumP, towerFractionFieldDerivP_logDeriv] using hres.residue_match
    simp only [IsIntegralResultP]
    calc
      towerFractionFieldDerivP Dt
            (am α (CPoly.toPoly (hermiteResult Dt a d).rationalNum) /
              am α (CPoly.toPoly (hermiteResult Dt a d).rationalDen))
          + logResidueSumP Dt _ =
          towerFractionFieldDerivP Dt
              (am α (CPoly.toPoly (hermiteResult Dt a d).rationalNum) /
                am α (CPoly.toPoly (hermiteResult Dt a d).rationalDen))
            + am α (CPoly.toPoly (hermiteResult Dt a d).remainderNum) /
                am α (CPoly.toPoly (hermiteResult Dt a d).remainderDen) := by
              rw [hlog]
      _ = am α (CPoly.toPoly a) / am α (CPoly.toPoly d) := hherm.field_identity

omit [LawfulCPolyEngine P] in
/-- Successful normal reduction has a nonzero rational-part denominator. -/
theorem reduceNormal_rationalDen_nonzero [CHermiteReduction P α]
    [LawfulCHermiteReduction (P := P) (α := α)] [CResidueSource P α]
    [CResidueLogPart P α] (Dt a d : P α) (out : IntegralResult α P)
    (hd : CPoly.toPoly d ≠ 0)
    (hnormal : @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly d))
    (hrun : reduceNormal Dt a d = some out) :
    CPoly.toPoly out.rational.2 ≠ 0 := by
  cases hlogs : CResidueLogPart.compute Dt (hermiteResult Dt a d).remainderNum
      (hermiteResult Dt a d).remainderDen with
  | none => simp [reduceNormal, hlogs] at hrun
  | some logs =>
    simp only [reduceNormal, hlogs, Option.some.injEq] at hrun
    subst out
    exact LawfulCHermiteReduction.rationalDen_nonzero Dt a d hd hnormal

/-- A complete residue source makes normal reduction succeed whenever its Hermite remainder has a genuine
logarithmic antiderivative. -/
theorem reduceNormal_complete [CHermiteReduction P α]
    [LawfulCHermiteReduction (P := P) (α := α)] [CResidueSource P α]
    [CResidueLogPart P α] [LawfulCResidueLogPart (P := P) (α := α)]
    (residueDomain : ResidueLogPartDomain (P := P) (α := α))
    [CompleteCResidueLogPart (P := P) (α := α) residueDomain]
    (hsource : LawfulCResidueSource P α) (Dt a d : P α)
    (hd : CPoly.toPoly d ≠ 0)
    (hnormal : @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly d))
    (hproper : (CPoly.toPoly a).degree < (CPoly.toPoly d).degree)
    (hdegree : (CPoly.toPoly Dt).natDegree ≤ 1)
    (hresidueDomain : residueDomain Dt (hermiteResult Dt a d).remainderNum
      (hermiteResult Dt a d).remainderDen)
    (hwitness : ∃ logs : List (α × P α),
      GenuineResidueLogPart Dt (hermiteResult Dt a d).remainderNum
        (hermiteResult Dt a d).remainderDen logs) :
    ∃ out, reduceNormal Dt a d = some out ∧ CertifiedNormalResult Dt a d out := by
  have hherm := LawfulCHermiteReduction.result_lawful Dt a d hd hnormal hproper hdegree
  obtain ⟨logs, hlogs, hgenuine⟩ := CompleteCResidueLogPart.complete hsource Dt
    (hermiteResult Dt a d).remainderNum (hermiteResult Dt a d).remainderDen
    hresidueDomain (LawfulCHermiteReduction.remainderDen_nonzero Dt a d hd)
    hherm.squarefree hherm.proper hwitness
  let out : IntegralResult α P :=
    ⟨((hermiteResult Dt a d).rationalNum, (hermiteResult Dt a d).rationalDen), logs⟩
  have hrun : reduceNormal Dt a d = some out := by
    simp only [reduceNormal, hlogs, out]
  refine ⟨out, hrun, ?_⟩
  exact {
    integral := reduceNormal_sound Dt a d out hd hnormal hproper hdegree hrun
    rationalDen_nonzero := reduceNormal_rationalDen_nonzero Dt a d out hd hnormal hrun
    coefficients_constant := by simpa only [out] using hgenuine.coefficients_constant
    arguments_nonzero := by simpa only [out] using hgenuine.arguments_nonzero }

/-- The existing Hermite-plus-residue composition as a selected normal-reduction operation. -/
def hermiteResidueNormalReduction [CHermiteReduction P α] [CResidueSource P α]
    [CResidueLogPart P α] : CNormalReduction P α where
  reduce := reduceNormal

/-- Soundness domain where Hermite reduction is normal, proper, and low-degree. -/
def hermiteResidueNormalSoundDomain [CHermiteReduction P α] : NormalReductionDomain P α :=
  fun Dt a d =>
    @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩ (CPoly.toPoly d) ∧
    (CPoly.toPoly a).degree < (CPoly.toPoly d).degree ∧
    (CPoly.toPoly Dt).natDegree ≤ 1

/-- Complete normal-reduction domain: the soundness hypotheses plus a genuine residue-log witness. -/
def hermiteResidueNormalCompleteDomain [CHermiteReduction P α]
    (residueDomain : ResidueLogPartDomain (P := P) (α := α)) : NormalReductionDomain P α :=
  fun Dt a d => hermiteResidueNormalSoundDomain Dt a d ∧
    (IsNormalPartIntegrable Dt a d →
      residueDomain Dt (hermiteResult Dt a d).remainderNum
          (hermiteResult Dt a d).remainderDen ∧
        ∃ logs : List (α × P α),
        GenuineResidueLogPart Dt (hermiteResult Dt a d).remainderNum
        (hermiteResult Dt a d).remainderDen logs)

/-- Lawful Hermite and residue stages realize sound normal reduction on the low-degree domain. -/
instance instLawfulCNormalReductionHermiteResidue [CHermiteReduction P α]
    [LawfulCHermiteReduction (P := P) (α := α)] [CResidueSource P α]
    [CResidueLogPart P α] [LawfulCResidueLogPart (P := P) (α := α)] :
    LawfulCNormalReduction (hermiteResidueNormalReduction (P := P) (α := α))
      (hermiteResidueNormalSoundDomain (P := P) (α := α)) where
  sound Dt a d out hdomain hd hrun :=
    reduceNormal_sound Dt a d out hd hdomain.1 hdomain.2.1 hdomain.2.2 hrun
  rationalDen_nonzero Dt a d out hdomain hd hrun :=
    reduceNormal_rationalDen_nonzero Dt a d out hd hdomain.1 hrun

/-- Genuine residue extraction makes Hermite-residue normal reduction genuinely lawful. -/
instance instLawfulGenuineCNormalReductionHermiteResidue [CHermiteReduction P α]
    [LawfulCHermiteReduction (P := P) (α := α)] [CResidueSource P α]
    [CResidueLogPart P α] [LawfulCResidueLogPart (P := P) (α := α)]
    [LawfulGenuineCResidueLogPart (P := P) (α := α)] :
    LawfulGenuineCNormalReduction (hermiteResidueNormalReduction (P := P) (α := α))
      (hermiteResidueNormalSoundDomain (P := P) (α := α)) where
  coefficients_constant Dt a d out _hdomain _hd hrun := by
    cases hlogs : CResidueLogPart.compute Dt (hermiteResult Dt a d).remainderNum
        (hermiteResult Dt a d).remainderDen with
    | none => simp [hermiteResidueNormalReduction, reduceNormal, hlogs] at hrun
    | some logs =>
      simp only [hermiteResidueNormalReduction, reduceNormal, hlogs, Option.some.injEq] at hrun
      subst out
      exact (LawfulGenuineCResidueLogPart.genuine Dt
        (hermiteResult Dt a d).remainderNum
        (hermiteResult Dt a d).remainderDen logs hlogs).coefficients_constant
  arguments_nonzero Dt a d out _hdomain _hd hrun := by
    cases hlogs : CResidueLogPart.compute Dt (hermiteResult Dt a d).remainderNum
        (hermiteResult Dt a d).remainderDen with
    | none => simp [hermiteResidueNormalReduction, reduceNormal, hlogs] at hrun
    | some logs =>
      simp only [hermiteResidueNormalReduction, reduceNormal, hlogs, Option.some.injEq] at hrun
      subst out
      exact (LawfulGenuineCResidueLogPart.genuine Dt
        (hermiteResult Dt a d).remainderNum
        (hermiteResult Dt a d).remainderDen logs hlogs).arguments_nonzero

/-- The stronger complete domain inherits the normal-reduction soundness contract. -/
instance instLawfulCNormalReductionHermiteResidueCompleteDomain [CHermiteReduction P α]
    [LawfulCHermiteReduction (P := P) (α := α)] [CResidueSource P α]
    [CResidueLogPart P α] [LawfulCResidueLogPart (P := P) (α := α)]
    (residueDomain : ResidueLogPartDomain (P := P) (α := α)) :
    LawfulCNormalReduction (hermiteResidueNormalReduction (P := P) (α := α))
      (hermiteResidueNormalCompleteDomain (P := P) (α := α) residueDomain) where
  sound Dt a d out hdomain hd hrun :=
    LawfulCNormalReduction.sound (N := hermiteResidueNormalReduction (P := P) (α := α))
      Dt a d out hdomain.1 hd hrun
  rationalDen_nonzero Dt a d out hdomain hd hrun :=
    LawfulCNormalReduction.rationalDen_nonzero
      (N := hermiteResidueNormalReduction (P := P) (α := α)) Dt a d out hdomain.1 hd hrun

/-- The complete Hermite-residue domain inherits genuine normal-reduction soundness. -/
instance instLawfulGenuineCNormalReductionHermiteResidueCompleteDomain [CHermiteReduction P α]
    [LawfulCHermiteReduction (P := P) (α := α)] [CResidueSource P α]
    [CResidueLogPart P α] [LawfulCResidueLogPart (P := P) (α := α)]
    [LawfulGenuineCResidueLogPart (P := P) (α := α)]
    (residueDomain : ResidueLogPartDomain (P := P) (α := α)) :
    LawfulGenuineCNormalReduction (hermiteResidueNormalReduction (P := P) (α := α))
      (hermiteResidueNormalCompleteDomain (P := P) (α := α) residueDomain) where
  coefficients_constant Dt a d out hdomain hd hrun :=
    LawfulGenuineCNormalReduction.coefficients_constant
      (N := hermiteResidueNormalReduction (P := P) (α := α))
      (domain := hermiteResidueNormalSoundDomain (P := P) (α := α))
      Dt a d out hdomain.1 hd hrun
  arguments_nonzero Dt a d out hdomain hd hrun :=
    LawfulGenuineCNormalReduction.arguments_nonzero
      (N := hermiteResidueNormalReduction (P := P) (α := α))
      (domain := hermiteResidueNormalSoundDomain (P := P) (α := α))
      Dt a d out hdomain.1 hd hrun

/-- Complete residue extraction realizes relative completeness of the Hermite-residue normal stage. -/
instance instCompleteCNormalReductionHermiteResidue [CHermiteReduction P α]
    [LawfulCHermiteReduction (P := P) (α := α)] [CResidueSource P α]
    [LawfulCResidueSource P α] [CResidueLogPart P α]
    [LawfulCResidueLogPart (P := P) (α := α)]
    (residueDomain : ResidueLogPartDomain (P := P) (α := α))
    [CompleteCResidueLogPart (P := P) (α := α) residueDomain] :
    CompleteCNormalReduction (hermiteResidueNormalReduction (P := P) (α := α))
      (hermiteResidueNormalCompleteDomain (P := P) (α := α) residueDomain) where
  relative_complete Dt a d hdomain hd hintegrable :=
    reduceNormal_complete residueDomain (inferInstance : LawfulCResidueSource P α) Dt a d hd
      hdomain.1.1 hdomain.1.2.1 hdomain.1.2.2 (hdomain.2 hintegrable).1
      (hdomain.2 hintegrable).2

end DeepWiki.SymbolicIntegration
