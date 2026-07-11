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
    [CompleteCResidueLogPart (P := P) (α := α)]
    (hsource : LawfulCResidueSource P α) (Dt a d : P α)
    (hd : CPoly.toPoly d ≠ 0)
    (hnormal : @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly d))
    (hproper : (CPoly.toPoly a).degree < (CPoly.toPoly d).degree)
    (hdegree : (CPoly.toPoly Dt).natDegree ≤ 1)
    (hwitness : ∃ logs : List (α × P α),
      GenuineResidueLogPart Dt (hermiteResult Dt a d).remainderNum
        (hermiteResult Dt a d).remainderDen logs) :
    ∃ out, reduceNormal Dt a d = some out ∧ CertifiedNormalResult Dt a d out := by
  have hherm := LawfulCHermiteReduction.result_lawful Dt a d hd hnormal hproper hdegree
  obtain ⟨logs, hlogs, hgenuine⟩ := CompleteCResidueLogPart.complete hsource Dt
    (hermiteResult Dt a d).remainderNum (hermiteResult Dt a d).remainderDen
    (LawfulCHermiteReduction.remainderDen_nonzero Dt a d hd) hherm.squarefree hherm.proper hwitness
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

end DeepWiki.SymbolicIntegration
