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

/-- Successful lawful normal reduction integrates its input fraction. -/
theorem reduceNormal_sound [CHermiteReduction P α] [LawfulCHermiteReduction (P := P) (α := α)]
    [CResidueSource P α] [CResidueLogPart P α]
    [LawfulCResidueLogPart (P := P) (α := α)] (Dt a d : P α) (out : IntegralResult α P)
    (hd : CPoly.toPoly d ≠ 0)
    (hnormal : @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly d))
    (hproper : (CPoly.toPoly a).degree < (CPoly.toPoly d).degree)
    (hdegree : (CPoly.toPoly Dt).degree ≤ 1)
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
/-- A complete residue source makes normal reduction succeed whenever its Hermite remainder has a genuine
logarithmic antiderivative. -/
theorem reduceNormal_complete [CHermiteReduction P α]
    [LawfulCHermiteReduction (P := P) (α := α)] [CResidueSource P α]
    [CResidueLogPart P α] [LawfulCResidueLogPart (P := P) (α := α)]
    (hsource : LawfulCResidueSource P α) (Dt a d : P α)
    (hd : CPoly.toPoly d ≠ 0)
    (hnormal : @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly d))
    (hproper : (CPoly.toPoly a).degree < (CPoly.toPoly d).degree)
    (hdegree : (CPoly.toPoly Dt).degree ≤ 1)
    (hwitness : ∃ logs : List (α × P α),
      LawfulResidueLogPart Dt (hermiteResult Dt a d).remainderNum
        (hermiteResult Dt a d).remainderDen logs ∧
      (∀ cv ∈ logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      (∀ cv ∈ logs, CPoly.toPoly cv.2 ≠ 0)) :
    ∃ out, reduceNormal Dt a d = some out := by
  have hherm := LawfulCHermiteReduction.result_lawful Dt a d hd hnormal hproper hdegree
  obtain ⟨logs, hlogs⟩ := LawfulCResidueLogPart.complete hsource Dt
    (hermiteResult Dt a d).remainderNum (hermiteResult Dt a d).remainderDen
    (LawfulCHermiteReduction.remainderDen_nonzero Dt a d hd) hherm.squarefree hherm.proper hwitness
  refine ⟨⟨((hermiteResult Dt a d).rationalNum, (hermiteResult Dt a d).rationalDen), logs⟩, ?_⟩
  simp only [reduceNormal, hlogs]

end DeepWiki.SymbolicIntegration
