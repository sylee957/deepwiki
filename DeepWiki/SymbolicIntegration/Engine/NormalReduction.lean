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

/-- Relative-completeness contract for a lawful normal-reduction operation. -/
class CompleteCNormalReduction (N : CNormalReduction P α)
    (domain : NormalReductionDomain P α) [LawfulCNormalReduction N domain] : Prop where
  /-- Every integrable in-domain normal fraction produces a certified result. -/
  relative_complete : ∀ (Dt a d : P α),
    domain Dt a d → CPoly.toPoly d ≠ 0 → IsNormalPartIntegrable Dt a d →
      ∃ out, N.reduce Dt a d = some out ∧ CertifiedNormalResult Dt a d out

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

/-- The existing Hermite-plus-residue composition as a selected normal-reduction operation. -/
def hermiteResidueNormalReduction [CHermiteReduction P α] [CResidueSource P α]
    [CResidueLogPart P α] : CNormalReduction P α where
  reduce := reduceNormal

/-- Domain where Hermite reduction is proper and integrability supplies genuine residue logarithms. -/
def hermiteResidueNormalDomain [CHermiteReduction P α] : NormalReductionDomain P α :=
  fun Dt a d =>
    @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩ (CPoly.toPoly d) ∧
    (CPoly.toPoly a).degree < (CPoly.toPoly d).degree ∧
    (CPoly.toPoly Dt).natDegree ≤ 1 ∧
    (IsNormalPartIntegrable Dt a d →
      ∃ logs : List (α × P α),
        GenuineResidueLogPart Dt (hermiteResult Dt a d).remainderNum
          (hermiteResult Dt a d).remainderDen logs)

/-- Lawful Hermite and residue stages realize sound normal reduction on the low-degree domain. -/
instance instLawfulCNormalReductionHermiteResidue [CHermiteReduction P α]
    [LawfulCHermiteReduction (P := P) (α := α)] [CResidueSource P α]
    [CResidueLogPart P α] [LawfulCResidueLogPart (P := P) (α := α)] :
    LawfulCNormalReduction (hermiteResidueNormalReduction (P := P) (α := α))
      (hermiteResidueNormalDomain (P := P) (α := α)) where
  sound Dt a d out hdomain hd hrun :=
    reduceNormal_sound Dt a d out hd hdomain.1 hdomain.2.1 hdomain.2.2.1 hrun
  rationalDen_nonzero Dt a d out hdomain hd hrun :=
    reduceNormal_rationalDen_nonzero Dt a d out hd hdomain.1 hrun

/-- Complete residue extraction realizes relative completeness of the Hermite-residue normal stage. -/
instance instCompleteCNormalReductionHermiteResidue [CHermiteReduction P α]
    [LawfulCHermiteReduction (P := P) (α := α)] [CResidueSource P α]
    [LawfulCResidueSource P α] [CResidueLogPart P α]
    [LawfulCResidueLogPart (P := P) (α := α)]
    [CompleteCResidueLogPart (P := P) (α := α)] :
    CompleteCNormalReduction (hermiteResidueNormalReduction (P := P) (α := α))
      (hermiteResidueNormalDomain (P := P) (α := α)) where
  relative_complete Dt a d hdomain hd hintegrable :=
    reduceNormal_complete (inferInstance : LawfulCResidueSource P α) Dt a d hd
      hdomain.1 hdomain.2.1 hdomain.2.2.1 (hdomain.2.2.2 hintegrable)

end DeepWiki.SymbolicIntegration
