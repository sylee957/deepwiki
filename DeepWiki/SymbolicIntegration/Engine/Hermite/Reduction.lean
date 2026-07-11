import DeepWiki.SymbolicIntegration.Engine.CheckIdentityCorrect
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.NormalSqfree

/-! # Interface: `LawfulHermiteReduction`

The Hermite-reduction stage of the Risch reduced case, stated purely against the denotation. A Hermite
output `(gnum, gden, hNum, Dstar)` for input `a/d` with monomial derivation `Dt` is *lawful* when it clears
the cleared Hermite identity `D⟦gnum/gden⟧ + ⟦hNum/Dstar⟧ = ⟦a/d⟧`, the leftover denominator `Dstar` is
squarefree, and the leftover fraction `hNum/Dstar` is proper. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CFrac

universe u v

variable {P : Type u → Type u} [CPoly P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Representation-neutral output of transcendental Hermite reduction. -/
structure HermiteReductionResult (P : Type u → Type u) [CPoly P]
    (α : Type u) [CField α] where
  /-- Numerator of the extracted rational derivative part. -/
  rationalNum : P α
  /-- Denominator of the extracted rational derivative part. -/
  rationalDen : P α
  /-- Numerator of the squarefree-denominator remainder. -/
  remainderNum : P α
  /-- Squarefree denominator of the remainder. -/
  remainderDen : P α

/-- Prop-free transcendental Hermite-reduction operation over a polynomial representation. -/
class CHermiteReduction (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Extract a rational derivative and a squarefree-denominator remainder from `a/d`. -/
  compute : P α → P α → P α → HermiteReductionResult P α

/-- The selected Hermite-reduction output. -/
abbrev hermiteResult [CPolyEngine P] [CHermiteReduction P α] (Dt a d : P α) :
    HermiteReductionResult P α :=
  CHermiteReduction.compute Dt a d

/-- Interface law for a Hermite reduction output `(gnum, gden, hNum, Dstar)` of `a/d`. -/
structure LawfulHermiteReduction (Dt a d gnum gden hNum Dstar : P α) : Prop where
  /-- The cleared Hermite identity `D⟦gnum/gden⟧ + ⟦hNum/Dstar⟧ = ⟦a/d⟧`. -/
  field_identity : towerFractionFieldDerivP Dt
      (am α (CPoly.toPoly gnum) / am α (CPoly.toPoly gden))
      + am α (CPoly.toPoly hNum) / am α (CPoly.toPoly Dstar)
        = am α (CPoly.toPoly a) / am α (CPoly.toPoly d)
  /-- The leftover denominator is squarefree. -/
  squarefree : Squarefree (CPoly.toPoly Dstar)
  /-- The leftover fraction is proper. -/
  proper : (CPoly.toPoly hNum).degree < (CPoly.toPoly Dstar).degree

/-- Semantic laws for a selected transcendental Hermite-reduction operation. -/
class LawfulCHermiteReduction [CPolyEngine P] [CHermiteReduction P α] : Prop where
  /-- The rational-part denominator is nonzero on a nonzero normal-squarefree input denominator. -/
  rationalDen_nonzero : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩ (CPoly.toPoly d) →
    CPoly.toPoly (hermiteResult Dt a d).rationalDen ≠ 0
  /-- The squarefree-remainder denominator is nonzero on a nonzero input denominator. -/
  remainderDen_nonzero : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    CPoly.toPoly (hermiteResult Dt a d).remainderDen ≠ 0
  /-- Hermite reduction reconstructs the input under differential normality. -/
  field_identity : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩ (CPoly.toPoly d) →
    towerFractionFieldDerivP Dt
        (am α (CPoly.toPoly (hermiteResult Dt a d).rationalNum) /
          am α (CPoly.toPoly (hermiteResult Dt a d).rationalDen))
      + am α (CPoly.toPoly (hermiteResult Dt a d).remainderNum) /
          am α (CPoly.toPoly (hermiteResult Dt a d).remainderDen)
        = am α (CPoly.toPoly a) / am α (CPoly.toPoly d)
  /-- The Hermite remainder denominator is squarefree. -/
  remainder_squarefree : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    Squarefree (CPoly.toPoly (hermiteResult Dt a d).remainderDen)
  /-- Low-degree monomial derivations preserve properness of the Hermite remainder. -/
  remainder_proper : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩ (CPoly.toPoly d) →
    (CPoly.toPoly a).degree < (CPoly.toPoly d).degree →
    (CPoly.toPoly Dt).degree ≤ 1 →
    (CPoly.toPoly (hermiteResult Dt a d).remainderNum).degree <
      (CPoly.toPoly (hermiteResult Dt a d).remainderDen).degree

/-- The selected Hermite output satisfies the stage-result contract under its semantic preconditions. -/
theorem LawfulCHermiteReduction.result_lawful [CPolyEngine P] [CHermiteReduction P α]
    [LawfulCHermiteReduction (P := P) (α := α)] (Dt a d : P α)
    (hd : CPoly.toPoly d ≠ 0)
    (hnormal : @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly d))
    (hproper : (CPoly.toPoly a).degree < (CPoly.toPoly d).degree)
    (hdegree : (CPoly.toPoly Dt).degree ≤ 1) :
    LawfulHermiteReduction Dt a d (hermiteResult Dt a d).rationalNum
      (hermiteResult Dt a d).rationalDen (hermiteResult Dt a d).remainderNum
      (hermiteResult Dt a d).remainderDen where
  field_identity := LawfulCHermiteReduction.field_identity Dt a d hd hnormal
  squarefree := LawfulCHermiteReduction.remainder_squarefree Dt a d hd
  proper := LawfulCHermiteReduction.remainder_proper Dt a d hd hnormal hproper hdegree

end DeepWiki.SymbolicIntegration
