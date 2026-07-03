import DeepWiki.SymbolicIntegration.Computable.RischDE.SolveExhaustiveness

/-! # The Risch-DE decision procedure

`crischDESolveSoundWf_isDecisionProcedure`: modulo the completeness frontier
`RischDEDecisionProcedureFrontierWf f g` and the soundness certificate `RischDESoundnessWf f g`,
the recursive Risch-DE solver returns `some` iff the field-level RDE is solvable. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## Inner frontier -/

section InnerFrontierWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- The inner-completeness frontier: the three residual clauses feeding `RischDEInnerCompletenessWf`. -/
structure RischDEInnerDecisionFrontierWf (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- Normal-denominator divisibility residual. -/
  hnorm : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden
  /-- Degree-bound cancellation residual on the special-cleared coefficients. -/
  hbound : RdeBoundCancellationResidualWf Dt fnum fden gnum gden
  /-- Inner solver exhaustiveness residual. -/
  hsolve : RischDESolveExhaustiveResidualWf Dt fnum fden gnum gden

/-- The inner frontier assembles `RischDEInnerCompletenessWf`. -/
theorem rischDEInnerCompletenessWf_of_decisionFrontierWf (Dt fnum fden gnum gden : CPolyG α)
    (h : RischDEInnerDecisionFrontierWf Dt fnum fden gnum gden) :
    RischDEInnerCompletenessWf Dt fnum fden gnum gden :=
  rischDEInnerCompletenessWf_of_residuals Dt fnum fden gnum gden h.hnorm h.hbound h.hsolve

/-- The inner frontier yields inner-solver success on polynomial-solvable inputs. -/
theorem cRischDEGWf_isSome_of_decisionFrontierWf (Dt fnum fden gnum gden : CPolyG α)
    (h : RischDEInnerDecisionFrontierWf Dt fnum fden gnum gden)
    (hsol : ∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    (cRischDEGWf Dt fnum fden gnum gden).isSome = true :=
  cRischDEGWf_isSome_of_innerCompletenessWf Dt fnum fden gnum gden
    (rischDEInnerCompletenessWf_of_decisionFrontierWf Dt fnum fden gnum gden h) hsol

example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
    [CRischField α] (Dt fnum fden gnum gden : CPolyG α)
    (h : RischDEInnerDecisionFrontierWf Dt fnum fden gnum gden) :
    RischDEInnerCompletenessWf Dt fnum fden gnum gden :=
  rischDEInnerCompletenessWf_of_decisionFrontierWf Dt fnum fden gnum gden h

end InnerFrontierWf

/-! ## Inner input and decision frontier -/

section InnerInputWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- The inner RDE input pair: after weak normalization by `q`, the reduced transformed left-hand side
paired with `q * g`, as `crischDESolveSoundWf` forms it before calling `crischDERawSolveWf`. -/
def rischDEInnerInputWf (f g : QFunNZG β) : QFunNZG β × QFunNZG β :=
  let q : CPolyG β := cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
  let q' : QFunNZG β := qOfPolyNZG q
  (qReduce (weakNormalizedF f q'), qmulNZG q' g)

end InnerInputWf

/-! ## The field-level decision-procedure frontier and capstone -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- `RischDEDecisionProcedureFrontierWf f g`: the field-level frontier — nonzero weak normalizer (`hwn`),
canonical-normality (`hck`), a polynomial solution for the inner input (`hpolysol`), an inner-completeness
proof (`hinner`), and the denominator guard (`hden`). -/
structure RischDEDecisionProcedureFrontierWf (f g : QFunNZG β) : Prop where
  /-- A solvable RDE has a nonzero weak normalizer. -/
  hwn : FieldRDESolvable f g →
    CPolyG.cisZeroG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2) = false
  /-- A solvable RDE satisfies the canonical-normality guarantee. -/
  hck : FieldRDESolvable f g →
    IsCanonNormalizedWf f
      (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))
  /-- A solvable field RDE has a polynomial solution for the inner input. -/
  hpolysol : FieldRDESolvable f g →
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    ∃ ynum yden,
      IsCRischDEGPolySol ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2
        gtilde.1.1 gtilde.1.2 ynum yden
  /-- The inner-completeness proof for the weak-normalized, reduced input pair. -/
  hinner : FieldRDESolvable f g →
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    RischDEInnerCompletenessWf ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2
      gtilde.1.1 gtilde.1.2
  /-- The returned denominator of a successful inner solve is nonzero. -/
  hden : FieldRDESolvable f g → ∀ ynum yden : CPolyG β,
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    cRischDEGWf ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2 gtilde.1.1 gtilde.1.2
        = some (ynum, yden) →
      CPolyG.cisZeroG yden = false

/-- Assemble the field-level frontier from its inner residual-tip frontier. -/
theorem decisionProcedureFrontierWf_of_innerFrontier (f g : QFunNZG β)
    (hwn : FieldRDESolvable f g →
      CPolyG.cisZeroG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2) = false)
    (hck : FieldRDESolvable f g →
      IsCanonNormalizedWf f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)))
    (hpolysol : FieldRDESolvable f g →
      let ftildeR := (rischDEInnerInputWf f g).1
      let gtilde := (rischDEInnerInputWf f g).2
      ∃ ynum yden,
        IsCRischDEGPolySol ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2
          gtilde.1.1 gtilde.1.2 ynum yden)
    (hinnerFront : FieldRDESolvable f g →
      let ftildeR := (rischDEInnerInputWf f g).1
      let gtilde := (rischDEInnerInputWf f g).2
      RischDEInnerDecisionFrontierWf ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2
        gtilde.1.1 gtilde.1.2)
    (hden : FieldRDESolvable f g → ∀ ynum yden : CPolyG β,
      let ftildeR := (rischDEInnerInputWf f g).1
      let gtilde := (rischDEInnerInputWf f g).2
      cRischDEGWf ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2 gtilde.1.1 gtilde.1.2
          = some (ynum, yden) →
        CPolyG.cisZeroG yden = false) :
    RischDEDecisionProcedureFrontierWf f g where
  hwn := hwn
  hck := hck
  hpolysol := hpolysol
  hinner hsol :=
    rischDEInnerCompletenessWf_of_decisionFrontierWf ([CField.one] : CPolyG β)
      (rischDEInnerInputWf f g).1.1.1 (rischDEInnerInputWf f g).1.1.2
      (rischDEInnerInputWf f g).2.1.1 (rischDEInnerInputWf f g).2.1.2
      (hinnerFront hsol)
  hden := hden

/-- The frontier produces `RischDECompletenessResidualWf`: the `hinner` clause comes from feeding the
inner-completeness proof through the raw-solver bridge. -/
theorem completenessResidualWf_of_decisionProcedureFrontierWf (f g : QFunNZG β)
    (h : RischDEDecisionProcedureFrontierWf f g) :
    RischDECompletenessResidualWf f g where
  hwn hsol := h.hwn hsol
  hck hsol := h.hck hsol
  hinner hsol := by
    simpa [rischDEInnerInputWf] using
      (crischDERawSolveWf_isSome_of_innerCompletenessWf (rischDEInnerInputWf f g).1
        (rischDEInnerInputWf f g).2
        (h.hinner hsol)
        (h.hpolysol hsol) (h.hden hsol))

/-- Under `RischDEDecisionProcedureFrontierWf f g` and `RischDESoundnessWf f g`, the recursive solver returns
`some` iff the field-level Risch DE is solvable — `crischDESolveSoundWf f g = some _ ↔ FieldRDESolvable f g`. -/
theorem crischDESolveSoundWf_isDecisionProcedure (f g : QFunNZG β)
    (h : RischDEDecisionProcedureFrontierWf f g)
    (hsound : RischDESoundnessWf f g) :
    (∃ y, crischDESolveSoundWf f g = some y) ↔ FieldRDESolvable f g :=
  crischDESolveSoundWf_decides_of_residualWf f g
    (completenessResidualWf_of_decisionProcedureFrontierWf f g h) hsound

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ The RDE decision procedure in book terms: the fuel-free recursive Risch-DE solver returns `some` iff the
-- field-level Risch DE `D(Y) + F·Y = G` is solvable, modulo the named Wf §6 completeness frontier + the
-- direct Wf soundness certificate.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]
    (f g : QFunNZG β) (h : RischDEDecisionProcedureFrontierWf f g)
    (hsound : RischDESoundnessWf f g) :
    (∃ y, crischDESolveSoundWf f g = some y) ↔ FieldRDESolvable f g :=
  crischDESolveSoundWf_isDecisionProcedure f g h hsound

end Capstone

/-! ### Axiom audit -/

#print axioms crischDESolveSoundWf_isDecisionProcedure
#print axioms decisionProcedureFrontierWf_of_innerFrontier
#print axioms rischDEInnerCompletenessWf_of_decisionFrontierWf
#print axioms cRischDEGWf_isSome_of_decisionFrontierWf

end DeepWiki.SymbolicIntegration
