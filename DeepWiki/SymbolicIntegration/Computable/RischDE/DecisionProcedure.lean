import DeepWiki.SymbolicIntegration.Computable.RischDE.SolveExhaustiveness
import DeepWiki.SymbolicIntegration.Computable.RischDE.ExpPrimCancellation

/-! # The Risch-DE decision procedure

`crischDESolveSoundWf_isDecisionProcedure`: modulo the completeness frontier
`RischDEDecisionProcedureFrontierWf f g` and the soundness certificate `RischDESoundnessWf f g`,
the recursive Risch-DE solver returns `some` iff the field-level RDE is solvable. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## Inner frontier

Bundles the normal-denominator, degree-bound, and solver-exhaustiveness residuals into the
inner-completeness frontier. -/

section InnerFrontierWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- The §6 inner-completeness frontier: the three residual clauses feeding `RischDEInnerCompletenessWf`. -/
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

/-! ## Wf inner input and decision frontier

The field-level Wf residual uses the weak-normalized, reduced pair passed to `crischDERawSolveWf`. Naming that
pair lets the decision-procedure frontier talk about the inner `cRischDEGWf` proof obligation directly, without
restating the §6.1 normalization expression at every field. -/

section InnerInputWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- **The Wf inner RDE input pair**: after fuel-free weak normalization by `q`, reduce the transformed
left-hand side and pair it with `q * g`, exactly as `crischDESolveSoundWf` does before calling
`crischDERawSolveWf`. -/
def rischDEInnerInputWf (f g : QFunNZG β) : QFunNZG β × QFunNZG β :=
  let q : CPolyG β := cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
  let q' : QFunNZG β := qOfPolyNZG q
  (qReduce (weakNormalizedF f q'), qmulNZG q' g)

end InnerInputWf

/-! ## ★ The Wf field-level decision-procedure frontier and the CAPSTONE

The field-level decision procedure now targets `crischDESolveSoundWf`, the fuel-free executable wrapper.
`crischDESolveSoundWf_decides_of_residualWf` consumes the Wf-native residual
`RischDECompletenessResidualWf f g`, whose clauses are stated directly against `cWeakNormalizerGWf` and
`crischDERawSolveWf`. The public frontier below states those clauses through the Wf inner input and a direct
`RischDEInnerCompletenessWf` proof, then derives the residual consumed by the capstone:
`some ⟺ solvable` for the fuel-free solver. The completeness direction is Wf-native; the soundness direction
is supplied by the direct `RischDESoundnessWf` certificate. -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- **The Wf decision-procedure frontier** `RischDEDecisionProcedureFrontierWf f g`: a field-level frontier
whose inner clause is stated through the fuel-free inner API. Besides the two §6.1 completeness clauses
(`hwn`, `hck`), it supplies a polynomial solution for the Wf inner input, a
`RischDEInnerCompletenessWf` proof for that input, and the denominator guard needed to lift
`cRischDEGWf = some _` through `crischDERawSolveWf`. -/
structure RischDEDecisionProcedureFrontierWf (f g : QFunNZG β) : Prop where
  /-- §6.1/Wf: a solvable RDE has a nonzero fuel-free weak normalizer. -/
  hwn : FieldRDESolvable f g →
    CPolyG.cisZeroG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2) = false
  /-- §6.1/Wf: a solvable RDE satisfies the fuel-free canonical-normality guarantee. -/
  hck : FieldRDESolvable f g →
    IsCanonNormalizedWf f
      (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))
  /-- A solvable field RDE has a polynomial solution for the Wf inner input. -/
  hpolysol : FieldRDESolvable f g →
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    ∃ ynum yden,
      IsCRischDEGPolySol ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2
        gtilde.1.1 gtilde.1.2 ynum yden
  /-- The Wf inner completeness proof for the weak-normalized, reduced input pair. -/
  hinner : FieldRDESolvable f g →
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    RischDEInnerCompletenessWf ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2
      gtilde.1.1 gtilde.1.2
  /-- The returned denominator of a successful Wf inner solve is nonzero. -/
  hden : FieldRDESolvable f g → ∀ ynum yden : CPolyG β,
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    cRischDEGWf ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2 gtilde.1.1 gtilde.1.2
        = some (ynum, yden) →
      CPolyG.cisZeroG yden = false

/-- **Assemble the field-level Wf frontier from its Wf inner residual-tip frontier.** -/
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

/-- **The Wf frontier produces the Wf completeness residual**: the `hinner` residual clause is
obtained by feeding the Wf inner-completeness proof through the raw fuel-free solver bridge. -/
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

/-- **★★ The CAPSTONE — `crischDESolveSoundWf` is a VERIFIED DECISION PROCEDURE**
(`crischDESolveSoundWf_isDecisionProcedure`): under the Wf-native frontier
`RischDEDecisionProcedureFrontierWf f g` and the direct Wf soundness certificate
`RischDESoundnessWf f g`, the fuel-free recursive solver returns `some` **iff** the field-level Risch DE is
solvable — `crischDESolveSoundWf f g = some _ ↔ FieldRDESolvable f g`.

The `←` half is Wf-native (`crischDESolveSoundWf_complete_of_residualWf`). The `→` half is the existing
fuel-free soundness wrapper `crischDESolveSoundWf_imp_solvable`, which consumes `RischDESoundnessWf`. -/
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

/-! ### Final verdict (stated precisely)

**Is `crischDESolveSoundWf` a verified decision procedure?** **YES — `some ⟺ solvable`, modulo the
Wf-native §6 frontier and the direct Wf soundness certificate.**
`crischDESolveSoundWf_isDecisionProcedure` proves
`crischDESolveSoundWf f g = some _ ↔ FieldRDESolvable f g` under the Wf consolidated frontier
`RischDEDecisionProcedureFrontierWf f g` and `RischDESoundnessWf f g`. The `←` (completeness) is Wf-native
through `crischDESolveSoundWf_complete_of_residualWf`; the `→` (soundness) is the direct
`crischDESolveSoundWf_field` certificate application.

`rischDEInnerCompletenessWf_of_decisionFrontierWf` assembles the fuel-free inner map through
`RdeNormalDivisibilityResidualWf`, `RdeBoundCancellationResidualWf`, and
`RischDESolveExhaustiveResidualWf`. The public Wf capstone consumes
`RischDEInnerCompletenessWf` directly through the field-level frontier, then uses the §6.1 `hwn`/`hck` plus
the Wf inner-input clauses through `RischDECompletenessResidualWf`. The lift of Wf inner completeness into
the raw-solver `hinner` clause is encoded in
`completenessResidualWf_of_decisionProcedureFrontierWf`. -/

/-! ### Axiom audit (the Wf capstone and inner-frontier assembly are axiom-clean;
NO `native_decide`, NO `sorry`) -/

#print axioms crischDESolveSoundWf_isDecisionProcedure
#print axioms decisionProcedureFrontierWf_of_innerFrontier
#print axioms rischDEInnerCompletenessWf_of_decisionFrontierWf
#print axioms cRischDEGWf_isSome_of_decisionFrontierWf

end DeepWiki.SymbolicIntegration
