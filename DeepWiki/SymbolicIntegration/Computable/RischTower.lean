import DeepWiki.SymbolicIntegration.Computable.RischSolver

/-! # `LawfulRischLevel` — the Risch solver as a **typeclass** (write once, assembled)

The `X` / `LawfulX` idiom applied to the Risch integrator. Instead of assembling a `RischSolver` with a
`def` that threads the per-level obligations as parameters (over and over, once per construction), the
obligations are the fields of a **class** `LawfulRischLevel α`. Materialize **one** instance and the whole
solver — `integrate`, `sound`, constructive completeness, and the completeness frontier — is assembled by
instance resolution, parameter-free, wherever `[LawfulRischLevel α]` is in scope.

Because the tower carriers iterate generically (`CField`/`CDiffField`/`CRischField`/`CFracGcdCoreWf` of
`QFunNZG β` are all recursive instances), a recursive instance
`[LawfulRischLevel α] → LawfulRischLevel (QFunNZG α)` (the tower step) then makes solvers at *every* depth
resolve automatically — the base instance and the step instance are each written once. See
`docs/recursive-risch-solver.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The per-level Risch obligations as a class.** The computable data (`case` + `candidates`) and the
soundness/completeness laws, exactly the fields of `RischSolver` — but a **typeclass**, so one `instance`
declaration assembles the solver and everything derived from it by resolution. -/
class LawfulRischLevel (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] where
  /-- The per-monomial-case computable hooks for this level. -/
  case : MonomialCase α
  /-- The level's residue-candidate generator. -/
  candidates : CPolyG α → CPolyG α → CPolyG α → List α
  /-- Special-part soundness + reconstruction (existential special value). -/
  specialSound : ∀ (Dt a d snum sden : CPolyG α),
    case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden) →
    toPolyG sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDerivG Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d
  /-- Reduced-part soundness. -/
  reducedSound : ∀ (Dt a d : CPolyG α) (cands : List α) (nrm : IntegralResultG α),
    case.reducedCorrect Dt (redNorm Dt a d cands) = some nrm →
    toPolyG nrm.rational.2 ≠ 0 ∧ IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm
  /-- Special-part elementarity obstruction (completeness frontier). -/
  SpecElem : CPolyG α → CPolyG α → CPolyG α → Prop
  /-- Normal-part elementarity obstruction (completeness frontier). -/
  NrmElem : CPolyG α → CPolyG α → CPolyG α → Prop
  /-- Completeness descent law. -/
  descend : ∀ (Dt a d : CPolyG α),
    IsElementaryIntegrableG Dt a d → SpecElem Dt a d ∧ NrmElem Dt a d

namespace LawfulRischLevel

/-- **The assembled solver from the level instance.** No parameters — the obligations come from the
`[LawfulRischLevel α]` instance. -/
def solver (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
    [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [LawfulRischLevel α] : RischSolver α where
  case := case
  candidates := candidates
  specialSound := specialSound
  reducedSound := reducedSound
  SpecElem := SpecElem
  NrmElem := NrmElem
  descend := descend

/-- **The assembled integrator** — parameter-free, from the instance. -/
def integrate [LawfulRischLevel α] (Dt a d : CPolyG α) : Option (IntegralResultG α) :=
  (solver α).integrate Dt a d

/-- **Derived soundness** — assembled from the instance, no threaded hypotheses. -/
theorem sound [LawfulRischLevel α] (Dt a d : CPolyG α) (res : IntegralResultG α)
    (h : integrate Dt a d = some res) : IsIntegralResultG Dt a d res :=
  (solver α).sound Dt a d res h

/-- **Derived constructive completeness** — assembled from the instance. -/
theorem isElementaryIntegrable_of_run [LawfulRischLevel α] (Dt a d : CPolyG α)
    (res : IntegralResultG α) (h : integrate Dt a d = some res) : IsElementaryIntegrableG Dt a d :=
  (solver α).isElementaryIntegrable_of_run Dt a d res h

/-- **Derived completeness frontier** — assembled from the instance. -/
theorem not_isElementaryIntegrable [LawfulRischLevel α] (Dt a d : CPolyG α)
    (hobstruct : ¬ SpecElem Dt a d ∨ ¬ NrmElem Dt a d) : ¬ IsElementaryIntegrableG Dt a d :=
  (solver α).not_isElementaryIntegrable Dt a d hobstruct

end LawfulRischLevel

end DeepWiki.SymbolicIntegration
