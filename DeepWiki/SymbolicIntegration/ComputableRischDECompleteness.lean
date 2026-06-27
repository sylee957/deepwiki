import DeepWiki.SymbolicIntegration.ComputableRischDESolveSound

/-! # §6 RDE decision-procedure COMPLETENESS — `solvable ⟹ some` (the converse of soundness)

`ComputableRischDESolveSound` proved the corrected recursive Risch-DE solver `crischDESolveSound`
**sound**: `crischDESolveSound f g = some y → D(Y) + F·Y = G` at the field level, **unconditionally**
(`crischDESolveSound_field`; the §6.1 check `cisCanonNormalizedG` supplies the normality, so no
`IsCanonNormalized` hypothesis). That is the `some ⟹ correct` half. This file pursues the **converse**,
`solvable ⟹ some` — together making the solver a verified **DECISION PROCEDURE**
(`some ⟺ solvable`).

**The structure of completeness.** `crischDESolveSound f g` produces `none` on exactly four branches:

1. **§6.1 weak-normalizer vanishes** — `cWeakNormalizerG … = 0` (`cisZeroG q`);
2. **§6.1 normality check fails** — `cisCanonNormalizedG f̃ = false`;
3. **the lowest-terms reduction fails** — `reduceSoundOpt f̃ = none` (impossible: `reduceSoundOpt_eq`);
4. **the inner recursive solve fails** — `crischDESolve (qReduce f̃) (q'·g) = none`.

So a `none` result decomposes structurally into these four cases (`crischDESolveSound_eq_none_iff`,
fully reachable). Completeness — `solvable ⟹ ¬ none` — is then **exactly** the conjunction of four
stage-completeness facts: a solvable RDE has (1) a non-vanishing weak normalizer, (2) a passing §6.1
check, (3) a successful reduction (free), and (4) a successful inner solve. Branch (3) is closed
unconditionally; branches (1), (2), (4) are the genuine §6 completeness content.

**What is reachable here.**
* **The structural `none`-characterization** `crischDESolveSound_eq_none_iff` — the exact four-way
  disjunction a `none` reduces to (the control-flow skeleton, no §6 mathematics).
* **The base-field completeness** `rischDE_complete_base` — over the constant base `ℚ` (`D = 0`),
  `crischDESolve` is the direct division `g/b`, so it is **decidably complete**: an RDE `b·y = g`
  has a solution iff `crischDESolve b g = some _` (axiom-clean, no `native_decide`).
* **The reduction of completeness to the deep §6 stages** — `crischDESolveSound_complete_of_residual`:
  modulo the isolated residual `RischDECompletenessResidual` (the three deep stage-completeness facts),
  `solvable ⟹ some`. With soundness this gives `some ⟺ solvable` modulo the residual
  (`crischDESolveSound_decides_of_residual`).

**The deep §6 residual (precisely isolated, NEVER `sorry`).** The genuine content of completeness — that
a solvable RDE survives every §6 `none`-gate — is bundled in `RischDECompletenessResidual`. Its three
clauses are the converse directions the soundness layer never needed and the engine does **not**
self-certify: (a) the §6.1 weak-normalizer non-vanishing, (b) the §6.1 normality completeness
(`solvable ⟹ check passes` — the contrapositive of the unsoundness witness, i.e. a non-normalizable
denominator's RDE is genuinely unsolvable), and (c) the **§6.4 degree-bound + SPDE + poly-RDE
completeness** (any field solution has bounded degree and is found by the bounded polynomial solve). Clause
(c) is the research-grade core: it requires the §6.4 degree bound to be a *provable upper bound on any
solution's degree* and the SPDE/poly-RDE solve to be *exhaustive within the bound* — neither of which is
formalized anywhere in the engine (only the soundness cleared-identity is). This file states it precisely
and proves completeness *modulo* it; it is the honest §6 decision-procedure frontier. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The field-level RDE solvability predicate `FieldRDESolvable`

`FieldRDESolvable f g` is the existence of a `QFunNZG β` solution to the field-level Risch DE
`D(Y) + F·Y = G`, phrased through the *exact* expression of `crischDESolveSound_field`'s conclusion
(`towerFractionFieldDerivG` + `amG ∘ toPolyG` readings). This is the "solvable" side of the decision
procedure: soundness says `some ⟹ FieldRDESolvable`, completeness says `FieldRDESolvable ⟹ some`. -/

section Solvable

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

/-- **Field-level RDE solvability** `FieldRDESolvable f g`: there exists `y : QFunNZG β` solving the
field-level Risch differential equation `D(Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`, read through
`amG ∘ toPolyG` exactly as `crischDESolveSound_field`'s conclusion. The "solvable" side of the decision
procedure: soundness gives `crischDESolveSound f g = some _ → FieldRDESolvable f g`; completeness is the
converse `FieldRDESolvable f g → crischDESolveSound f g = some _`. -/
def FieldRDESolvable (f g : QFunNZG β) : Prop :=
  ∃ y : QFunNZG β,
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2)

/-- **Soundness, restated as `some ⟹ solvable`** (`crischDESolveSound_imp_solvable`): a successful sound
solve `crischDESolveSound f g = some y` witnesses `FieldRDESolvable f g` (take the returned `y`). The
forward half of the decision-procedure equivalence; the capstone `crischDESolveSound_field` supplies the
identity. -/
theorem crischDESolveSound_imp_solvable (f g y : QFunNZG β)
    (hsolve : crischDESolveSound f g = some y) (hfit : InputFitsFuel f g) :
    FieldRDESolvable f g :=
  ⟨y, crischDESolveSound_field f g y hsolve hfit⟩

end Solvable

end DeepWiki.SymbolicIntegration
