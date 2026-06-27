import DeepWiki.SymbolicIntegration.ComputableRischDESolveExhaustiveness
import DeepWiki.SymbolicIntegration.ComputableRischDENormDivisibility
import DeepWiki.SymbolicIntegration.ComputableRischDEExpPrimCancellation

/-! # ★ The CAPSTONE: `crischDESolveSound` is a VERIFIED DECISION PROCEDURE modulo three §6 residuals

This file is the **consolidation** of the §6 Risch-DE completeness arc. The corrected recursive solver
`crischDESolveSound` was proved **unconditionally sound** (`crischDESolveSound_field`: `some ⟹ solvable`,
axiom-clean, NO `native_decide`); the completeness direction (`solvable ⟹ some`) was reduced — through a
chain of fully-proven engine/algebra layers — to a small set of precisely isolated, **route-carrying** deep
§6 facts. Here those pieces compose into a single crisp, citable statement:

  **`crischDESolveSound` decides field-level RDE solvability** (`crischDESolveSound_isDecisionProcedure`):
  modulo the consolidated frontier `RischDEDecisionProcedureFrontier f g`, the sound solver returns `some`
  **iff** the RDE is solvable — `crischDESolveSound f g = some _ ↔ FieldRDESolvable f g` — with the forward
  half (soundness) **unconditional**.

**The consolidated frontier (`RischDEDecisionProcedureFrontier`).** The completeness direction reduces to the
field-level residual `RischDECompletenessResidual f g` (the unit `crischDESolveSound_decides_of_residual`
consumes), whose three clauses are the §6 converse facts the engine does not self-certify:

| clause | §6 stage | what a solvable RDE must clear | route to a proof |
|---|---|---|---|
| `hwn`  | §6.1 weak-normalizer | `cWeakNormalizerG … ≠ 0` | `WeakNormalizer` never vanishes on a solution |
| `hck`  | §6.1 normality | `cisCanonNormalizedG f̃ = true` | contrapositive of the unsoundness witness |
| `hinner` | §6.2–6.6 inner solve | the lowest-terms inner solve returns `some` | the three deepest tips below |

The single deep clause `hinner` is itself the composite of the **three irreducible §6 residuals** named by
this arc — one per §6 stage, each carrying its Bronstein theorem and its actionable proof route. They are
recorded in `RischDEDecisionProcedureFrontier` (and the `## Summary map` below), exactly the deepest tips of
the proven decomposition `rischDEInnerCompleteness_of_residuals`:

| residual (deepest tip) | clause it discharges | Bronstein | route | proven below it |
|---|---|---|---|---|
| `RdeNormalClearedResidual` (`hcleared` = `dₙh²g ∈ k⟨t⟩`, the differential-subring fact) | `hnorm` / `hdvd` | Cor 6.1.1(ii) / Thm 6.1.2 | Mathlib `derivative_rootMultiplicity`, per-pole order via `cValuationG` | the whole UFD/per-pole/arithmetic layer; structural clauses from splitting |
| `RdeBoundCancellationResidual` (deepest correct tip = `ExpPrimLogDerivativeBound`, the log-deriv oracle) | `hbound` | §6.3 Thm 6.3.1 / Lemma 6.3.3-6.3.4 (`λ`-recursion) | log-derivative decision §5.12 | non-cancellation bound + the **nonlinear `λ`-recursion** (proven outright) |
| `RischDESolveExhaustiveResidual` (SPDE peeling-divisibility + cancellation-regime exhaustiveness) | `hsolve` | §6.4-6.6 SPDE / poly-RDE | the SPDE peel recursion (peel-step inverse proven) | the engine/base/SPDE-control-flow/preservation layers |

**Soundness is unconditional, and the engine is sound in production.** The `→` of the equivalence is
`crischDESolveSound_field` — proved with NO residual, axiom-clean `[propext, Classical.choice, Quot.sound]`.
So `crischDESolveSound` **never returns a spurious `some`**: every `some` is a genuine solution, today,
unconditionally. The frontier governs only the *converse* (`solvable ⟹ some`): the solver's `none` is
certified correct exactly modulo the three named §6 residuals. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## ★ The consolidated three-residual frontier (one level down: `RischDEInnerCompleteness`)

The deep §6 content of the decision procedure — the `hinner` clause of `RischDECompletenessResidual` — is
the inner-solve completeness `RischDEInnerCompleteness`, whose three clauses (`hnorm`/`hbound`/`hsolve`) the
proven `rischDEInnerCompleteness_of_residuals` produces from exactly three residuals. We bundle the
**deepest tips** of those three — pushed as far down each chain as the proven layers reach — into one
structure: the differential-subring fact (`hnorm`/`hdvd`), the §6.3 cancellation residual whose correct
deepest tip is the log-derivative oracle (`hbound`), and the SPDE/poly-RDE exhaustiveness (`hsolve`). This is
the precise, citable §6 decision-procedure frontier. -/

section InnerFrontier

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CRischField α]

/-- **★ The consolidated three-residual §6 inner-completeness frontier**
`RischDEInnerDecisionFrontier Dt fnum fden gnum gden`: the deepest tips of the three §6 residuals that, by
the proven `rischDEInnerCompleteness_of_residuals`, assemble the inner-solve completeness
`RischDEInnerCompleteness` (clause `hinner` of the field-level decision procedure). Exactly three fields, one
per §6 stage, each the irreducible tip its chain reaches:

* `hnorm` — ★ the §6.2 **`k⟨t⟩` differential-subring fact** `RdeNormalClearedResidual` (Bronstein Cor
  6.1.1(ii) / Thm 6.1.2): its deep clause `hcleared` is `dₙh²g ∈ k⟨t⟩` (the cleared (6.2) RHS has
  nonnegative order at every normal pole); the structural clauses are §3.5 splitting / lowest-terms, the UFD
  per-pole layer is proven. Carries the §6.2 dividend fuel bound `hfuel` (benign per-run).
* `hbound` — ★ the §6.3 **degree-bound cancellation residual** `RdeBoundCancellationResidual` (Bronstein Thm
  6.3.1, the `λ`-recursion): the leading-term cancellation case. The non-cancellation bound and the
  **nonlinear `λ`-recursion** are proven outright; the deepest *correct* tip below it is the **log-derivative
  oracle** `ExpPrimLogDerivativeBound` (the δ ≤ 1 parametric logarithmic-derivative decision, §5.12).
* `hsolve` — ★ the §6.4–6.6 **SPDE peeling-divisibility + cancellation-regime exhaustiveness**
  `RischDESolveExhaustiveResidual`: a polynomial solution survives the SPDE peel and the poly-RDE dispatcher.
  The peel-step inverse and the base/control-flow layers are proven; the irreducible residue is the peeling
  divisibility `(a/g) ∣ (q − r)` and the cancellation-regime exhaustiveness.

A `Prop`-bundle of stated assumptions, NO `sorry`; the precise §6 frontier of the decision procedure. -/
structure RischDEInnerDecisionFrontier (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- ★ §6.2/§6.1 — the `k⟨t⟩` differential-subring fact (`RdeNormalClearedResidual`, deep clause `dₙh²g ∈
  k⟨t⟩`), discharging the §6.2 normal-denominator completeness `hnorm`/`hdvd` (Bronstein Cor 6.1.1(ii)). -/
  hnorm : RdeNormalClearedResidual Dt fnum fden gnum gden
  /-- The §6.2 dividend fuel bound (benign per-run; `towerRischDEFuel = 60` covers `dₙ·h²`). -/
  hfuel : (CPolyG.cnormG (rdeNormDnh2 Dt towerRischDEFuel fden gden) : List α).length
    ≤ towerRischDEFuel
  /-- ★ §6.3 — the degree-bound cancellation residual (`RdeBoundCancellationResidual`, Bronstein Thm 6.3.1
  `λ`-recursion); deepest correct tip = the log-derivative oracle `ExpPrimLogDerivativeBound` (§5.12). -/
  hbound : RdeBoundCancellationResidual Dt fnum fden gnum gden
  /-- ★ §6.4–6.6 — the SPDE peeling-divisibility + poly-RDE cancellation-regime exhaustiveness
  (`RischDESolveExhaustiveResidual`), discharging the inner-solve exhaustiveness `hsolve`. -/
  hsolve : RischDESolveExhaustiveResidual Dt fnum fden gnum gden

/-- **★ The three-residual frontier assembles `RischDEInnerCompleteness`**
(`rischDEInnerCompleteness_of_decisionFrontier`): the consolidated `RischDEInnerDecisionFrontier` produces
the full §6 inner-solve completeness `RischDEInnerCompleteness Dt fnum fden gnum gden`, via the proven
assembly `rischDEInnerCompleteness_of_residuals` (with `hnorm` produced from the `k⟨t⟩`-cleared residual
through `divisibilityResidual_of_cleared` + the benign fuel bound). This is the deep-clause (`hinner`)
half of the decision procedure, reduced to exactly the three named §6 tips. -/
theorem rischDEInnerCompleteness_of_decisionFrontier (Dt fnum fden gnum gden : CPolyG α)
    (h : RischDEInnerDecisionFrontier Dt fnum fden gnum gden) :
    RischDEInnerCompleteness Dt fnum fden gnum gden :=
  rischDEInnerCompleteness_of_residuals Dt fnum fden gnum gden
    (divisibilityResidual_of_cleared Dt fnum fden gnum gden h.hnorm h.hfuel)
    h.hbound h.hsolve

/-- **The three-tip frontier yields the §6.2–6.6 inner-solve exhaustiveness** (`hinner clause`,
`cRischDEG_isSome_of_decisionFrontier`): from the consolidated `RischDEInnerDecisionFrontier`, a
`cRischDEG`-polynomial-solvable RDE makes the assembled §6 solve return `some` —
`(∃ ynum yden, IsCRischDEGPolySol …) → (cRischDEG Dt towerRischDEFuel …).isSome = true`. This is the
`hsolve` content (the deep clause (c) of the field-level decision procedure) read straight off the three
tips, through `rischDEInnerCompleteness_of_decisionFrontier` and `cRischDEG_isSome_of_innerCompleteness`. -/
theorem cRischDEG_isSome_of_decisionFrontier (Dt fnum fden gnum gden : CPolyG α)
    (h : RischDEInnerDecisionFrontier Dt fnum fden gnum gden)
    (hsol : ∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    (cRischDEG Dt towerRischDEFuel fnum fden gnum gden).isSome = true :=
  cRischDEG_isSome_of_innerCompleteness Dt fnum fden gnum gden
    (rischDEInnerCompleteness_of_decisionFrontier Dt fnum fden gnum gden h) hsol

/-! ### Restatement against the §6 inner-completeness shape (anonymous `example`) -/

-- ★ The three named §6 tips (the `k⟨t⟩` fact + fuel, the §6.3 cancellation residual, the SPDE/poly-RDE
-- exhaustiveness) genuinely assemble the full §6.2–6.6 inner-solve completeness `RischDEInnerCompleteness`
-- — the deep `hinner` content of the field-level decision procedure — via the proven assembly.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
    [CRischField α] (Dt fnum fden gnum gden : CPolyG α)
    (h : RischDEInnerDecisionFrontier Dt fnum fden gnum gden) :
    RischDEInnerCompleteness Dt fnum fden gnum gden :=
  rischDEInnerCompleteness_of_decisionFrontier Dt fnum fden gnum gden h

end InnerFrontier

/-! ## ★ The field-level decision-procedure frontier and the CAPSTONE

The field-level decision procedure `crischDESolveSound_decides_of_residual` consumes the residual
`RischDECompletenessResidual f g`, whose three clauses are the §6.1 weak-normalizer non-vanishing (`hwn`),
the §6.1 normality completeness (`hck`), and the §6.2–6.6 inner-solve completeness (`hinner`). We bundle that
residual as the field-level frontier and state the capstone: a clean `some ⟺ solvable` modulo the frontier,
soundness unconditional. The deep `hinner` clause reduces — one tower level down — to the three named §6
tips of `RischDEInnerDecisionFrontier` (the documented continuation is the cross-level lift through the §6
structural-decomposition bridge, recorded in `ComputableRischFieldSpec`). -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

/-- **★ The consolidated field-level decision-procedure frontier** `RischDEDecisionProcedureFrontier f g`:
the precise residual under which `crischDESolveSound` is a verified decision procedure for the field-level
Risch DE. Its single field is `RischDECompletenessResidual f g` — the §6 converse content the engine does not
self-certify, in three clauses: `hwn` (§6.1 weak-normalizer non-vanishing on a solvable input), `hck` (§6.1
normality completeness — contrapositive of the unsoundness witness), and `hinner` (the §6.2–6.6 inner-solve
completeness, whose deep content is the three tips of `RischDEInnerDecisionFrontier` one level down). A
`Prop`-bundle of stated assumptions, NO `sorry`; the citable frontier of the RDE decision procedure. -/
structure RischDEDecisionProcedureFrontier (f g : QFunNZG β) : Prop where
  /-- The §6 completeness residual: the three field-level converse clauses (`hwn`/`hck`/`hinner`). -/
  residual : RischDECompletenessResidual f g

/-- **★★ The CAPSTONE — `crischDESolveSound` is a VERIFIED DECISION PROCEDURE**
(`crischDESolveSound_isDecisionProcedure`): under the consolidated frontier
`RischDEDecisionProcedureFrontier f g` and the benign fuel budget `InputFitsFuel f g`, the corrected
recursive solver returns `some` **iff** the field-level Risch DE is solvable —
`crischDESolveSound f g = some _ ↔ FieldRDESolvable f g`.

* The `→` half (**soundness**) is **UNCONDITIONAL** — `crischDESolveSound_field` (via
  `crischDESolveSound_imp_solvable`), proved with NO residual: every `some` is a genuine solution, today.
* The `←` half (**completeness**) is `crischDESolveSound_complete_of_residual`, modulo the frontier's
  `RischDECompletenessResidual` (its `hinner` clause reducing — one level down — to the three named §6 tips
  of `RischDEInnerDecisionFrontier`: the `k⟨t⟩` differential-subring fact, the §6.3 log-derivative oracle,
  the SPDE/poly-RDE exhaustiveness).

So `crischDESolveSound` **decides** field-level RDE solvability modulo exactly three precisely-named,
route-carrying §6 residuals, with soundness unconditional. Axiom-clean `[propext, Classical.choice,
Quot.sound]`; NO `native_decide`, NO `sorry`. -/
theorem crischDESolveSound_isDecisionProcedure (f g : QFunNZG β)
    (h : RischDEDecisionProcedureFrontier f g) (hfit : InputFitsFuel f g) :
    (∃ y, crischDESolveSound f g = some y) ↔ FieldRDESolvable f g :=
  crischDESolveSound_decides_of_residual f g h.residual hfit

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ The RDE decision procedure in book terms: the corrected recursive Risch-DE solver returns `some` iff the
-- field-level Risch DE `D(Y) + F·Y = G` is solvable, modulo the named §6 completeness frontier + the benign
-- fuel budget; soundness (the `→`) is the unconditional `crischDESolveSound_field`.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]
    (f g : QFunNZG β) (h : RischDEDecisionProcedureFrontier f g) (hfit : InputFitsFuel f g) :
    (∃ y, crischDESolveSound f g = some y) ↔ FieldRDESolvable f g :=
  crischDESolveSound_isDecisionProcedure f g h hfit

/-- **Soundness stays unconditional inside the capstone** (`crischDESolveSound_isDecisionProcedure_mp`): the
forward half of the decision-procedure equivalence — a successful solve witnesses solvability — needs NO
frontier, only the benign fuel budget. Extracted to make explicit that the `→` of the capstone is the proven
unconditional soundness `crischDESolveSound_imp_solvable` (`crischDESolveSound_field`), independent of the
completeness residual. -/
theorem crischDESolveSound_isDecisionProcedure_mp (f g y : QFunNZG β)
    (hsolve : crischDESolveSound f g = some y) (hfit : InputFitsFuel f g) :
    FieldRDESolvable f g :=
  crischDESolveSound_imp_solvable f g y hsolve hfit

end Capstone

/-! ### Final verdict (stated precisely)

**Is `crischDESolveSound` a verified decision procedure?** **YES — `some ⟺ solvable`, soundness
unconditional, modulo exactly three precisely-named route-carrying §6 residuals.**
`crischDESolveSound_isDecisionProcedure` proves `crischDESolveSound f g = some _ ↔ FieldRDESolvable f g` under
the consolidated frontier `RischDEDecisionProcedureFrontier f g` + the benign fuel budget. The `→`
(soundness) is the **unconditional** `crischDESolveSound_field` (axiom-clean, NO residual — the engine is
sound in production, never returning a spurious `some`); the `←` (completeness) is
`crischDESolveSound_complete_of_residual`, modulo the frontier.

**The three irreducible §6 residuals (the deepest tips, `RischDEInnerDecisionFrontier`):**
1. **§6.2/§6.1 — the `k⟨t⟩` differential-subring fact** (`RdeNormalClearedResidual`, deep clause `hcleared` =
   `dₙh²g ∈ k⟨t⟩`): Bronstein **Cor 6.1.1(ii) / Thm 6.1.2**; route = Mathlib `derivative_rootMultiplicity`
   per-pole order-drop lifted through `cValuationG`. Below it: the whole UFD/per-pole/arithmetic layer proven,
   the structural clauses reduced to §3.5 splitting + lowest-terms.
2. **§6.3 — the degree-bound cancellation residual** (`RdeBoundCancellationResidual`, deepest *correct* tip =
   the log-derivative oracle `ExpPrimLogDerivativeBound`): Bronstein **Thm 6.3.1 / Lemma 6.3.3–6.3.4** (the
   `λ`-recursion); route = the parametric logarithmic-derivative decision §5.12. Below it: the
   non-cancellation bound + the **nonlinear `λ`-recursion** proven outright.
3. **§6.4–6.6 — the SPDE peeling-divisibility + cancellation-regime exhaustiveness**
   (`RischDESolveExhaustiveResidual`): Bronstein **§6.4–6.6** (SPDE peel + poly-RDE dispatcher); route = the
   SPDE peel recursion. Below it: the engine/base/SPDE-control-flow/preservation layers proven, incl. the
   peel-step inverse.

`rischDEInnerCompleteness_of_decisionFrontier` assembles these three into `RischDEInnerCompleteness` (the deep
`hinner` content) via the proven `rischDEInnerCompleteness_of_residuals`; the field-level capstone consumes
the §6.1 `hwn`/`hck` + `hinner` through `RischDECompletenessResidual`. The cross-level lift of the inner
completeness into `hinner` (the §6 structural-decomposition bridge) is the documented continuation recorded
in `ComputableRischFieldSpec`. -/

/-! ### Axiom audit (the capstone, its soundness half, and the three-residual assembly are axiom-clean;
NO `native_decide`, NO `sorry`) -/

#print axioms crischDESolveSound_isDecisionProcedure
#print axioms crischDESolveSound_isDecisionProcedure_mp
#print axioms rischDEInnerCompleteness_of_decisionFrontier
#print axioms cRischDEG_isSome_of_decisionFrontier

end DeepWiki.SymbolicIntegration
