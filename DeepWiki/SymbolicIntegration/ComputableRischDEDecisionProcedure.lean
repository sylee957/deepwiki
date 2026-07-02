import DeepWiki.SymbolicIntegration.ComputableRischDESolveExhaustiveness
import DeepWiki.SymbolicIntegration.ComputableRischDENormDivisibility
import DeepWiki.SymbolicIntegration.ComputableRischDEExpPrimCancellation

/-! # ★ The CAPSTONE: `crischDESolveSoundWf` is a VERIFIED DECISION PROCEDURE modulo Wf §6 residuals

This file is the **consolidation** of the §6 Risch-DE completeness arc. The corrected recursive solver
now has a fuel-free wrapper `crischDESolveSoundWf`. Its completeness direction (`solvable ⟹ some`) is stated
against Wf-native stage clauses (`cWeakNormalizerGWf`, `crischDERawSolveWf`); its soundness direction consumes
the direct Wf soundness certificate `RischDESoundnessWf`. Here those pieces compose
into a single crisp, citable statement:

  **`crischDESolveSoundWf` decides field-level RDE solvability**
  (`crischDESolveSoundWf_isDecisionProcedure`): modulo the consolidated Wf frontier
  `RischDEDecisionProcedureFrontierWf f g` and `RischDESoundnessWf f g`, the fuel-free
  solver returns `some` **iff** the RDE is solvable —
  `crischDESolveSoundWf f g = some _ ↔ FieldRDESolvable f g`.

**The consolidated frontier (`RischDEDecisionProcedureFrontierWf`).** The completeness direction is stated
through the fuel-free field-level stages: the Wf weak-normalizer clauses, the Wf inner input passed to
`crischDERawSolveWf`, the Wf inner completeness proof for that input, and the returned-denominator guard needed
to lift a successful `cRischDEGWf` run through the raw wrapper:

| clause | §6 stage | what a solvable RDE must clear | route to a proof |
|---|---|---|---|
| `hwn`  | §6.1 weak-normalizer | `cWeakNormalizerGWf … ≠ 0` | `WeakNormalizer` never vanishes on a solution |
| `hck`  | §6.1 normality | `IsCanonNormalizedWf f q'` | contrapositive of the unsoundness witness |
| `hinner` | §6.2-6.6 inner solve | `RischDEInnerCompletenessWf` for the Wf inner input | Wf-native inner completeness |

The helper `RischDEInnerDecisionFrontierFueled` records the legacy fueled **three irreducible §6 residuals**
named by this arc — one per §6 stage, each carrying its Bronstein theorem and its actionable proof route.
The Wf replacement `RischDEInnerDecisionFrontierWf` keeps the normal-denominator residual fuel-free and feeds
`RischDEInnerCompletenessWf` directly:

| residual (deepest tip) | clause it discharges | Bronstein | route | proven below it |
|---|---|---|---|---|
| `RdeNormalClearedResidual` (`hcleared` = `dₙh²g ∈ k⟨t⟩`, the differential-subring fact) | `hnorm` / `hdvd` | Cor 6.1.1(ii) / Thm 6.1.2 | Mathlib `derivative_rootMultiplicity`, per-pole order via `cValuationG` | the whole UFD/per-pole/arithmetic layer; structural clauses from splitting |
| `RdeBoundCancellationResidual` (deepest correct tip = `ExpPrimLogDerivativeBound`, the log-deriv oracle) | `hbound` | §6.3 Thm 6.3.1 / Lemma 6.3.3-6.3.4 (`λ`-recursion) | log-derivative decision §5.12 | non-cancellation bound + the **nonlinear `λ`-recursion** (proven outright) |
| `RischDESolveExhaustiveResidual{Wf}` (SPDE peeling-divisibility + cancellation-regime exhaustiveness) | `hsolve` | §6.4-6.6 SPDE / poly-RDE | the SPDE peel recursion (peel-step inverse proven) | the engine/base/SPDE-control-flow/preservation layers |

**Soundness is direct at the public boundary.** The `→` of the Wf equivalence is
`crischDESolveSoundWf_field`, which consumes `RischDESoundnessWf`; the decision theorem exposes only the Wf
soundness certificate. The frontier governs only the *converse*
(`solvable ⟹ some`): the fuel-free solver's `none` is certified correct modulo the Wf-native §6 residual. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## Legacy fueled three-residual frontier (one level down: `RischDEInnerCompleteness`)

The legacy fueled map remains here only as an impact-contained bridge for older residual files. The Wf
decision procedure below does not consume this structure; it consumes `RischDEInnerCompletenessWf` directly.
The fueled inner-solve completeness `RischDEInnerCompleteness`, whose three clauses (`hnorm`/`hbound`/`hsolve`)
the proven `rischDEInnerCompleteness_of_residuals` produces from exactly three residuals. We bundle the
**deepest tips** of those three — pushed as far down each chain as the proven layers reach — into one
structure: the differential-subring fact (`hnorm`/`hdvd`), the §6.3 cancellation residual whose correct
deepest tip is the log-derivative oracle (`hbound`), and the SPDE/poly-RDE exhaustiveness (`hsolve`). This is
the precise, citable fueled §6 frontier while Wf counterparts are taking over the public path. -/

section InnerFrontier

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CRischField α]

/-- **The legacy fueled three-residual §6 inner-completeness frontier**
`RischDEInnerDecisionFrontierFueled Dt fnum fden gnum gden`: the deepest tips of the three §6 residuals that, by
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
structure RischDEInnerDecisionFrontierFueled (Dt fnum fden gnum gden : CPolyG α) : Prop where
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

/-- **The fueled three-residual frontier assembles `RischDEInnerCompleteness`**
(`rischDEInnerCompleteness_of_decisionFrontierFueled`): the consolidated
`RischDEInnerDecisionFrontierFueled` produces
the full §6 inner-solve completeness `RischDEInnerCompleteness Dt fnum fden gnum gden`, via the proven
assembly `rischDEInnerCompleteness_of_residuals` (with `hnorm` produced from the `k⟨t⟩`-cleared residual
through `divisibilityResidual_of_cleared` + the benign fuel bound). This is the deep-clause (`hinner`)
half of the decision procedure, reduced to exactly the three named §6 tips. -/
theorem rischDEInnerCompleteness_of_decisionFrontierFueled (Dt fnum fden gnum gden : CPolyG α)
    (h : RischDEInnerDecisionFrontierFueled Dt fnum fden gnum gden) :
    RischDEInnerCompleteness Dt fnum fden gnum gden :=
  rischDEInnerCompleteness_of_residuals Dt fnum fden gnum gden
    (divisibilityResidual_of_cleared Dt fnum fden gnum gden h.hnorm h.hfuel)
    h.hbound h.hsolve

/-- **The three-tip frontier yields the §6.2–6.6 inner-solve exhaustiveness** (`hinner clause`,
`cRischDEG_isSome_of_decisionFrontierFueled`): from the consolidated
`RischDEInnerDecisionFrontierFueled`, a
`cRischDEG`-polynomial-solvable RDE makes the assembled §6 solve return `some` —
`(∃ ynum yden, IsCRischDEGPolySol …) → (cRischDEG Dt towerRischDEFuel …).isSome = true`. This is the
`hsolve` content (the deep clause (c) of the field-level decision procedure) read straight off the three
tips, through `rischDEInnerCompleteness_of_decisionFrontierFueled` and
`cRischDEG_isSome_of_innerCompleteness`. -/
theorem cRischDEG_isSome_of_decisionFrontierFueled (Dt fnum fden gnum gden : CPolyG α)
    (h : RischDEInnerDecisionFrontierFueled Dt fnum fden gnum gden)
    (hsol : ∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    (cRischDEG Dt towerRischDEFuel fnum fden gnum gden).isSome = true :=
  cRischDEG_isSome_of_innerCompleteness Dt fnum fden gnum gden
    (rischDEInnerCompleteness_of_decisionFrontierFueled Dt fnum fden gnum gden h) hsol

/-! ### Restatement against the §6 inner-completeness shape (anonymous `example`) -/

-- ★ The three named §6 tips (the `k⟨t⟩` fact + fuel, the §6.3 cancellation residual, the SPDE/poly-RDE
-- exhaustiveness) genuinely assemble the full §6.2–6.6 inner-solve completeness `RischDEInnerCompleteness`
-- — the deep `hinner` content of the field-level decision procedure — via the proven assembly.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
    [CRischField α] (Dt fnum fden gnum gden : CPolyG α)
    (h : RischDEInnerDecisionFrontierFueled Dt fnum fden gnum gden) :
    RischDEInnerCompleteness Dt fnum fden gnum gden :=
  rischDEInnerCompleteness_of_decisionFrontierFueled Dt fnum fden gnum gden h

end InnerFrontier

/-! ## Wf inner frontier

This is the replacement inner frontier for the public Wf decision path. It keeps both the normal-denominator
and degree-bound residuals fuel-free (`RdeNormalDivisibilityResidualWf`,
`RdeBoundCancellationResidualWf`) and consumes the Wf solver-exhaustiveness residual
`RischDESolveExhaustiveResidualWf`. -/

section InnerFrontierWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- The Wf §6 inner-completeness frontier, with no `towerRischDEFuel` side condition. -/
structure RischDEInnerDecisionFrontierWf (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- §6.2/Wf normal-denominator divisibility residual. -/
  hnorm : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden
  /-- §6.3/Wf degree-bound cancellation residual on the Wf special-cleared coefficients. -/
  hbound : RdeBoundCancellationResidualWf Dt fnum fden gnum gden
  /-- §6.2-6.6/Wf inner solver exhaustiveness residual. -/
  hsolve : RischDESolveExhaustiveResidualWf Dt fnum fden gnum gden

/-- The Wf inner frontier assembles `RischDEInnerCompletenessWf`. -/
theorem rischDEInnerCompletenessWf_of_decisionFrontierWf (Dt fnum fden gnum gden : CPolyG α)
    (h : RischDEInnerDecisionFrontierWf Dt fnum fden gnum gden) :
    RischDEInnerCompletenessWf Dt fnum fden gnum gden :=
  rischDEInnerCompletenessWf_of_residuals Dt fnum fden gnum gden h.hnorm h.hbound h.hsolve

/-- The Wf inner frontier yields fuel-free inner-solver success on polynomial-solvable inputs. -/
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

**The legacy fueled three irreducible §6 residuals (the deepest tips,
`RischDEInnerDecisionFrontierFueled`):**
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

`rischDEInnerCompleteness_of_decisionFrontierFueled` assembles these three into the original fueled
`RischDEInnerCompleteness` map. The Wf replacement
`rischDEInnerCompletenessWf_of_decisionFrontierWf` assembles the fuel-free inner map through
`RdeNormalDivisibilityResidualWf`, `RdeBoundCancellationResidualWf`, and
`RischDESolveExhaustiveResidualWf`. The public Wf capstone consumes
`RischDEInnerCompletenessWf` directly through the field-level frontier, then uses the §6.1 `hwn`/`hck` plus
the Wf inner-input clauses through `RischDECompletenessResidualWf`. The lift of Wf inner completeness into
the raw-solver `hinner` clause is encoded in
`completenessResidualWf_of_decisionProcedureFrontierWf`. -/

/-! ### Axiom audit (the Wf capstone and the three-residual assembly are axiom-clean;
NO `native_decide`, NO `sorry`) -/

#print axioms crischDESolveSoundWf_isDecisionProcedure
#print axioms decisionProcedureFrontierWf_of_innerFrontier
#print axioms rischDEInnerCompleteness_of_decisionFrontierFueled
#print axioms cRischDEG_isSome_of_decisionFrontierFueled
#print axioms rischDEInnerCompletenessWf_of_decisionFrontierWf
#print axioms cRischDEGWf_isSome_of_decisionFrontierWf

end DeepWiki.SymbolicIntegration
