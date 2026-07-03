# Assemblable Risch — a typeclass architecture for the integrator + its proofs

Goal: dissolve the main↔hyperexp entanglement (see `integral-entanglement.md`) by making the one-level
Risch algorithm **one generic assembler** parameterized by a per-monomial-case typeclass, with soundness
and completeness proven **once** against the class laws instead of per driver.

The design is evolutionary: it reuses the repo's existing idioms — the `CField`/`CFieldSpec` split, the
`X` / `LawfulX` pair, and the `@[denote]` commuting-square discipline (`Computable/Denote.lean`).

## The core idea

Bronstein's Fig. 5.1 is: **shared reductions** (Hermite, polynomial reduction, residue criterion) then a
**case dispatch** (primitive / hyperexponential / hypertangent). Today two drivers hardcode both halves:

- `cIntegrateGFullWf` = canonicalRep + reduced (Hermite+logs) + poly-RDE, requires special part `b = 0`.
- `cIntegrateHyperexpFullGWf` = canonicalRep + reduced + **Laurent special part** + normal RDE correction.

They differ in exactly one thing: **how the special part is integrated.** Everything else (canonicalRep,
Hermite, residue logs, the recombination) is duplicated. That duplicated wiring around a shared core *is*
the entanglement. Abstract the difference into a hook and the drivers become instances.

## Layers

```
Layer 0  Mathlib carriers          K, derivation D, elementary integral, IsLiouville     (proof targets)
Layer 1  Denotation bridge         ⟦⟧ : α → K   (CFieldSpec, CDiffFieldSpec)              (exists)
Layer 2  Shared stages (generic)   canonicalRep · Hermite · residueLogPart               (exists, generic)
           + one commuting-square lemma each, @[denote]
Layer 3  Case typeclass            CMonomialCase α        (Prop-free hooks)               (NEW)
           + LawfulCMonomialCase α (the hook soundness laws)                              (NEW)
Layer 4  Generic assembler         cIntegrate [CMonomialCase α]                           (NEW)
           + cIntegrate_sound  [LawfulCMonomialCase α]   (proven ONCE)
Layer 5  Instances                 Primitive · Hyperexp · Hypertangent                    (thin)
Layer 6  Tower recursion           CMonomialCase (QFunNZG β)  from  [… β]                 (the descent)
```

## Layer 3 — the case typeclass (Prop-free, `native_decide`-friendly)

Only the case-specific hooks live here; the shared stages are generic functions the assembler calls
directly. Keep it Prop-free so the tower still reduces under `native_decide`.

```lean
/-- Per-monomial-case computable hooks for one level of Risch integration over `α(t)`. -/
class CMonomialCase (α : Type*) [CField α] [CDiffField α] where
  /-- The monomial derivative `Dt` (primitive: `∈ α`; hyperexp: `η·t`; tangent: `η(t²+1)`). -/
  Dt : CPolyG α
  /-- Integrate the special/Laurent part `b/dₛ + fₚ` → `Option (rational num, den)`.
      Primitive: the poly-RDE `Dqₚ = fₚ` (special part empty). Hyperexp: `cIntegrateHyperexpLaurentG`.
      Tangent: the coupled-DE box. -/
  integrateSpecial : CPolyG α → CPolyG α → CPolyG α → Option (CPolyG α × CPolyG α)
  /-- The base-residual correction on the reduced part (η·Σcᵢ subtracted via the base RDE);
      identity for the primitive case. -/
  reducedResidual : IntegralResultG α → Option (IntegralResultG α)
```

Instances: `instPrimitiveCase` (special = poly-RDE, `reducedResidual = pure`), `instHyperexpCase`
(`integrateSpecial = Laurent`, `reducedResidual` = the `crischDESolve` subtraction currently inside
`cIntegrateHyperexpNormalGWf`), `instHypertangentCase` (coupled-DE). These are *thin* — each names existing
functions.

## Layer 4 — the generic assembler + one soundness proof

```lean
variable {α} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CMonomialCase α]

/-- One-level Risch integration, generic in the monomial case. -/
def cIntegrate (a d : CPolyG α) (cands : List α) : Option (IntegralResultG α) :=
  let Dt := CMonomialCase.Dt
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFastGWf Dt a d   -- SHARED
  let nrm := cIntegrateReducedGWf Dt cn dn cands                          -- SHARED (Hermite + residue logs)
  match CMonomialCase.reducedResidual nrm with                           -- CASE hook
  | none => none
  | some nrm' =>
    match CMonomialCase.integrateSpecial fp b ds with                    -- CASE hook
    | none => none
    | some (snum, sden) => some (combineRational nrm' snum sden)          -- SHARED
```

The companion carries the commuting squares:

```lean
class LawfulCMonomialCase (α) [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]
    [CMonomialCase α] : Prop where
  integrateSpecial_sound : ∀ fp b ds r, integrateSpecial fp b ds = some r →
    towerFractionFieldDerivG Dt ⟦r⟧ = ⟦specialPart fp b ds⟧
  reducedResidual_sound  : ∀ nrm nrm', reducedResidual nrm = some nrm' →
    ⟦nrm'⟧-differentiates-to ⟦nrm⟧-plus-its-residual
```

and the **single** generic theorem — the thing that today is re-derived per driver in
`OneShotAssembly` / `Hyperexp/FullSoundness`:

```lean
theorem cIntegrate_sound [LawfulCMonomialCase α] (a d : CPolyG α) (cands : List α)
    (res : IntegralResultG α) (h : cIntegrate a d cands = some res) (…side conds…) :
    towerFractionFieldDerivG Dt ⟦res.rational⟧ + logResidueSumG Dt res.logs = ⟦a⟧/⟦d⟧ := …
```

proven from: `canonicalRepresentationFastGWf` faithful (Layer 2 lemma) + `cIntegrateReducedGWf` sound
(Layer 2, the Hermite + Rothstein–Trager squares) + the two hook laws. No per-case reproof.

## Layer 6 — the tower descent (unchanged in spirit)

The recursion `k(t) → k` is already the `CRischField (QFunNZG β)` instance (`Tower/RischDEInstance.lean`).
`CMonomialCase (QFunNZG β)` is built from the level-`β` structure the same way; the assembler at level `n+1`
calls the shared stages over `QFunNZG β` and the hooks recurse into level `n`. Termination bottoms at
`CMonomialCase ℚ` (rational base case, `integrateSpecial = pure`, `reducedResidual = pure`).

## Completeness — the parallel pair

Same shape, decision-valued: `CDecidesElementary α` provides the per-case "no elementary integral" test
(non-constant `r_n` from the residue criterion; RDE `none`), `LawfulCDecidesElementary` proves each test
reflects `¬ IsElementaryIntegral`, and one generic `cIntegrate_none_of_not_elementary` /
`not_elementary_of_cIntegrate_none` assembles from the per-stage completeness lemmas
(`RischDE/Completeness.lean`, the residue-criterion split).

## What this buys / costs

Wins:
- The two drivers collapse to `@cIntegrate _ _ instPrimitive` / `instHyperexp`; the shared hubs are called
  **once**, in the assembler — the duplication (and the cross-lane hub edges) is gone.
- Soundness/completeness proven **once** against class laws; a new monomial case (algebraic, nested) is a
  new instance + two hook lemmas, not a new assembly + a new soundness development.
- `cIntegrateHyperexpG` stays as the deliberate weaker-driver counterexample (it just isn't a
  `LawfulCMonomialCase` instance — that *is* its point).

Cost / risk (honest):
- `OneShotAssembly` (~98 refs) and `Hyperexp/FullSoundness` are written against the concrete `cIntegrateGFullWf`
  / `cIntegrateHyperexpFullGWf`. Migration is: (1) introduce the classes + generic assembler, (2) prove the
  concrete drivers *equal* `@cIntegrate _ _ inst…` (a `native_decide`/`rfl`-level bridge), (3) re-express the
  existing soundness as corollaries of `cIntegrate_sound` through that bridge, (4) retire the bespoke
  assemblies. Each step gate-green; the driver-equality bridge (step 2) de-risks the proof migration.

## Phases

- [ ] P1 — `CMonomialCase` + `instPrimitiveCase`/`instHyperexpCase`, generic `cIntegrate`; prove
  `cIntegrateGFullWf = @cIntegrate _ _ instPrimitiveCase` and
  `cIntegrateHyperexpFullGWf = @cIntegrate _ _ instHyperexpCase` (bridge lemmas).
- [ ] P2 — `LawfulCMonomialCase` + `cIntegrate_sound`; re-derive the two drivers' soundness as corollaries.
- [ ] P3 — `CDecidesElementary` / completeness assembly.
- [ ] P4 — retire the bespoke assemblies; `instHypertangentCase` folds the CoupledDE arc in too.
