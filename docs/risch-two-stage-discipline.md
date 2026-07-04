# Risch — the two-stage discipline (abstract architecture ↔ per-solver realization)

This is the organizing discipline for the whole Risch development. It supersedes the ad-hoc wiring that
accreted in `Computable/Assemble.lean` (concrete `cHermiteReduceTowerGWf`/`cSqfreeYunFFGWf`/`QFunNZG ℚ`
lemmas mixed into the assembler). It refines — does not replace — `docs/risch-typeclass-architecture.md`;
that doc describes the *assembler shape*, this one fixes the *proof organization law* it must obey.

## The principle (two stages, 1-1)

**Stage 1 — the architecture is proven abstractly.** The one-level Risch assembler and its
soundness/completeness are stated and proven **only** against stage *interfaces* and their *laws*. No
concrete algorithm name (`cHermiteReduceTowerGWf`, `cSqfreeYunFFGWf`, `cIntegrateReducedGWf`, `QFunNZG ℚ`)
appears anywhere in the architecture file. Stage 1 says: *"Risch is correct given each stage does its job."*

**Stage 2 — each solver realizes its interface, independently.** Every concrete algorithm has **exactly
one** realization theorem: *"this algorithm satisfies its interface's laws."* Proven in that algorithm's
own file, never threaded into the assembler. Stage 2 says: *"this algorithm does its job."*

**Composition is a corollary.** `assembler_sound` (Stage 1) ∘ the realization instances (Stage 2). The
`QFunNZG ℚ` one-shots become one-line corollaries living next to their solvers — not in the architecture.

**1-1 rule.** Every notion carries a matched pair: a **mathematical** statement and an **algorithmic**
statement, greppable and name-paired (see Naming below). Abstract proof ↔ algorithm proof, one to one.

**Center of mass.** The interfaces and the assembler *are* the Risch algorithm. Everything else (Yun,
gcd, RischDE, …) hangs off a realization theorem and is otherwise invisible to the spine.

## Encoding decision — `Lawful` Prop-bundles keyed on the concrete op

Following the repo's `CField`/`LawfulCField` and `@[denote]` idiom (CLAUDE.md): a stage is a **Prop-free
computable op** (already exists — `cSqfreeYunFFGWf`, etc.; keep it `native_decide`-reducible) plus a
**`Lawful…` Prop-bundle** carrying the denotation laws (and any genuine preconditions as hypotheses).
The op stays reducible; the abstract carrier is mentioned only in the `Lawful` half. This preserves the
engine's `native_decide` story while giving the assembler a law-only surface to prove against.

Preconditions that are genuine mathematics (normality `hcopgcd`, rational-residue `hsplit`, input
properness, residue distinctness) live **as fields/hypotheses of the `Lawful` bundle** — they are the
interface's *contract*, not gaps.

## The spine (Bronstein Fig 5.1, the reduced case)

```
a/d  ─canonicalRep→  fp (poly) + b/ds (special) + cn/dn (normal)
cn/dn ─Hermite→       D(g) + h/dr           (dr squarefree, deg h < deg dr)
h/dr  ─ResidueLogPart→ Σ cᵢ D(log vᵢ)       (residues rational)
fp, b/ds ─MonomialCase→ special/poly antiderivative
```

Four interfaces, one assembler.

## The interface stack (signatures + laws + realizers)

Notation: `⟦p⟧ := amG α (toPolyG p) : RatFunc (CFieldSpec.K α)`; `D := towerFractionFieldDerivG Dt`.

### 1. `SquarefreeDecomposition` (leaf; consumed by Hermite)
- **Op** (exists): `cSqfreeYunFFGWf : CPolyG α → List (CPolyG α)` — `d ↦ [v₁,…,vₘ]`, `vᵢ` of multiplicity `i`.
- **`LawfulSquarefreeDecomposition d`** (laws): `Associated (toPolyG d) (prodPow 1 (map toPolyG (op d)))`
  (reconstruction) ∧ each factor squarefree ∧ pairwise `IsRelPrime` ∧ each monic.
- **Realizer** (Stage 2, `YunTowerCorrect`): `cSqfreeYunFFGWf_reconstruction` + `_squarefree` + `_isRelPrime`
  + `cSqfreeYunFFGWf_monic`. **These already exist** — Phase 1 just bundles them.

### 2. `HermiteReduction` (consumes SquarefreeDecomposition)
- **Op** (exists): `cHermiteReduceTowerGWf Dt a d = ((gnum,gden),(hNum,Dstar))`.
- **`LawfulHermiteReduction Dt a d`** (laws, under the normality precondition): `D ⟦gnum/gden⟧ + ⟦hNum/Dstar⟧
  = ⟦a/d⟧` (field identity) ∧ `Squarefree (toPolyG Dstar)` ∧ `(toPolyG hNum).degree < (toPolyG Dstar).degree`
  (properness, for deg Dt ≤ 1) ∧ `toPolyG Dstar = C·nodal(roots)` is *derived*, not assumed.
- **Precondition (contract):** `hcopgcd` (differential normality) + input properness `deg a < deg d` + the
  gcd frontier.
- **Realizer** (Stage 2, new `HermiteReduction`/`.Realization` file): `cHermiteReduceTowerGWf_field_identity`
  (this session), `toPolyG_cHermiteReduceTowerGWf_Dstar_squarefree`, `cHermiteReduceTowerGWf_numer_degree_lt_of_degree_le_one`.

### 3. `ResidueLogPart` (Rothstein–Trager)
- **Op** (exists): the `logs` of `cIntegrateReducedGWf`.
- **`LawfulResidueLogPart Dt hNum Dstar`** (law, under rational-residue + distinctness): `(Σ over logs of cᵢ·D(log vᵢ)) = ⟦hNum/Dstar⟧`.
- **Realizer** (Stage 2): `cIntegrateReducedGWf_logs_eq_per_root` + `primitive_engine_hmatch` and the
  discharges (`hDd`/`hnorm`/`hgcdread` — this session).

### 4. `MonomialCase` (case dispatch; already a record)
- Keep `MonomialCase α` record + `LawfulMonomialCase` (the `integrateSpecial_sound`/`reducedResidual_sound`
  laws). Instances: primitive / hyperexp / tangent.

## The abstract assembler (Stage 1)

`cIntegrateCase_sound` **already** takes `hSpecField`/`hNrmField`/`hrecon` as abstract field identities — it
is *nearly* Stage-1-clean. The work is: (a) repackage those three hypotheses as the `Lawful…` bundles above,
(b) evict every concrete realization from `Assemble.lean`, (c) leave `Assemble.lean` = {assembler def, the
four interface `Lawful` classes, `cIntegrate_sound` against them, `cIntegrate_complete`}.

## Naming convention (1-1, greppable)

- Interface / law: **`<Notion>`** (op, Prop-free) and **`Lawful<Notion>`** (Prop-bundle). Math theorems
  about the abstraction: `Lawful<Notion>.<fact>`.
- Realization: **`<algorithm>_lawful<Notion>`** — the single theorem `Lawful<Notion> … (op := <algorithm>)`.
  (e.g. `cSqfreeYunFFGWf_lawfulSquarefreeDecomposition`, `cHermiteReduceTowerGWf_lawfulHermiteReduction`.)
- No concrete-op name in any Stage-1 theorem; no `Lawful<Notion>`-proof body in the assembler.
- Legacy names migrate gradually (git-mv/rename-only commits), per CLAUDE.md's gradual-improvement rule.

## Evicted (2026-07-04) ✓

The four superseded concrete lemmas + two `local instance`s were REMOVED from `Assemble.lean` — the
interface path (`cIntegrateReducedGWf_isIntegralResult_of_lawful` + the two realizations) supersedes them.
What remains in Assemble: the abstract assembler (`cIntegrateCase`/`cIntegrateCase_sound`), the interface
composition `_of_lawful`, and the end-to-end `_via_interfaces` corollary — all interface-consuming.

## (historical) Was misplaced

`field_identity_of_cIntegrateReducedGWf_of_residueMatch_of_hcopgcd`,
`cIntegrateReducedGWf_isIntegralResult_of_hcopgcd`,
`field_identity_of_cIntegrateReducedGWf_primitive_maximal`,
`cIntegrateGFullWf_primitive_oneShot_hcopgcd_qfunNZG`, and the two `local instance`s — all Stage-2/concrete.
They move to per-solver realization files as the interfaces land.

## Phase plan (dependency-ordered; each phase = one gate-green commit sequence)

- [ ] **P0 — this note.** Fixes the discipline, encoding, interface signatures, naming.
- [x] **P1 — `SquarefreeDecomposition`.** DONE (`SquarefreeDecomposition.lean` interface + `cSqfreeYunFFGWf_lawfulSquarefreeDecomposition` realization in `YunTowerCorrect`). Define the interface + `LawfulSquarefreeDecomposition`; prove
  `cSqfreeYunFFGWf_lawfulSquarefreeDecomposition` bundling the four existing facts. Leaf, no consumers yet.
- [x] **P2 — `HermiteReduction`.** DONE (interface `HermiteReduction.lean` + realization `cHermiteReduceTowerGWf_lawfulHermiteReduction` in `HermiteReductionRealization.lean`; `squarefree` consumed via `LawfulSquarefreeDecomposition.prod_squarefree`). Assemble-file eviction of the residue/one-shot lemmas is P3–P5. Define the interface + `LawfulHermiteReduction` consuming a
  `SquarefreeDecomposition` abstractly (dr-squarefree comes from the interface, not the Yun loop). Prove
  `cHermiteReduceTowerGWf_lawfulHermiteReduction` (this session's `_field_identity` + squarefree + properness).
  Evict the concrete Hermite lemmas from `Assemble.lean` into the realization file.
- [x] **P3 — `ResidueLogPart`.** DONE (interface `ResidueLogPart.lean` + primitive realization `cIntegrateReducedGWf_lawfulResidueLogPart` in `OneShotAssembly`). Eviction of the Assemble one-shots is P5. Define interface + `LawfulResidueLogPart`; prove the `cIntegrateReducedGWf`
  realization. Evict the residue lemmas.
- [x] **P4 (part 1) — abstract composition.** DONE (`cIntegrateReducedGWf_isIntegralResult_of_lawful` in Assemble: `LawfulHermiteReduction` + `LawfulResidueLogPart` → `IsIntegralResultG`, interface-only). Full eviction of the concrete one-shots is P5. Original P4: Restate `cIntegrateCase_sound` to consume `Lawful{Hermite,ResidueLogPart,
  MonomialCase}` + `LawfulSquarefreeDecomposition`. `Assemble.lean` becomes abstract-only.
- [x] **P5 (core) — end-to-end via interfaces.** DONE (`cIntegrateReducedGWf_primitive_isIntegralResult_via_interfaces`: the primitive reduced-part soundness assembled from the two realizations through `_of_lawful`, zero concrete re-derivation). Removing the now-superseded concrete `_of_hcopgcd`/`_maximal`/`_qfunNZG` lemmas from Assemble is the remaining cleanup. Original P5: Primitive/hyperexp/poly one-shots become thin corollaries in their
  solver files (the evicted `_qfunNZG` theorems, now one-liners).
- [ ] **P6 — completeness.** Same discipline: `LawfulDecidesElementary` interface + per-case realizations +
  one abstract `cIntegrate_complete`.
- [ ] **P7 — naming sweep.** Migrate legacy names to the 1-1 convention (rename-only commits).

Rule for every phase: the abstract half and the algorithm half are **separate theorems**, named 1-1; the
assembler never sees a concrete op. Keep this file current as phases land.

## State after P0–P5 (2026-07-04) — the soundness discipline is established

Done, all gate-green:
- **Three shared-stage interfaces** with realizations: `LawfulSquarefreeDecomposition`
  (`cSqfreeYunFFGWf_lawfulSquarefreeDecomposition`), `LawfulHermiteReduction`
  (`cHermiteReduceTowerGWf_lawfulHermiteReduction`, consuming the squarefree interface via
  `prod_squarefree`), `LawfulResidueLogPart` (`cIntegrateReducedGWf_lawfulResidueLogPart` **for both**
  primitive and hyperexp).
- **The assembler consumes interfaces**: `cIntegrateReducedGWf_isIntegralResult_of_lawful`
  (`LawfulHermiteReduction`+`LawfulResidueLogPart` → `IsIntegralResultG`); and
  `cIntegrateCase_sound` was ALREADY Stage-1 abstract (takes `hSpecField`/`hNrmField`/`hrecon`, no concrete
  op in its proof) — the interface work makes `hNrmField` flow through the interfaces.
- **End-to-end** for both solvers: `cIntegrateReducedGWf_{primitive,hyperexp}_isIntegralResult_via_interfaces`
  compose the realizations through the abstract law, zero concrete re-derivation.
- **Assemble cleaned**: the four tangled concrete lemmas + two `local instance`s evicted.

The `MonomialCase` hook already has its abstract law surface (`hSpecField`) consumed by
`cIntegrateCase_sound`; a bundled `LawfulMonomialCase` is optional repackaging.

Remaining (larger, separate): **P6 completeness** — a research frontier (Liouville-descent; the
transcendental log/exp `IsLiouville` instance is not yet in Mathlib), NOT a mechanical discipline
application like soundness was. **P7 naming sweep** — a large gradual legacy-rename effort.
