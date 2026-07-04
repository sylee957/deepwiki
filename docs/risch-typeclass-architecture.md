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
         Residue source            CResidueSource α       (automates `cands`)             (NEW)
           + LawfulCResidueSource α (the completeness law only)                           (NEW)
Layer 4  Generic assembler         cIntegrate [CMonomialCase α] [CResidueSource α]        (NEW)
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

## Layer 3b — automated residue candidates (`CResidueSource`)

Today `cands : List α` is a manual parameter: the residues are the roots of the Rothstein–Trager resultant
`R(z) = cResidueResultantTowerGWf Dt cn dn`, so they depend on the integrand, and the Prop-free engine has
no root/factor oracle — so the caller supplies candidates and `cRationalResiduesGWf` **filters** them to the
genuine roots (`R(c)=0`). Candidate generation is a property of the **constant field of `α`**, independent of
the monomial case, so it is its own class keyed on `α`:

```lean
/-- Computable source of residue candidates: given the RT resultant `R ∈ α[z]`, produce candidates `c ∈ α`. -/
class CResidueSource (α : Type*) [CField α] where
  residueCandidates : CPolyG α → List α
```

Because `cRationalResiduesGWf` filters to genuine roots, **soundness holds for any source** — a wrong or
partial list can only drop terms, never fabricate one. So the source's only law is a **completeness**
obligation (return every constant root of `R`):

```lean
class LawfulCResidueSource (α) [CField α] [CFieldSpec α] [CResidueSource α] : Prop where
  residueCandidates_complete : ∀ R (c : α),
    IsConstant c → (⟦R⟧).eval ⟦c⟧ = 0 → c ∈ residueCandidates R
```

Instances: `CResidueSource ℚ` = rational-root enumeration on `R`
(`±(divisors of constant-coeff numerator)/(divisors of leading)`) — sound always, `Lawful` for the
rational-residue slice (what the `native_decide` examples exercise); `CResidueSource (QFunNZG β)` reads the
constant part of `R`'s `ℚ(x)`-coefficients and delegates to the ℚ enumerator. **Frontier:** irrational
algebraic residues (roots of `R` in an extension of ℚ) need Bronstein's `factor(R)` + symbolic `K(α)`
arithmetic — a richer instance you swap in; the default ℚ instance is sound-but-incomplete there, and
`LawfulCResidueSource` documents exactly where completeness holds.

## Layer 4 — the generic assembler + one soundness proof

```lean
variable {α} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CMonomialCase α] [CResidueSource α]

/-- One-level Risch integration, generic in the monomial case. No manual `cands`. -/
def cIntegrate (a d : CPolyG α) : Option (IntegralResultG α) :=
  let Dt := CMonomialCase.Dt
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFastGWf Dt a d    -- SHARED
  let R     := cResidueResultantTowerGWf Dt cn dn                         -- SHARED (compute the resultant)
  let cands := CResidueSource.residueCandidates R                         -- AUTOMATED — no caller param
  let nrm   := cIntegrateReducedGWf Dt cn dn cands                        -- SHARED (Hermite + residue logs)
  match CMonomialCase.reducedResidual nrm with                           -- CASE hook
  | none => none
  | some nrm' =>
    match CMonomialCase.integrateSpecial fp b ds with                    -- CASE hook
    | none => none
    | some (snum, sden) => some (combineRational nrm' snum sden)          -- SHARED
```

`cIntegrateReducedGWf` keeps its explicit `cands` internally (it is the mechanism); the source supplies it
at the top, so the ~50 soundness signatures that thread `cands` are untouched — only the public entry drops
it. The companion carries the commuting squares:

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
theorem cIntegrate_sound [LawfulCMonomialCase α] (a d : CPolyG α)
    (res : IntegralResultG α) (h : cIntegrate a d = some res) (…side conds…) :
    towerFractionFieldDerivG Dt ⟦res.rational⟧ + logResidueSumG Dt res.logs = ⟦a⟧/⟦d⟧ := …
```

proven from: `canonicalRepresentationFastGWf` faithful (Layer 2 lemma) + `cIntegrateReducedGWf` sound
(Layer 2, the Hermite + Rothstein–Trager squares) + the two hook laws. **Note it needs no
`LawfulCResidueSource`** — the residue filter makes soundness independent of the candidate source;
`LawfulCResidueSource` is consumed only by the *completeness* theorem (Layer, below).

## Layer 6 — the tower descent (unchanged in spirit)

The recursion `k(t) → k` is already the `CRischField (QFunNZG β)` instance (`Tower/RischDEInstance.lean`).
`CMonomialCase (QFunNZG β)` is built from the level-`β` structure the same way; the assembler at level `n+1`
calls the shared stages over `QFunNZG β` and the hooks recurse into level `n`. Termination bottoms at
`CMonomialCase ℚ` (rational base case, `integrateSpecial = pure`, `reducedResidual = pure`).
`CResidueSource (QFunNZG β)` likewise delegates to `CResidueSource ℚ` — residues are constants in `C = ℚ`
regardless of tower depth, so the ℚ enumerator is the single base of that descent too.

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

## Status (landed)

`Computable/Assemble.lean` (commits 4b19bd7f, a855892d), gate-green:

- **Design refinement.** `CMonomialCase` is realized as a **`MonomialCase α` record**, not an α-resolved
  typeclass: primitive and hyperexp both live over the *same* `α`, so instances would conflict. The
  assemblable component is a record (`integrateSpecial` / `reducedCorrect` hooks) passed explicitly. Same
  "plug in a case" idea; correct Lean encoding.
- **P1 done.** `cIntegrateCase (C : MonomialCase α) Dt a d cands`, with `primitiveCase` and `hyperexpCase`.
  Bridge `cIntegrateHyperexpFullGWf = cIntegrateCase hyperexpCase` holds by **`rfl`** (the hyperexp driver's
  combine is already the uniform fraction form). `native_decide` validates the assembler reproduces
  `checkIdentityG` on the primitive (∫1/t²) and hyperexp (∫1/exp, special+normal mix) cases.
- **P2 done.** `cIntegrateCase_sound` proves `D(res.rational) + logResidueSum res.logs = a/d` for the generic
  assembler **once**, from the two abstract hook field-identities (`hSpecField`, `hNrmField`) + the canonical
  reconstruction, via the `combineSN` algebra — independent of the monomial case. **Both** transcendental
  cases are corollaries: `cIntegrateCase_hyperexp_sound` (special value `⟦fpPart⟧`, Laurent/normal solves)
  and `cIntegrateCase_primitive_sound` (special part `qₚ/1` from the `b=0` RDE, uncorrected reduced) — the
  latter is what the `rfl` bridge alone could not give.
- **P2+ started — discharging the hypotheses from deep stage lemmas.** `cIntegrateCase_primitive_sound_polyRDE`
  (canonical primitive `Dt=1`, `fₚ≠0`) drops `hSpecField`: it follows from `cPolyRischDEGWf_nil_field_identity`
  (the engine's own poly-RDE soundness). First case law discharged.

### Unconditionality dependency map (what's left for "sound, full stop")

Each corollary still consumes `hNrmField` (shared reduced identity) + `hrecon` (canonical reconstruction),
and hyperexp still consumes `hLaurField`. Status of the deep lemmas that would discharge them:

| hypothesis | deep lemma | status |
| --- | --- | --- |
| primitive `hSpecField` | `cPolyRischDEGWf_nil_field_identity` | **exists — discharged** |
| `hrecon` (canonical) | `canonicalReconstruction` (new) | **discharged, modulo the split frontier** |
| `hNrmField` (reduced) | `cIntegrateReducedGWf_isIntegralResult` (new) | **wired — reduces to Hermite + RT frontier** |
| split factorization `d = dₛ·dₙ` (special·normal) | `cSplitFactorFastGWf_isSplittingFactorizationGen` (new) | **PROVEN abstractly (uncond. at ℚ; general modulo `GcdFFCorrect`)** |
| Hermite half `hherm` | `cHermiteReduceTowerGWf` | **DISCHARGED (2026-07-04)** — `cHermiteReduceTowerGWf_field_identity` proves it abstractly modulo only `hcopgcd` (differential normality); wired via `field_identity_of_cIntegrateReducedGWf_of_residueMatch_of_hcopgcd` and `cIntegrateReducedGWf_isIntegralResult_of_hcopgcd`. No longer `native_decide`-only. |
| RT residue match — `hform` core | `cIntegrateReducedGWf_logs_eq_per_root` | **already abstract** (via `residue_gcd_eq_linear_factor` + `cLogArgTowerGWf_eq_linear_factor`); takes `hden`/`hres`/`hDd`/`hdist`/`hcand`/`hgcdread` as side conditions. |
| RT residue match — `hden` | `toPolyG_cHermiteReduceTowerGWf_Dstar_eq_nodal` | **DISCHARGED (2026-07-04)** — `Dstar = nodal(roots)` modulo only `hsplit` (rational-residue split); monic + squarefree proven from the Yun structure (`YunTowerCorrect`). No longer `native_decide`-only. |
| RT residue match — `hDd` | `implicitDeriv_C_nodal_eval_ne_zero` | **DISCHARGED (2026-07-04)** — resolvent derivative ≠ 0 at roots, modulo constant roots + `w ≠ 0` (`mapCoeffs(nodal)=0` for constant roots + `Lagrange.nodalWeight`). |
| RT residue match — `hnorm` | `primitive_monomial_norm_of_const_roots` | discharged modulo constant roots + `w ≠ 0` (pre-existing). |
| RT residue match — `hdist` | — | **GENUINE side condition** (residue distinctness); correctly a hypothesis, not a gap. |
| RT residue match — `hres` | — | **engine-external** (caller enumerates residue candidates); correctly a hypothesis. |
| RT residue match — `hcand`, `hgcdread` | `cRationalResiduesGWf`, `cLogArgTowerGWf` | engine-compute frontier (residue values + log-arg gcd); real arcs, still `native_decide`-only. |
| leftover properness `hA` | degree induction over the Hermite fold | the "Large residual"; needs the abstract Hermite identity (now DONE) **plus** a tower `hermiteReducePower_remainder_degree` induction. Still open. |

**Composed (2026-07-04):** `field_identity_of_cIntegrateReducedGWf_primitive_maximal` (Assemble) assembles the
whole primitive reduced case discharging `hherm`/`hden`/`hnorm`/`hDd` internally; its remaining inputs are
exactly `hA` (Large residual), `hdist`/`hres` (genuine/external), `hcand`/`hgcdread` (engine-compute).
| RT residue match `hmatch` | Rothstein–Trager residue↔root | frontier (`native_decide`-only) |
| hyperexp `hLaurField` (Laurent) | `cIntegrateHyperexpLaurentG_special_sound` (new) | **PROVEN modulo special-part shape** |

**`cSplitFactorFastGWf` split correctness is now PROVEN** (`SplitFactorWfCorrect.lean`, not `native_decide`):
M1 per-step bridge `cstepGWf ~ splitFactorStep` → M2 well-founded recursion → `IsSplittingFactorizationGen`
(`toPolyG d = toPolyG dₛ · toPolyG dₙ`, `dₛ` special, `dₙ` normal-squarefree), reduced to a single gcd
frontier `GcdFFCorrect` and **discharged unconditionally at the ℚ base** (`gcdFFCorrect_Q`, where the
fraction-free gcd is the plain monic Euclidean gcd). This feeds `hsplit` in `canonicalReconstruction`
(the `d = dₛ·dₙ` part; `hgdeg`/`hgne` coprimality is the small remaining piece). One of the three
engine-compute frontiers is now off the `native_decide`-only list.

`canonicalReconstruction` assembles `toPolyG_cdivmodWf` + `toPolyG_cbezoutOneWf` +
`toPolyG_cextendedEuclideanSplitWf` + `canonicalRepFast_field_identity`, so `hrecon` reduces to
`cSplitFactorFastGWf` split-correctness. `cIntegrateReducedGWf_isIntegralResult` restates
`field_identity_of_cIntegrateReducedGWf_of_residueMatch` as `IsIntegralResultG`, so `hNrmField` reduces to
the Hermite half + the RT residue match. `cIntegrateCase_primitive_sound_full` already discharges
`hSpecField` (poly-RDE) and `hrecon`.

**Net for the primitive case:** `cIntegrateCase_primitive_sound_full ∘ cIntegrateReducedGWf_isIntegralResult_of_hcopgcd`
is sound given **two named engine-compute frontiers plus one genuine side condition** — `cSplitFactorFastGWf`
split correctness (PROVEN, gcd-only), the RT residue match (still `native_decide`-only), and `hcopgcd`
(the differential-normality side condition, a *genuine* Bronstein hypothesis, not a gap). **The
`cHermiteReduceTowerGWf` Hermite half is now abstract** (2026-07-04 pole-cancellation arc): the reduced
identity `hNrmField` is produced by `cIntegrateReducedGWf_isIntegralResult_of_hcopgcd` from `hcopgcd` +
`hmatch`, replacing the old `native_decide`-only Hermite frontier. So of the original three engine-compute
frontiers, two are discharged (split, Hermite) and only the **RT residue match** remains `native_decide`-only.

- Open: the three engine-compute frontiers above (each `native_decide`-only — the abstract-correctness
  frontier the whole engine shares); Laurent soundness (hyperexp); `LawfulMonomialCase` bundled Prop;
  `CResidueSource` (P0); completeness (P3).

## Phases

- [ ] P0 — `CResidueSource α` + `CResidueSource ℚ` (rational-root enumeration) + `CResidueSource (QFunNZG β)`
  (delegate to ℚ). Self-contained and additive: gives "no manual `cands`" ergonomics via a top wrapper
  `cIntegrateGFullAutoWf a d := cIntegrateGFullWf a d (residueCandidates (cResidueResultantTowerGWf …))`
  *before* any assembler work; validate it reproduces the hand-built `cands` on the existing examples.
- [ ] P1 — `CMonomialCase` + `instPrimitiveCase`/`instHyperexpCase`, generic `cIntegrate` (consuming
  `CResidueSource`); prove `cIntegrateGFullWf a d cands = @cIntegrate _ _ instPrimitiveCase a d` when
  `cands` covers the residues, and likewise for `cIntegrateHyperexpFullGWf` (bridge lemmas).
- [ ] P2 — `LawfulCMonomialCase` + `cIntegrate_sound`; re-derive the two drivers' soundness as corollaries.
- [ ] P3 — `CDecidesElementary` + `LawfulCResidueSource`-consuming completeness assembly.
- [ ] P4 — retire the bespoke assemblies; `instHypertangentCase` folds the CoupledDE arc in too.
