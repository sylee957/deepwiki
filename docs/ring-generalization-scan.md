# Scan: generalize the polynomial engine to a *ring* coefficient (field as a specialization)

**Proposal.** Today `CPoly α` requires `[CField α]` — the coefficient must be a computable *field*. That is
why bivariate polynomials (polys-over-polys) can't reuse the engine: `CPolyQ = CPoly ℚ` is a *ring*, not a
field, so `CPoly CPolyQ` doesn't typecheck. Generalize the coefficient constraint to a computable
**commutative ring** (`CCommRing`), make `CField` *extend* it, and bivariate polynomials become
`CPoly (CPoly _)` — no separate definition.

## Finding 1 — the engine is already ~95 % ring-level

Of the 21 core `c*` ops in `Polynomial`, **20 use only `add`/`mul`/`neg`/`isZero`** (ring ops):
`cadd cmul cneg csub cscale cshift cnorm clead cdeg cisZero cpow cprod ceval cderiv cnsmul cMonomial
cfpow cpad creverseDeg cisMonic`. **Exactly one — `cmonic`** (divide by the leading coefficient) — uses
`CField.div`. So the op *bodies* barely change under generalization; only their typeclass *constraint*
(`[CField α]` → `[CCommRing α]`) and the denotation bridge do.

Field-only ops that legitimately **stay `[CField]`**: `cmonic`, `cdiv`/`cmod`/`cdivmod`, `cgcd*`,
`cinv`, `cinterpolate` (needs `1/(node differences)`), Euclidean-`cresultant`. Engine-wide, only ~46
files touch `CField.inv`/`CField.div`.

## Finding 2 — three parallel "list-of-CPoly" layers exist *only* because of the field constraint

| layer | definition | why it exists | size |
|---|---|---|---|
| `BPoly` | `List CPolyQ` (Compute/Subresultant) | bivariate ℚ subresultants; `CPolyQ` isn't a field | 204 lines of `b*` ops + `SubresultantCorrectness` cluster (1278 lines / 7 files) |
| `GBPolyCore B` | `List (CPoly B)` (Tower/GcdFFCore) | fraction-free gcd over `CPoly B` coefficients | 11 files use `GBPoly*` |
| `GBPoly B` | `List (CPoly B)` (Tower/GcdFF/Carrier) | **exact duplicate** of `GBPolyCore` | — |

All three *are* `CPoly (CPoly _)`. Each `b*`/GB op is a hand-written copy of a `c*` op specialized to a
polynomial coefficient — e.g. `badd` = coefficientwise add of `List CPolyQ` = exactly `cadd @ CPolyQ`
*if* `CPolyQ` were an allowed (ring) coefficient. Their gcd machinery (`bpsremainder`,
`bsubresultantGcd`, fraction-free `GBPoly` gcd) is **pseudo-division-based** — i.e. deliberately
ring-level (no coefficient inversion) — so it composes cleanly over a ring coefficient.

## What gets cleaned

- **`BPoly` and its `b*` ops collapse into `CPoly CPolyQ`** (defeq: `CPoly CPolyQ = List CPolyQ = BPoly`),
  and each `b*` op becomes `c* @ CPolyQ`. The bivariate subresultant development (≈ **1480 lines** across
  `Compute/Subresultant` + the 7-file `SubresultantCorrectness/` cluster) mostly evaporates — replaced by
  *instantiating* the generic subresultant at a ring coefficient.
- **`GBPolyCore` and `GBPoly` unify** into `CPoly (CPoly B)` and the **duplicate is deleted**.
- One conceptual polynomial engine instead of four representations (`CPoly`, `BPoly`, `GBPoly`,
  `GBPolyCore`); the `RadElem = List α` radical carrier is a *different* concept and is unaffected.

## What it costs (the generalization, not deletion)

Foundational but largely *mechanical* (op bodies unchanged):
1. **New class hierarchy.** `CCommRing α` (zero/one/add/mul/neg/isZero + a `CRingSpec` bridge `toR : α → R`
   into a Mathlib `CommRing R`); `CField extends CCommRing` (adds `inv` + the field bridge `toK`, with
   `R = K`). Mirror `CFieldSpec`/`CDiffFieldSpec` with `CRingSpec` bases.
2. **Weaken constraints.** ~754 `[CField α]`/`[CFieldSpec α]` binders; the ring-level majority become
   `[CCommRing α]`/`[CRingSpec α]`, the ~46 field-touching files keep `[CField]`. Mechanical, but wide.
3. **Re-target the denotation.** `toPoly : CPoly α → (CFieldSpec.K α)[X]` becomes
   `CPoly α → (CRingSpec.R α)[X]` over a `CommRing`; the ~150 `@[denote]`/homomorphism squares weaken
   their coefficient constraint (statements unchanged, `Field`→`CommRing`).
4. **Instance plumbing.** Provide `CCommRing (CPoly α)` (a `CPoly` over a ring is itself a ring
   coefficient) so `CPoly (CPoly _)` resolves — this is the keystone instance that makes bivariate work.

## Feasibility & recommendation

**Feasible and genuinely cleaning** — the 20/21 ring-level finding means this is constraint-weakening +
a class-hierarchy split, not an algorithm rewrite, and it removes ~1500 lines of duplicated bivariate
machinery plus a duplicate GBPoly. But it is a **foundational, multi-phase** refactor (on the order of the
fuel retirement or the `CFrac` move): the `CField`/`CFieldSpec` split touches the whole engine.

Recommended phasing (each gate-green):
1. Introduce `CCommRing`/`CRingSpec`; make `CField extends CCommRing`, `CFieldSpec extends CRingSpec`
   (`R := K`) — no call-site changes yet (CField still resolves everything).
2. Add the keystone `CCommRing (CPoly α)` instance + `toR` denotation into `(R α)[X][Y]`-style tower.
3. Weaken the 20 ring-level `c*` ops + their squares from `[CField]`/`[CFieldSpec]` to
   `[CCommRing]`/`[CRingSpec]` (mechanical, batch by op family).
4. Collapse `BPoly` → `CPoly CPolyQ` and its `b*` ops → `c* @ CPolyQ`; migrate `SubresultantCorrectness`
   to the generic subresultant; delete the bivariate duplication.
5. Unify `GBPoly`/`GBPolyCore` → `CPoly (CPoly B)`; delete the duplicate.

Net: **large touch surface (~754 constraints), large cleanup (~1500 lines + a duplicate + 3 layers → 1)**.
Worth doing; do it as a dedicated phased arc after the current naming/reorg work settles.

## Empirical outcome (2026-07-09, arc complete — see `ring-generalization-plan.md`)

The architecture generalization landed in full (P1–P3: `CCommRing`/`CRingSpec` base + keystones
`CCommRing (CPoly α)` and `CRingSpec (CPoly α)`; `native_decide` survives; the whole engine is now
ring-coefficient-generic with `CField` a specialization). The bivariate collapse landed as far as is
**correct and safe** (P4a/b, P5a/b/c): all three `List (CPoly _)` carriers' **arithmetic now IS the generic
engine** (thin `c*` wrappers), the dead `GBPoly` op set + the duplicate `GcdFF` denominator subtree are
**deleted**, and `GBPoly` no longer exists.

**But the "~1500 lines evaporate" estimate was optimistic.** The genuinely-duplicate code was small — the
dead `GBPoly` ops (~75 L) + the `b*`/`gb*Core` arithmetic recursions (~60 L) + the duplicate denominator
helpers — netting **≈ −46 lines** over the P4/P5 arc (the generalization adds base classes + bridge lemmas
that offset raw deletions). The BULK the scan expected to remove is **genuine content, not duplication**:
- the generic `cSubresultant` is **determinant-based**, a *different algorithm* than the PRS
  `bpsremainder`/`gbpsremainderCore` — so `SubresultantCorrectness` (1278 L) is genuine subresultant-PRS
  correctness, not a redundant copy;
- the `bnorm`/`gbnormCore` **canonicalizing** normalization is a real op (not `cnorm @`);
- Compute's PRS duplicate of `GBPolyCore` (`BPoly = GBPolyCore ℚ`) is left **deliberately**: unifying it
  would make the concrete `Compute/` reference layer depend on the generic `Engine/Tower` gcd engine,
  inverting the intended layering.

The real win is the **architecture** (one ring-generic engine; bivariate polys are `CPoly (CPoly _)` going
through it), not a large line-count deletion.
