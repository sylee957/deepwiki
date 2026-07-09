# Ring-generalization refactor plan

Executes the generalization scoped in `docs/ring-generalization-scan.md`: make `CPoly`'s coefficient a
computable **commutative ring**, with `CField` a specialization, so `BPoly`/`GBPoly` (polys-over-polys)
collapse into `CPoly (CPoly _)`. Dependency-ordered, each phase its own gate-green commit. This is a
foundational multi-session arc (scale of the fuel retirement / `CFrac` move).

## Inventory (from the scan)

- **Class hierarchy** — everything hangs off `[CField α]`: `CFieldSpec` (bridge `toK : α → K`, `K` a
  `Field`), `CFieldDomain`, `CDiffField`/`CDiffFieldSpec`, `CRischField`/`CRischFieldSpec`,
  `CFracGcdCoreWf`. `CFieldSpec.K` appears **1030×** (the denotation target).
- **~95 % ring-level:** 20/21 core `c*` ops use only `add`/`mul`/`neg`/`isZero`; only `cmonic` needs
  `CField.div`. Field-only ops (stay `[CField]`): `cmonic`, `cdiv`/`cmod`/`cdivmod`, `cgcd*`, `cinv`,
  `cinterpolate`, Euclidean-`cresultant`. ~46 files touch `CField.inv`/`div`.
- **Collapsible layers:** `BPoly = List CPolyQ` (`= CPoly CPolyQ` defeq; `Compute/Subresultant` 204 L +
  `SubresultantCorrectness/` 1278 L / 7 files); `GBPolyCore`/`GBPoly` = identical `List (CPoly B)`
  duplicate (11 files). `RadElem = List α` is a different concept — untouched.
- **Constraint surface:** 475 `[CField α]` + 279 `[CFieldSpec α]` = 754 binders.

## Target design

```
CCommRing α                         -- Prop-free ring ops: zero/one/add/mul/neg/isZero  (native_decide-safe)
CRingSpec  α [CCommRing α]          -- bridge toR : α → R, R a CommRing; hom laws (no inv law)
CField     α extends CCommRing α    -- adds inv
CFieldSpec α extends CRingSpec α    -- adds [Field R] + toK_inv;  K := R  (keeps CFieldSpec.K working)
```

- **Keystone instance** `CCommRing (CPoly α)` (a poly over a ring is itself a ring coefficient:
  `add := cadd`, `mul := cmul`, `neg := cneg`, `zero := []`, `one := [1]`, `isZero := cisZero`) +
  `CRingSpec (CPoly α)` with `R := (CRingSpec.R α)[X]`, `toR := toPoly`. This is what makes
  `CPoly (CPoly _)` typecheck and reduce.
- **Denotation:** `toPoly : CPoly α → (CRingSpec.R α)[X]` over `[CRingSpec α]`. For a field, `R = K`, so
  every existing `(CFieldSpec.K α)[X]` stays defeq — no statement changes on the field path.

## Pins (what keeps the old code alive during migration)

- After P1, **`[CField]`/`[CFieldSpec]` still resolves everything** (a `CField` *is* a `CCommRing`; a
  `CFieldSpec` *is* a `CRingSpec`), so no call site breaks until an op is deliberately weakened in P3.
- **`CFieldSpec.K` is retained** as `CFieldSpec.K α := CRingSpec.R α` (abbrev), so the 1030 uses compile
  untouched. Only ring-level *denotation squares* migrate to `CRingSpec.R` in P3.
- **`native_decide` guard:** `CCommRing` is Prop-free (like `CField`), and the keystone
  `CCommRing (CPoly α)` instance is built from the reducing `c*` ops — so the engine keeps reducing. Every
  phase re-runs the native_decide showcase.

## Phase order (delete/weaken consumers only after their base is generalized)

**P1 — DONE (commit below).** introduce the ring base, zero call-site churn. Add `CCommRing`, `CRingSpec`; make
`CField extends CCommRing`, `CFieldSpec extends CRingSpec` (`R := K`, `K` kept as alias). Provide the
`CField ⇒ CCommRing` / `CFieldSpec ⇒ CRingSpec` paths so all existing instances still resolve.
*Verify (spike):* the whole build is unchanged and green; `#check (inferInstance : CCommRing ℚ)` works via
the `CField ℚ` instance. Risk: **instance diamond** if any type gets both a direct `CCommRing` and a
`CField`-derived one — none should yet. Gate: full build + native_decide showcase unchanged.

**P2 — the `CCommRing (CPoly α)` keystone: DONE + native_decide-validated (commit below).** The
*computational* keystone is in: `CCommRing (CPoly (CPoly ℚ))` resolves and bivariate `cmul` reduces under
`native_decide`; `List (CPoly ℚ) = CPoly (CPoly ℚ)` by `rfl`. Weakened cadd/cmul/cneg/cisZero/cnorm/… to
`[CCommRing]` with 5 `@[denote]` bridge lemmas. **Still remaining in this phase:** the *denotational*
`CRingSpec (CPoly α)` keystone (`R := (R α)[X]`, `toR := toPoly` as a ring hom) — needed before P4's
correctness collapse. The original P2 text: Define them from `c*` ops; prove the
`CRingSpec` hom laws (`toPoly` is a ring hom — reuse the existing `@[denote]` squares). *Verify (spike):*
`#check (inferInstance : CCommRing (CPoly ℚ))` and a `native_decide` on `cmul (X:CPoly (CPoly ℚ)) …`
reduces. Risk: the `CRingSpec (CPoly α)` `R = (R α)[X]` bridge must be a genuine ring hom — this is where
the real proof work is (bounded: it is the `toPoly` homomorphism already proven, re-typed over `CommRing`).
Gate: `CPoly (CPoly ℚ)` typechecks + reduces.

**P3 — DONE (commits `6e1d7f75` P3a + `548f7c03` P3 substance).** Two sub-steps landed:
- **P3a** retargeted the denotation `toPoly : CPoly α → (CRingSpec.R α)[X]` over `[CCommRing]/[CRingSpec]`
  and fixed the bounded R/K instance-boundary cascade (a `Field (CRingSpec.R α)` + `Differential
  (CRingSpec.R α)` instance; `erw`/`rfl`/`CRingSpec.toR` closes the `am(K)=algebraMap(R)` defeq goals).
- **P3 substance** weakened the `toPoly` homomorphism squares (nil/cons/one/caddG/cnegG/csubG/cscaleG/
  cshiftG/cmulG/cpowG and the `cnorm`/`cdeg`/`clead`/`cisZero`↔`toPoly=0` chain) to `[CCommRing]/[CRingSpec]`,
  and added the **denotational keystone** `instance CRingSpec (CPoly α)` (`R := (CRingSpec.R α)[X]`,
  `toR := toPoly`). Validated: `CRingSpec (CPoly (CPoly ℚ))` resolves, bivariate `cmul` reduces under
  `native_decide`, `R (CPoly ℚ) = (R ℚ)[X]` by `rfl`.

The predicted R/K cascade was REAL but **bounded** (contradicting the earlier "do the CFieldSpec-extends-
CRingSpec redesign first" fear): the fix was `@[simp]` normalizers `toR_eq_toK` + `ccrZero/One/Add/Mul/Neg`
that collapse `toR→toK`/`CCommRing→CField` on the field path automatically, plus `simp only [toR_eq_toK]`
inserts at ~15 explicit-`rw` field-path sites across 10 files, plus `toK_cleadG_*`/`toK_cnormG_getD` field
aliases of the now-`toR` chain lemmas. The full redesign was NOT needed. `cmonic` + field ops stay `[CField]`.

**P4 — collapse `BPoly`.** Replace `BPoly` with `CPoly CPolyQ` (defeq), and each `b*` op with `c* @ CPolyQ`
(`badd`→`cadd`, `bmul`→`cmul`, …); the pseudo-division subresultant (`bpsremainder`/`bsubresultantGcd`) →
the generic ring-level subresultant instantiated at `CPolyQ`. Migrate the `SubresultantCorrectness/`
cluster's bivariate lemmas to the generic ones. Delete the `b*` layer in `Compute/Subresultant`. *Verify:*
the Rothstein–Trager log-part native_decide examples still pass. Risk: `SubresultantCorrectness` proofs may
lean on `b*`-specific rewrite lemmas — port or re-derive from the generic satellites; do this last (it is
the largest single chunk, ~1500 L).

**P5 — unify `GBPoly`/`GBPolyCore`.** Both become `CPoly (CPoly B)`; delete the duplicate abbrev and
re-point the 11 consumers. The fraction-free gcd (`cgcdFF*`) already works over a ring coefficient, so this
is a type-alias unification. Gate.

## Rollback & sequencing

- Each phase is an independent gate-green commit; a failing phase reverts without touching earlier ones.
- P1→P2 are additive (no deletions) and safe to land early. P3 is the wide mechanical sweep. P4/P5 are the
  payoff (deletions) and must come last (they consume the generalized ops from P3).
- Do **not** start before the current naming/reorg work is settled — P3 touches 754 binders across the
  whole engine and will conflict with any concurrent rename.

## Net

Touch surface ~754 constraints (mechanical) + a real `CRingSpec (CPoly α)` hom proof (P2) and the
`SubresultantCorrectness` port (P4). Cleanup ~1500 lines + a duplicate; four polynomial representations
(`CPoly`/`BPoly`/`GBPoly`/`GBPolyCore`) → one ring-generic `CPoly`. See `docs/ring-generalization-scan.md`.
