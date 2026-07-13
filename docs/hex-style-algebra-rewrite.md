# Hex-style greenfield rewrite of the computable-algebra + symbolic-integration engine

**Status:** ACTIVE (started 2026-07-13). Multi-session program. Each phase is its own
gate-green commit. This doc holds the mechanical phase list; durable adjudications/lessons go to
memory.

## Goal

Rebuild the DeepWiki computable-algebra substrate and the symbolic-integration engine on top of it
in the style of the `leanprover/hex` library
(`github.com/leanprover/hex`, `github.com/kim-em/hex-dev`), replacing the current denotation-homomorphism
architecture with Hex's **canonical-representation + ring-isomorphism** architecture.

The rewrite is **greenfield and parallel**: the new tree is built alongside the existing
`DeepWiki/ComputableAlgebra/` + `DeepWiki/SymbolicIntegration/{Compute,Engine,RationalIntegrationAlgorithms}`,
both kept gate-green in `defaultTargets`, and the old tree is retired only once the new one reaches
parity (end-to-end `cIntegrate` examples reproduced + catalog reachability preserved).

## Why (the load-bearing Hex properties)

Hex's advantages, ranked by how much they buy *us*:

1. **Canonical (normalized) representation → `RingEquiv`, not a one-way homomorphism.** Hex's
   `DensePoly` bundles the no-trailing-zeros invariant into the type, so structural equality =
   semantic equality and the bridge to `Polynomial` is a genuine `≃+*` bijection. Completeness
   (reflection) then falls out of transporting in the *reverse* direction, instead of proving each
   reflection lemma by hand (`isZero_iff` + per-op reverse lemmas) as the current `toK`/`toPoly`
   homomorphism approach must. **This is the primary reason for the rewrite.**
2. **Intrinsic `Laws` Prop-classes, discharged per carrier.** `DivModLaws`/`GcdLaws` state the
   executable algorithm's universal property *inside* the computable world (Mathlib-free), proven
   once and instantiated per coefficient type. The Mathlib bridge then transports the universal
   property; it never re-derives algorithm correctness. Mirrors our `X`/`LawfulX` idiom, applied
   uniformly.
3. **Optional `decide +kernel` certificate path (small TCB).** Fuel-indexed twins of the
   Euclidean/Bareiss loops kernel-reduce, so concrete certificates can be checked by the kernel
   (dropping `native_decide`'s compiler-in-TCB) where a small trusted base is worth it. `native_decide`
   stays available for heavy end-to-end validation.

**Explicitly NOT load-bearing for us:** Hex's strict *Mathlib-free cores*. Hex keeps cores
Mathlib-free so the packages are reusable standalone; DeepWiki is a Mathlib-based wiki and *wants*
Mathlib available. We adopt the **core / `*Bridge` companion split** for organization and to keep the
`RingEquiv` layer isolated, but a new "core" module may still `import Mathlib` where convenient. Going
fully Mathlib-free is a later, optional packaging decision (only if we ever spin the substrate out).

## Honest scope / risk

- Current sizes: `ComputableAlgebra` ~10.8k L, `Compute` ~0.8k L, `Engine` ~49.3k L, rational
  algorithms ~2.8k L. The **substrate is ~15%**; the **engine math is ~67%** and is
  *representation-independent* (Liouville, tower exhaustiveness, RT/LRT, the algebraic decision
  procedure do not get shorter under a normalized `Array` poly).
- The already-proven, axiom-clean, **sound+complete transcendental Risch** arc and the fully-realized
  **algebraic** layer must be *transported*, not rediscovered. The risk is regressing verified results
  during the port. Mitigation: parallel build + parity gates + port algorithm-by-algorithm as
  commuting squares over the new carriers, never deleting an old proof before its new twin is green.
- This is a **multi-month** program. Prior lesson ([[leanproofs-representation-independent-poly]]):
  existing-engine migration is connected-component-scale.

## Target architecture

New tree under `DeepWiki/CAlgebra/` (namespace `DeepWiki.CAlgebra`), organized core + bridge:

```
DeepWiki/CAlgebra/
  Poly/Dense.lean            -- normalized `DensePoly R` structure (Array + invariant) + coeff API
  Poly/Operations.lean       -- add/mul/neg/C/monomial/eval/degree, structural
  Poly/Euclid.lean           -- divMod/gcd/xgcd (Wf) + DivModLaws/GcdLaws classes
  Poly/EuclidFuel.lean       -- fuel-indexed kernel-reducible twins (decide +kernel path)
  Poly/Resultant.lean        -- resultant / subresultant PRS / Bareiss
  PolyBridge/Basic.lean      -- toPolynomial/ofPolynomial + coeff lemmas + `equiv : DensePoly R ≃+* Polynomial R`
  PolyBridge/Euclid.lean     -- gcd/xgcd `Associated` correspondence, dvd_iff
  PolyBridge/Resultant.lean  -- resultant/det correspondence
  Frac/Dense.lean            -- canonical `DenseFrac` (normalized num/denom) fraction field
  FracBridge/Basic.lean      -- `equiv : DenseFrac K ≃+* RatFunc K` (or the tower field)
  Field/Carrier.lean         -- computable-field carrier + per-carrier Laws instances (ℚ, tower)
  Diff/Derivation.lean       -- computable derivation + bridge to Mathlib `Derivation`/`′`
  Tower/*.lean               -- iterated construction for ℚ(x)(t₁)(t₂)…
Engine2/*                    -- Risch engine re-anchored onto CAlgebra (ported incrementally)
```

Naming/conventions carry over from CLAUDE.md: concept-named modules (no book numbers), one-line
docstrings, `Laws`-class = `Lawful` idiom, `_apply`/`_coe` reading lemmas, satellites in the defining
file. `@[simp, grind =]` on the bridge squares (Hex's convention; our `@[denote]` set is subsumed by
these + `grind`).

## Phase order (dependency-ordered, bottom-up)

Each phase ends gate-green (`scripts/check.sh`) and is one commit.

- **Phase 0 — scaffold.** Create `DeepWiki/CAlgebra/` area + aggregator, wire into `DeepWiki.lean`,
  add this plan. Decide namespace (`DeepWiki.CAlgebra`) and the parallel-build strategy. *(this commit)*
- **Phase 1 — normalized `DensePoly` + `RingEquiv`. DONE.** `Poly/Dense.lean` (structure + invariant +
  `coeff`/`degree`/`normalize` + `ext_coeff`) ✓ 1a; `Poly/Operations.lean` (one/monomial/add/neg/mul +
  coeff laws) ✓ 1b; `PolyBridge/Basic.lean` (`coeff_toPolynomial`/`coeff_ofPolynomial`, round trips,
  hom squares, `equiv : DensePoly R ≃+* Polynomial R`) ✓ 1c. Keystone landed: the canonical-rep →
  ring-iso thesis holds; note `RingEquiv` needs only `Mul`+`Add` on `DensePoly`, so no `CommRing`
  instance was required to state it. **← NEXT: Phase 2.**
- **Phase 2 — Euclid + Laws + gcd bridge.** `divMod`/`gcd`/`xgcd`, `DivModLaws`/`GcdLaws`, `ℚ`
  instances, `PolyBridge/Euclid.lean` (`gcd_associated`, Bezout transport).
  Optional: `EuclidFuel.lean` + one `decide +kernel` certificate.
  - **2a DONE:** `PolyBridge/Ring.lean` — `CommRing (DensePoly R)` via injective `toPolynomial`
    (computable `+`/`-`/`*`; auxiliary `•`/`^`/casts through the bridge) + `toPolynomial_dvd_iff`
    (divisibility preserved AND reflected — first completeness-by-reverse-transport payoff). **← NEXT:
    2b divMod/gcd/xgcd (Wf) + `GcdLaws` + gcd `Associated` bridge.**
- **Phase 3 — resultant / subresultant / Bareiss** + Mathlib correspondence.
- **Phase 4 — canonical `DenseFrac` fraction field + `≃+* RatFunc`**, and the tower iteration
  (replacing `CFracG`/`QFunNZG` towers with normalized-fraction carriers bridged by field iso).
- **Phase 5 — computable derivation + bridge** to Mathlib `′`/`Derivation` on the new carriers.
- **Phase 6…N — re-anchor the engine.** Port Hermite → Rothstein–Trager → residues/log part →
  LRT → RDE / coefficient recursion → tower orchestration → algebraic layer, each restated as a
  transported commuting square over `CAlgebra` carriers. Reproduce the end-to-end `cIntegrate`
  examples. This is the bulk.
- **Phase Z — retire the old tree.** Once parity + catalog reachability confirmed, delete
  `ComputableAlgebra` + old `Engine`, repoint `Sources/` catalogs, update CLAUDE.md.

## Parity / acceptance gates

- Every phase: `scripts/check.sh` PASS (warning-/sorry-free), axiom-clean where the old twin was.
- Substrate parity: for each ported algorithm, an `example` restating the old theorem on the new
  carrier compiles; gcd/resultant/Bareiss reproduce the old `native_decide` checks (or `decide +kernel`).
- Engine parity: the marquee `cIntegrate` / tower / algebraic worked examples reproduce identical
  results on the new substrate before the old one is deleted.
- Catalog: `Sources/` aliases repoint to new declarations in the retirement phase; no orphaned or
  silently-skipped catalog modules (`Sources.lean` import audit).

## Open design questions (resolve as phases land)

- `Array`-backed (Hex) vs `List`-backed normalized `DensePoly`? Hex uses `Array` for perf; kernel
  reduction over `Array` vs `List` differs. Decide in Phase 1 (lean `List` for proof ergonomics unless
  a bench says otherwise).
- Does the tower fraction field want a single `DenseFrac` iterated, or distinct level carriers? Phase 4.
- How much of the algebraic layer's Gröbner/divisor machinery gets a canonical rep vs stays as-is. Phase 6+.
