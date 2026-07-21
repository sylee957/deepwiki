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

**`native_decide` examples are dev-time scaffolding, deleted once compiled.** To validate that a
computable layer genuinely runs, write `native_decide` `example`s and confirm they pass — then
**delete them before (or immediately after) the phase commit**. The new tree stays `native_decide`-free
(small TCB, Hex-aligned); the permanent verified content is the abstract theorems (`*_spec`, universal
properties, `Associated` bridges). Kernel-reducible `decide` certificates (via fuel twins) may be kept
when a phase adds them; only compiler-trusting `native_decide` is transient. Record "computability
checked, examples removed" in the phase commit message.

**ARCHITECTURAL RULE (superseded 2026-07-13, user): COHESIVE concept modules — no `*Bridge/`
separation.** We are NOT pursuing Mathlib-free cores (a standalone-package goal we don't want), so
splitting each concept into a core file + a `*Bridge` file only fragments it without payoff. Instead
each concept module holds its computable defs *and* their Mathlib correspondence together. The earlier
core/`*Bridge` split was reverted: `PolyBridge/`, `FracBridge/`, `MatrixBridge/` folders **deleted**,
their content folded into the concept modules — `Poly/Operations` (arithmetic + `toPolynomial`/`equiv`
+ computable `CommRing` + dvd), `Poly/Euclid` (division/gcd + `Associated`), `Poly/Derivative` (deriv +
bridge + laws), `Frac/Basic` (carrier + ops + `toRatFunc`), `Matrix/{Dense,Sylvester}` (carrier +
`toMatrix`/resultant). Genuinely-noncomputable denotations (`toPolynomial`/`ofPolynomial`/`equiv`,
`toRatFunc`) are marked `noncomputable def` individually; the computable ops and `CommRing` stay
computable (guarded in `Test/Computable`).

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
    (divisibility preserved AND reflected — first completeness-by-reverse-transport payoff).
  - **2b-i DONE:** `Poly/Euclid.lean` — `divMod` (Wf on remainder size; termination = leading-term
    cancellation `divStep_size_lt`) + `divMod_spec` (`div·q + mod = p`).
  - **2b-ii DONE:** `gcd` (Wf on divisor size, `mod_size_lt`) + universal property
    `gcd_dvd_left`/`gcd_dvd_right`/`dvd_gcd` (the intrinsic `GcdLaws` content).
  - **2b-iii DONE:** `PolyBridge/Euclid.lean` — `toPolynomial_gcd_associated`: executable gcd is
    `Associated` to `EuclideanDomain.gcd` (up to a unit, since the raw remainder isn't normalized),
    proved purely by transporting the universal property across `toPolynomial_dvd_iff`. **← NEXT:
    2c optional `xgcd`/Bezout + `ℚ`-carrier `GcdLaws`/`DivModLaws` instances; then Phase 3 resultant.**
  - **2d DONE (2026-07-20):** `Poly/PseudoDivision.lean` — pseudo-division over any `CommRing`
    coefficient (structural recursion on the exact step count): `pseudoDivMod`/`pseudoDiv`/`pseudoMod`
    with the exact-power identity `C (lc q ^ (size p + 1 − size q)) * p = quo * q + rem`
    (`pseudoDivMod_spec`, proved by transport) + `pseudoMod_size_lt`, and the transported Mathlib-facing
    square `toPolynomial_pseudoDivMod` (Mathlib has NO pseudo-division — the transported identity IS
    the bridge). Shared helpers generalized out of Euclid's `Field` section (`leadingCoeff`,
    `size_le_of_coeff_zero` → `Poly/Dense`; `coeff_monomial_mul` + new `coeff_C_mul`/`size_C_mul_le` →
    `Poly/Operations`). Computability guarded; validated over `ℤ` and `DensePoly (DensePoly ℤ)`
    (dev `#eval`s, removed). Prerequisite for subresultant PRS / tower-coefficient division (3b'/6).
  - **2e DONE (2026-07-20):** `Poly/GcdSubresultant.lean` — subresultant-PRS gcd `gcdSubresultant`
    ALONGSIDE the Euclidean `gcd` (user directive: keep both, connect by proof): each pseudo-remainder
    divided by `β = (−1)^(δ+1)·g·h^δ` (a unit constant over a field), universal property proved via
    unit-cancellation (`dvd_of_dvd_C_mul`), and the **agreement theorem**
    `gcdSubresultant_associated_gcd : Associated (gcdSubresultant p q) (gcd p q)` (both satisfy the
    same universal property). Mathlib bridge `toPolynomial_gcdSubresultant_associated` DERIVED by
    mapping the agreement through the iso and composing with the Euclidean bridge. Satellites:
    `C_mul` (Operations), `pseudoMod_eq_sub` (PseudoDivision), `eq_zero_of_size_zero` generalized to
    `Poly/Dense`. Fraction-free variant over non-field domains (exact-division interface) deferred.
  - **2f DONE (2026-07-20):** computable `EuclideanDomain (DensePoly R)` instance (`Poly/Euclid`) —
    quotient/remainder = the executable `div`/`mod`, measure = `size`; laws from `divMod_spec` +
    `mod_size_lt` + new `size_mul` (via `natDegree` transport; `size_eq_natDegree_add_one`).
    Mathlib's GENERIC `EuclideanDomain.gcd`/`xgcd`/Bézout now run computably on the dense carrier
    (guarded; xgcd Bézout identity checked in dev `#eval`, removed) and
    `euclideanDomain_gcd_associated_gcd` connects the generic gcd to ours by universal property.
    `toPolynomial_ne_zero` moved Frac/Basic → Operations. Next candidate: `GCDMonoid` instance
    (needs dvd → `mod = 0` exact-division lemma).
  - **2h DONE (2026-07-21, user): gcd dispatch class `DensePolyGcd`.** `Poly/Gcd.lean` is now the
    INTERFACE: class `DensePolyGcd R` (fields = the gcd universal property) with priority-ordered
    instances — generic default (100) = subresultant PRS, `ℚ` override (200) = Euclidean (measured
    faster there; dispatch verified: `ℚ` → Euclid output, `𝔽₁₀₀₉` → subresultant output). The
    Euclidean algorithm renamed `gcdEuclid` into `Poly/GcdEuclid.lean` (symmetric with
    `GcdSubresultant`); `DensePoly.gcd` no longer exists. Class-level theorems (independent of the
    instance): `gcd_ne_zero_of_right`, `associated_euclideanDomain_gcd`, `gcd_associated_gcdEuclid`
    (all instances pairwise associated), `toPolynomial_gcd_associated` (Mathlib bridge).
    `DenseFrac.normalize` + the fraction ops/instances now take `[DensePolyGcd R]` and dispatch per
    carrier; `Refine/Gcd` witnesses target the class interface. Retuning instances is invisible to
    every proof — algorithm choice is pure performance policy. ★ Lint lesson: a section-variable
    `[DensePolyGcd R]` auto-includes into theorems that don't use it → `omit [DensePolyGcd R] in`
    per theorem.
  - **4g DONE (2026-07-21, user): bundled monic sub-carrier `DensePolyMonic`** (`Poly/Monic.lean`):
    `toPoly` + `monic` with `One`/`Mul` closure (new satellites `leadingCoeff_toPolynomial`,
    `leadingCoeff_mul` in `Poly/Euclid`), `ne_zero`, and the rigidity lemma `eq_of_associated`
    (associated monic polynomials are equal — monicity pins the unit). `DenseFrac.den` is now a
    `DensePolyMonic`, deleting the `monic_den` field, `den_ne_zero`, and the inlined unit-pinning
    block in `toRatFunc_injective` (now one `eq_of_associated` call).
  - **2j DONE (2026-07-21, user): monic division** (`Poly/DivisionMonic.lean`): `divModMonic p q`
    for `q : DensePolyMonic` — the quotient term is `leadingCoeff r` directly (no coefficient
    division), so it runs over any nontrivial `CommRing` (the fraction-free/domain track's
    division) and saves a field division per step on expensive carriers (measured ~5% at `ℚ(x)`;
    grows with coefficient-normalization cost). Connected to the general division by
    **uniqueness of Euclidean division**: `divModMonic_eq_divMod` — literal equality of the pair
    over a field (differing quotients would force `size ≥ size q` on one side of the remainder
    identity, `< size q` on the other). ★ Lean lessons: a section variable used only in
    `decreasing_by` is NOT auto-included (bind `[Nontrivial R]` explicitly on the def); `omega`
    treats defeq-but-not-syntactic atoms (`(divMod …).2.size` vs `(mod …).size`) as unrelated —
    ascribe hypotheses to the goal's spelling.
  - **SHELVED (2026-07-21, user — "too many proofs for now"): monic-remainder Euclidean gcd.**
    Prototyped and benchmarked, then reverted: re-monicizing each remainder makes every division
    step the division-free `modMonic` and the result canonically monic. Measured: parity at `ℚ`
    (15.5 vs 14.8 ms — division ≈ multiplication there), but **1.7× faster at the `ℚ(x)[t]` tower**
    (261 vs 441 ms Euclid vs 703 ms subresultant) — the per-remainder scaling acts as coefficient
    cleanup on fraction carriers (primitive-PRS-style content taming). When tower gcd performance
    matters, reinstate as a `DensePolyGcd` override for `DenseFrac`-coefficient carriers: def
    `gcdMonic p q := modMonic-loop with monicized remainders` + universal property by the standard
    induction + `monicize` satellites (`toPoly_monicize`/`size_monicize`/`monicize_associated`).
  - **2k DONE (2026-07-21, user): `gcdEuclid` DELETED — Mathlib's generic `EuclideanDomain.gcd`
    is the Euclidean algorithm.** `Gcd/Euclid.lean` removed wholesale: the hand-rolled Euclidean
    gcd duplicated Mathlib's generic algorithm running through our computable `EuclideanDomain`
    instance. The `ℚ` override of `DensePolyGcd` now delegates to `EuclideanDomain.gcd` with ZERO
    proof obligations (algorithm + universal-property laws all Mathlib's); the subresultant's
    agreement retargets to it (`gcdSubresultant_associated_euclideanDomainGcd`) and its Mathlib
    bridge is proved directly. Canonical fraction outputs verified invariant (monic scaling
    cancels the gcd's unit ambiguity). Own the instance, inherit the algorithm.
  - **2i DONE (2026-07-21, user): gcd area directory.** The gcd family moves to its own area per
    the subdirectory grammar: `CAlgebra/Gcd.lean` (the `DensePolyGcd` class = area root/aggregator)
    over `CAlgebra/Gcd/{Euclid,Subresultant}.lean` (leaves drop the implied `Gcd` prefix). The
    ED-agreement theorem `euclideanDomain_gcd_associated_gcdEuclid` migrated `Poly/Euclid` →
    `Gcd/Euclid` so `Poly/` is gcd-free (pure carrier/division/instance layer). Import-only reorg,
    zero declaration changes.
  - **2g DONE (2026-07-20): division/gcd file reorg** (zero declaration changes, user layout):
    `Poly/Division.lean` (long division), `Poly/DivisionPseudo.lean` (renamed from
    `PseudoDivision.lean`), `Poly/Gcd.lean` (Euclidean gcd + universal property + Mathlib bridge),
    `Poly/GcdSubresultant.lean`, `Poly/Euclid.lean` (now solely the `EuclideanDomain` instance +
    size lemmas + generic-gcd agreement). Base-concept-first naming so families sort together.
- **Phase 3 — resultant / subresultant / Bareiss** + Mathlib correspondence. **← NEXT.**
  Approach (scouted): bridge target is Mathlib `Polynomial.resultant` (exists, over `CommRing`). Hex
  has no standalone resultant module — it computes via the **Sylvester-matrix determinant**
  (`HexDeterminant` + `HexBareiss` fraction-free). So this phase needs a small computable-matrix layer
  first. Sub-phases: 3a computable `Matrix`/`Vector` carrier + `toMathlib` bridge; 3b Bareiss
  fraction-free determinant + `det` correspondence; 3c Sylvester matrix + `resultant` = its determinant,
  bridged to `Polynomial.resultant`. (Alternatively a subresultant-PRS resultant reusing `divMod`, but
  the Mathlib-equality proof is harder than the determinant route.)
  - **3a DONE:** `Matrix/Dense.lean` — `DenseMatrix R` (list-of-rows carrier) + `entry`/`ofFn` +
    `toMatrix : → Matrix (Fin n) (Fin m) R` with entrywise agreement.
  - **PIVOT (correctness-first):** Mathlib *defines* `Polynomial.resultant f g := (f.sylvester g).det`,
    so the resultant bridges through the Sylvester matrix with **no Bareiss correctness needed**.
    Bareiss becomes an optional efficiency-only sub-phase (3b'), NOT on the correctness path.
  - **3b DONE:** `Matrix/Sylvester.lean` — computable `sylvester p q m n` + `toMatrix_sylvester`
    (bridges to `Polynomial.sylvester`; proved by `Fin.addCases` column-split matching).
  - **3c DONE:** `Matrix/Resultant.lean` — `resultant := sylvester.det` + `toPolynomial_resultant`
    (bridges to `Polynomial.resultant`, near-definitional). **← NEXT: Phase 4 (canonical `DenseFrac`
    fraction field + `≃+* RatFunc` + tower iteration).** Optional later: 3b' Bareiss for efficient det.
- **Phase 4 — canonical `DenseFrac` fraction field + `≃+* RatFunc`**, and the tower iteration
  (replacing `CFracG`/`QFunNZG` towers with normalized-fraction carriers bridged by field iso). **← NEXT.**
  - **4a DONE:** `Frac/Dense.lean` — `DenseFrac R` (num/den pair carrier) + noncomputable
    `toRatFunc : → RatFunc R` (`num/den` via `toPolynomial` + fraction-field `algebraMap`) +
    `ofPoly` embedding with its bridge lemma. Note: unlike `DensePoly`, the raw `DenseFrac` map is a
    homomorphism not an iso (num/den not reduced); a gcd-reduced canonical form (for the iso) is an
    optional refinement — the hom suffices for the engine's needs.
  - **4b-i DONE:** `Frac/Arithmetic.lean` — `mul`/`one` + `toRatFunc_mul`/`toRatFunc_one` (hold
    UNCONDITIONALLY).
  - **4b-ii DONE:** `Frac/Additive.lean` — `neg`/`inv` (unconditional hom via `neg_div`/`inv_div`) +
    `add` with `toRatFunc_add` carrying `den ≠ 0` hypotheses (via `RatFunc.algebraMap_ne_zero` +
    `toPolynomial_ne_zero` + `div_add_div`). **← NEXT: 4c tower iteration** — build the depth-`n`
    carrier `ℚ(x)(t₁)…(tₙ)` by iterating `DenseFrac`/`DensePoly` over the previous level, bridging
    each level to the corresponding `RatFunc` tower. Then Phase 5 (derivations).
  - **4d DONE (2026-07-20):** `Frac/Canonical.lean` — canonical fraction form via the gcd stack:
    `DenseFrac.reduce` (divide out `gcd`, monic-normalize the denominator, zero denominators
    collapse to `0/1`) with `toRatFunc_reduce` (denotation preserved),
    `reduce_den_leadingCoeff`/`reduce_den_ne_zero` (monic), `isCoprime_reduce` (coprime, via
    unit-gcd cancellation + Bézout through the `EuclideanDomain` instance). Exact division is
    Mathlib's `EuclideanDomain.mul_div_cancel'` through our instance — no new division lemmas.
    ★ Lean lesson: `set`-abstract `g`/`n'`/`d'` before rewriting — raw `rw [← hnum]` also rewrites
    the `f.num` inside `gcd f.num f.den` (garbage), and dvd-goals over nested WF `gcd` terms send
    `whnf` into timeout.
  - **4e DONE (2026-07-21): the canonical fraction FIELD + `≃+* RatFunc`.** Uniqueness keystone
    (`eq_of_toRatFunc_eq`: coprime + monic representatives are unique — Euclid's lemma on the
    `IsCoprime` certificates + `exists_C_of_isUnit` unit characterization via `size_mul`) and
    `reduce_eq_reduce_iff` (canonical forms decide semantic equality) in `Frac/Canonical.lean`;
    `Frac/CanonicalField.lean` — carrier `CanonicalFrac R` (subtype of `IsCanonical`, ops
    renormalize through `reduce`), computable hand-built `CommRing` + `Field` instances (laws by
    transport through the injective denotation; `nnqsmul := _`/`qsmul := _` idiom), decidable
    SEMANTIC equality (`toRatFunc_eq_iff` + structural `DecidableEq`), and
    `equivRatFunc : CanonicalFrac R ≃+* RatFunc R` (surjectivity via `reduce ∘ (num, denom)` —
    no Mathlib num/denom normalization lemmas needed). This is the lawful computable field carrier
    the fraction-level tower (4c-ii) requires. Guards: `canonicalAdd`/`canonicalInv`/`canonicalEq`.
    ★ REVISED (2026-07-21, user): raw `DenseFrac` is NOT an engine-facing carrier — unreduced
    arithmetic grows exponentially under iteration (measured: 8 iterations of `f := f + f` from
    `1/(x+1)` give a degree-256 raw denominator vs the canonical `256/(x+1)`), matching why CAS
    fraction arithmetic normalizes eagerly.
  - **4f DONE (2026-07-21, user): raw/canonical MERGED — canonicality encoded directly on
    `DenseFrac`.** The raw pair type and `CanonicalFrac` subtype are gone; `DenseFrac R` (now
    `[Field R]`) bundles `monic_den` + `coprime` as structure fields (the `DensePoly`/`Normalized`
    pattern one level up), with smart constructor `normalize (n d : DensePoly R)` (private
    `normNum`/`normDen` components; zero denominators ↦ `0/1`). `Frac/Basic.lean` = type +
    `normalize` + denotation + uniqueness (`toRatFunc_injective`) + renormalizing ops +
    unconditional hom squares (`neg` is componentwise — no renormalization); `Frac/Field.lean` =
    computable `CommRing`/`Field` instances + `equivRatFunc : DenseFrac R ≃+* RatFunc R`.
    `Frac/Canonical.lean`/`Frac/CanonicalField.lean` deleted; `reduce`/`Eqv`/`IsCanonical` folded
    in (`Eqv`'s bridge survives as `div_eq_div_iff_cross` on components). The old engine's
    `SymbolicIntegration.DenseFrac` is an unrelated namespace — untouched.
  - **4c-i DONE, module since removed (2026-07-20, user):** `Poly/Tower.lean` validated the depth-2
    tower — `DensePoly (DensePoly R)` a `CommRing` by iterating the instance, and the generic
    `equivTower2 : DensePoly (DensePoly R) ≃+* Polynomial (Polynomial R)` composing the level-2 iso
    with `Polynomial.mapEquiv` of the level-1 iso. Validation served its purpose; the file was
    deleted (no consumers). 4c-ii's generic depth-`n` carrier re-establishes the iso when built.
    - ★ FINDING (2026-07-13, now FIXED): the `CommRing (DensePoly R)` instance WAS noncomputable
      because it used `Function.Injective.commRing` (itself noncomputable — no compiled stage) with
      bridge-routed aux ops. **FIX (user directive "don't bundle Mathlib uncomputable ones"):**
      hand-built the `CommRing` — arithmetic fields = the computable `Operations`, axioms proved by
      transport through `toPolynomial`, and `nsmul`/`zsmul` = `nsmulRec`/`zsmulRec` with `npow`/
      `natCast`/`intCast` at Lean's computable defaults. Now the ENTIRE `CommRing` is computable:
      `^`/`•`/casts `#eval` correctly (guarded in `Test/Computable`). Nothing noncomputable is bundled
      onto the compute type — matches Hex's discipline while keeping the `ring`-tactic convenience.
    - ★ COMPUTABILITY IS BUILD-VERIFIED (`Test/Computable.lean`): Lean's compiler is a computability
      decision procedure — a plain `def` computing an op proves it's on the computable path (else the
      `dependsOnNoncomputable` error breaks the gate). Confirmed: `*`/`+`/`-`/`divMod`/`gcd`/`deriv` +
      `DenseFrac` ops ARE computable; `^`/`•`/`natCast` on `DensePoly` are NOT (compiler-rejected).
      Guards are `def`s, not `native_decide`, so they add nothing to any theorem's TCB. Full
      verified-computable-path = these guards (path exists) + the `toX_*` bridge squares (path denotes
      the right Mathlib op).
    - **← NEXT: 4c-ii generic depth-`n` tower carrier** (recursive type + instances — the known
      instance-recursion plumbing, [[leanproofs-tower-orchestration-rework]]) OR the fraction-field
      tower needing `Field (DenseFrac)` via canonical reduced form. Then Phase 5 (derivations).
- **Phase 5 — computable derivation + bridge** to Mathlib `′`/`Derivation` on the new carriers.
  **← NEXT.**
  - **5a DONE:** `Poly/Derivative.lean` — `deriv` (formal derivative, `coeff k = (k+1)·coeff (k+1)`) +
    `coeff_deriv` + `toPolynomial_deriv` (bridges to `Polynomial.derivative`).
  - **5b DONE:** `deriv_add` (additivity) + `deriv_mul` (Leibniz), transported from
    `Polynomial.derivative_add`/`derivative_mul` via `toPolynomial_injective`.
  - **5c BLOCKED (recorded):** Mathlib has **no** derivation/`derivative` on `RatFunc` (searched
    `FieldTheory/RatFunc/*` — none). So the `DenseFrac` quotient-rule derivative has no ready Mathlib
    bridge target. Options for later: (a) define a `RatFunc` derivation Mathlib-side (needs
    representative-independence — nontrivial) and bridge to it; (b) bridge the fraction derivative into
    the engine's own differential-field abstraction (Phase 6) rather than to a standalone RatFunc
    derivation. Deferred until Phase 6 clarifies which target the engine wants.
  - **5-API DONE:** `PolyBridge/Basic.lean` — added `toPolynomial_C`/`toPolynomial_monomial` (completes
    the bridge hom-square family the engine consumes). **← NEXT: Phase 6** (re-anchor the Risch engine
    as commuting squares over CAlgebra carriers).
  - (4c-ii generic depth-`n` tower deferred — instance-recursion plumbing; not blocking Phase 5/6.)
- **Phase 6…N — re-anchor the engine.** Port Hermite → Rothstein–Trager → residues/log part →
  LRT → RDE / coefficient recursion → tower orchestration → algebraic layer, each restated as a
  transported commuting square over `CAlgebra` carriers. Reproduce the end-to-end `cIntegrate`
  examples. This is the bulk. **← ACTIVE.**
  - **6a DONE:** `Diff/DifferentialRing.lean` — `deriv` packaged as `Derivation ℤ`, giving a
    `Differential (DensePoly R)` instance (Mathlib `Differential R = Derivation ℤ R R`). The CAlgebra
    polynomial carrier is now a Mathlib **differential ring**, so the abstract Risch/Hermite
    development (over `[Differential K]`) can run over it, with `toPolynomial` carrying each derivation
    step to `Polynomial.derivative`.
  - **6c-sqf DONE (2026-07-21): squarefree KERNEL** (`Poly/Squarefree.lean`) — first engine-math
    port onto CAlgebra. Bridge transports `isUnit/squarefree/isCoprime_toPolynomial_iff` (placed
    here, not Operations — `Squarefree`/`IsCoprime` are outside the base import closure; ★ Mathlib
    lesson: `isUnit_of_mul_eq_one` no longer exists in this Mathlib (Dedekind-finite refactor) —
    construct `Units` directly). Derivative criterion `squarefree_iff_isCoprime_deriv` under
    `[PerfectField R]` (covers char 0 via `PerfectField.ofCharZero`), proved as a pure rw-chain
    through `PerfectField.separable_iff_squarefree` + `separable_def` + the transports —
    hypothesis-free (works at `p = 0`). **`DecidablePred (Squarefree)`** via the gcd size test
    (`squarefree_iff_gcd_deriv_size` + `isUnit_iff_size_eq_one`). `sqfreePart p = p / gcd(p, p′)`
    with exact-division satellites. New satellites: `size_C` (Dense), `isUnit_C` (Division),
    `isUnit_iff_size_eq_one` (Euclid), class-level `gcd_ne_zero_of_left` +
    `isCoprime_iff_isUnit_gcd` (Gcd/Dense — the Bézout block, which also DEDUPS `isCoprime_norm`
    in Frac/Basic to one line).
  - **6c-sqf-2 DONE (2026-07-21): keystone + Musser decomposition.**
    `DeepWiki/Algebra/SquarefreeGcd.lean` (TOP-LEVEL Algebra area, per user — Mathlib-side
    statements live beside `SquarefreeDeflation`, not in CAlgebra):
    `Polynomial.squarefree_div_gcd_derivative` — over char 0, `p / gcd(p, p′)` is squarefree;
    the per-prime max-power argument (`Nat.findGreatest`, `derivative_pow`, char-0 `C k ∤`,
    `degree_derivative_lt`); a Mathlib gap, upstream candidate. Transported:
    `squarefree_sqfreePart` (via gcd-agreement + unit cancellation). **Musser's `sqfDecomp`**
    (recursion on `gcd(p, p′)`, size strictly drops in char 0 — NO fuel, unlike Yun's stalling
    loop) with `squarefree_of_mem_sqfDecomp` (every factor squarefree). ★ Lean lessons re-hit:
    decreasing_by-only class args need explicit binders; `rw [← h]` self-referential when the
    RHS occurs inside the goal's other operands; ED-`/` vs `div` spelling for `ring`/`omega`
    atoms — ascribe. DONE next sitting (6c-sqf-3, 2026-07-21): **exponent-exact
    reconstruction** `sqfDecomp_spec`: `p ~ powProd L 1 = ∏ᵢ pᵢ^i` AND `sqfreePart p ~ L.prod`,
    by the two-invariant Musser induction glued by `gcd_deriv_gcd_sqfreePart_associated`
    (`gcd(g, s) ~ sqfreePart g` — both radicals of `g`). New Mathlib-side stack in
    `DeepWiki/Algebra/SquarefreeGcd.lean` (all upstream candidates): shared cores
    `natDegree_pos_of_irreducible'`, `exists_max_pow_dvd`, `pow_not_dvd_derivative` (the char-0
    multiplicity drop; keystone A refactored onto it); keystone B
    `irreducible_dvd_div_gcd_derivative` (prime coverage, via `Prime.pow_dvd_of_dvd_mul_right`);
    generic UFD lemma `UniqueFactorizationMonoid.dvd_of_squarefree_of_forall_prime_dvd`
    (squarefree + prime coverage ⇒ dvd, by nodup normalizedFactors counts); workhorse
    `squarefree_dvd_div_gcd_derivative` (every squarefree divisor divides the squarefree part).
    Our side: `toPolynomial_sqfreePart_associated` extracted (squarefree_sqfreePart now 4 lines),
    `powProd`/`powProd_succ` (staircase product). ★ Lessons: `Associated` is a def unfolding to
    `Exists` — dot-notation `.symm` on an ascription fails, use prefix; multi-theorem files with
    same-named induct cases make regex anchors dangerous.
  - **6c-sqf-4 (2026-07-21): Squarefree area + Yun + dispatch class.** Squarefree things moved
    to their own area `CAlgebra/Squarefree/{Basic,Musser,Yun,Dense}.lean` (+aggregator;
    `Poly/Squarefree.lean` git-mv'd to `Basic`, Musser split out as `sqfDecompMusser`).
    **Yun's algorithm** (`Squarefree/Yun.lean`): the loop has NO structural termination measure
    (constant factors stall `c`), so instead of the heavy Yun invariant algebra it is
    **checker-validated**: `sqfDecompYunRaw` = fuel-bounded sweep (fuel `p.size` ≥ max
    multiplicity), `sqfDecompYun` = raw output validated by the DECIDABLE contract (factors
    squarefree — decidable; both Associated clauses via the cross-scaled certificate
    `associated_of_cross_mul_C : p·C(lc q) = q·C(lc p) ∧ q ≠ 0 → Associated p q`, now in
    `Basic`), falling back to Musser on failure — full spec proven with zero Yun theory.
    **Dispatch class `DensePolySquarefree`** (`Squarefree/Dense.lean`, the `DensePolyGcd`
    pattern): fields = `sqfDecomp` + the three contract clauses; Musser instance priority 100
    (default), checked-Yun 90. ★ Benchmarks (ℚ, 20 reps): raw Yun beats Musser 1.4–1.7×
    (141→89ms, 508→297ms, 528→373ms) but the contract check eats the gain (yun-check
    158/492/656ms ≈ Musser) — hence Musser stays default. Path to flip: prove Yun's invariants
    directly (drops the check); recorded as future work, not scheduled. ★ Lesson: class-field
    projections at a `fun p => Cls.field p` eta-expansion can leave the parent-class instance
    slot as a bare metavar — supply `@`-explicit `inferInstance`s in guard defs.
  - **6c-sqf-5 (2026-07-21): Yun SELF-VALIDATING — checker dropped, Yun is default.** The
    runtime contract check is gone; Yun's spec is proven directly via a **sum-free ghost
    invariant** (no classical multi-factor derivative sums). `IsYunState g c d` := `c`
    squarefree covering the primes of ghost `g`, plus the state identity `d·g = c·deriv g`
    (equivalent to the textbook `d = p′/g − c′` by the product rule; ghost chain = the Musser
    descent). Mathlib side (`DeepWiki/Algebra/SquarefreeYun.lean`, upstream candidates):
    `yun_prime_dvd_iff` — for prime `q ∣ c`, **`q ∣ d ⟺ q ∤ g`** (extract exact power
    `g = qᵏh`, cancel `qᵏ` from the identity, char-0 kills the `k·w·q′·h` term);
    `Polynomial.yun_step` — `(c/P) ∣ g` + new state for ghost `g/(c/P)` + the new identity by
    pure cancellation algebra; `associated_of_squarefree_of_prime_dvd_iff` (UFD-generic).
    Engine side: `IsYunState.step` transports through the bridge (new satellites
    `toPolynomial_div_of_dvd`, `prime_toPolynomial_iff` in `Poly/Euclid.lean`; surjectivity via
    `ofPolynomial`/`toPolynomial_ofPolynomial`); `yunAux_spec` fuel induction — fuel ≥ ghost
    size suffices because the ghost strictly shrinks while nonunit (`g = c₂·g₂`, `c₂` nonunit)
    and a unit `c₂` empties every later sweep (`yunAux_eq_nil`); reconstruction telescopes
    `c·g = P·c₂·(c₂·g₂)` with `powProd_succ`. Priorities flipped: **Yun default (100)**,
    Musser 90. Bench: dispatched = Yun = 82/268/350ms vs Musser 115/469/495ms (1.4–1.75×).
    ★ Lessons: `rw [← hPc']` where `c` occurs inside `c/P` self-rewrites — use
    `conv_lhs/rhs => rw [...]` or `.symm.trans (mul_comm ..)` witnesses; `Prime` transport
    through the RingEquiv needs surjectivity for the mul-direction (obtain ⟨q, rfl⟩ from
    `toPolynomial_ofPolynomial`); `NormalizationMonoid K[X]` synthesis needs `[DecidableEq K]`.
  - **6c-pf-1 (2026-07-21): squarefree partial fractions — `CAlgebra/PartFrac/Basic.lean`.**
    `a/p = poly + Σᵢ Σⱼ aᵢⱼ/dᵢʲ` over the dispatched decomposition, first consumer of the
    `DensePolySquarefree` contract. Pieces: `bezA`/`bezB` (computable scaled Bézout from
    `EuclideanDomain.gcdA/gcdB` — divide by the constant gcd via `C γ⁻¹`, identity
    `bezA·u + bezB·v = 1` under `IsCoprime`); `splitCoprime` (`a/(uv) = b/u + c/v`, `b`
    reduced mod `u`, spec `b·v + c·u = a` by pure `ring` after `mod_eq_sub`); `adicExpand`
    (`(poly, [a₁…aₙ])`, Horner-fold spec `foldl (acc·f + x) = a`, sizes < `f.size`);
    `partFracAux` staircase sweep + semantic spec in **RatFunc** via
    `toRatFuncHom := algebraMap ∘ equiv` (`invPowSum` = Horner foldr in `1/F`; seed lemma
    `foldr_div_seed`; the split/adic steps are `mul_div_mul_right` cancellations —
    unconditional field lemmas `add_div`/`div_div` need no nonzeroness). Coprimality of the
    split feeds from `isCoprime_powProd_of_squarefree` (new Squarefree/Basic satellite, with
    `powProd_ne_zero` + `dvd_prod_of_prime_dvd_powProd`; `squarefree_of_associated`
    un-privated). Top `sqfPartFrac` absorbs the reconstruction constant
    (`a · (powProd L 1)/p`) so the spec reads against `a/p` itself; numerator sizes < factor
    sizes; factors squarefree. Verified numerically over ℚ (4 point-evaluation checks).
    ★ Lessons: `nth_rewrite` for `gcd = C (gcd.coeff 0)` (gcd occurs inside its own coeff);
    `conv_lhs => rw [← hw]` still hits ALL lhs occurrences — `nth_rewrite k` is the precise
    tool; guard defs of class projections again needed `DensePoly.`-qualification.
    DONE next sitting — see 6c-int-1.
  - **6c-int-1 (2026-07-21): Hermite reduction (rational base case) + the RatFunc derivative.**
    New Mathlib-side `DeepWiki/Algebra/RatFuncDerivation.lean` (upstream candidates):
    `RatFunc.deriv` (quotient rule on `num`/`denom`), keystone `deriv_div` (representation
    independence — differentiate the cross-multiplication identity, close by
    `linear_combination`), `deriv_algebraMap`/`deriv_add`/`deriv_mul` (laws via num/denom
    representations + `field_simp; ring`), packaged as `Differential (RatFunc K)`.
    ★ Diamond: `Derivation ℤ (RatFunc K)` synthesizes RatFunc's polynomial-lift `Algebra ℤ`
    instance, NOT the `Ring.toIntAlgebra` that `Differential` pins — fixed by `letI`-shadowing
    inside the instance (and the `AddMonoidHom.mk'/toIntLinearMap` route whnf-times-out;
    explicit-field construction avoids it — do NOT raise heartbeats).
    Engine: `Diff/RatFunc.lean` (`toRatFuncHom` differential morphism);
    `Poly/Derivative.lean` gains `deriv_C_mul`, `deriv_pow_succ` (successor form,
    subtraction-free). `Integrate/Hermite.lean`: `hermiteFactorAux` (descending sweep per
    factor: Bézout split `c = t·d′ + b·d` via `splitCoprime c d (deriv d)`, integration by
    parts sheds one denominator power into a `DenseFrac`-accumulated rational part),
    `hermite_step` (the per-term identity — after `field_simp`, ONE `linear_combination`
    with coefficient `−C(n+1)·F^(2n+2)` against the Bézout image), `hermiteFactorAux_spec`
    (functional induction; assembly = `linear_combination ih + hstep`), and
    `hermiteReduce` on top of `sqfPartFrac`: **`a/p = G′ + poly + Σᵢ bᵢ/dᵢ` proven in
    `RatFunc R`** (`hermiteReduce_spec`) with all remainder denominators squarefree
    (`hermiteReduce_denom_squarefree`). Verified numerically over ℚ (4 point checks; sample
    `a₁/((x+1)³(x²+1)²)` gives rational part over `(x+1)²(x²+1)` exactly).
    NEXT: the log part (Rothstein–Trager) on the squarefree remainders.
  - **6c-diff-1 (2026-07-21): derivative moved behind Mathlib's `Differential` interface,
    instances SCOPED.** `Poly/Derivative.lean` git-mv'd to `Diff/Derivative.lean`: the raw
    `deriv` recursion is now **private**; the public spelling is `p′` via a **computable**
    `Derivation ℤ` packaged as `Differential (DensePoly R)`. ★ DESIGN: all three formal
    `Differential` instances (DensePoly / Polynomial in `Diff/Basic` / RatFunc in
    `Algebra/RatFuncDerivation`) are **scoped under `FormalDiff`** (`open scoped
    Differential FormalDiff` to use): the formal derivative (constant coefficients) is only
    ONE derivation on these carriers — a future differential-coefficient tower instance
    (`[Differential R]` + monomial data, the Risch extension `D(Σaᵢtⁱ) = Σ(Daᵢ)tⁱ + (∂/∂t)·Dt`)
    gets its OWN scope, so the two can never collide in one instance space; opening exactly
    one scope per file is the discipline. Satellite lemmas keep their names but are restated
    in `′`-form (`deriv_mul : (p*q)′ = …`), so consumer proofs kept their `rw` chains — the
    migration (~200 sites, 8 files) was a regex pass `deriv x → x′` + scope opens.
    `deriv_ne_zero` re-proved through the bridge (its old proof used the now-private
    coefficient lemma). Computability guard `fun p => p′` compiles ✓ and `#eval p′` runs.
    ★ Lean lessons: `scoped[NS] instance` is NOT implemented (Mathlib's scopedNS attr) — use
    an explicit top-level `namespace FormalDiff … scoped instance … end`; modifier order is
    `noncomputable scoped instance`.
  - **6c-int-2 (2026-07-21): Hermite BUNDLED — `DenseFrac` in, `HermiteResult` out,
    hypothesis-free spec.** `hermiteReduce : DenseFrac R → HermiteResult R`: input as a
    canonical fraction makes `p ≠ 0` automatic (monic denominator), so `hermiteReduce_spec`
    has NO hypotheses: `toRatFunc f = rational′ + poly + toRatFunc logPart`. The output
    structure carries `logPart : DenseFrac` (auto-canonical: monic + coprime, so the log
    stage's `b/d` arrives reduced) plus the bundled invariant `logPart_den_squarefree`.
    ★ The proof engine is a new Frac/Basic satellite — **the canonical denominator's
    universal property** `den_dvd_of_eq_div` (den divides ANY representing denominator, by
    coprime cancellation of the cross-multiplication) — from which `den_normalize_dvd`,
    `den_add_dvd` (den of sum ∣ product of dens), and the log-part squarefreeness all fall
    out: den(Σ normalize bᵢ dᵢ) ∣ ∏dᵢ ~ sqfreePart p, squarefree. Also
    `toRatFunc_list_sum`, `partFracAux_fst` (the sweep's factor column = the input list).
    Old pair-based API deleted; guard now `DenseFrac R → HermiteResult R` (Prop field
    erased, still computes). Numeric checks pass; sample logPart denominator comes out as
    the radical `(x+1)(x²+1)` exactly.
  - **6c-int-3 (2026-07-21): HERMITE COMPLETENESS — rational integrability DECIDED.**
    `hermiteReduce_complete : (∃ g : RatFunc R, g′ = toRatFunc f) ↔ (hermiteReduce f).logPart
    = 0` — hypothesis-free, decidable RHS, constructive witness (`rational +
    polyIntegrate poly`) in the affirmative case. First completeness theorem of the CAlgebra
    arc. Three layers:
    (1) Mathlib-side `DeepWiki/Algebra/RatFuncProper.lean` (upstream candidates):
    `RatFunc.IsProper` + closure laws (add/neg/sub/list-sum/div-by-poly/deriv), the
    representation transfer lemmas (`isProper_of_eq_div` both directions via
    cross-multiplication degree counting), `denom_associated_of_eq_div` (coprime reduced
    representations have associated denominators), and the **KEYSTONE obstruction**
    `eq_zero_of_deriv_of_squarefree_denom`: a nonzero proper fraction with squarefree
    denominator is no derivative — any prime π with exact multiplicity m in a candidate's
    denominator gives the derivative's numerator exact multiplicity m−1
    (`pow_not_dvd_derivative` again!) hence the derivative's denominator multiplicity
    m+1 ≥ 2. (2) `polyIntegrate` in Diff/Derivative (computable antiderivative,
    `(polyIntegrate p)′ = p`). (3) logPart PROPERNESS proven semantically (no size tracking
    through the algorithm — the Bézout cofactors are genuinely unbounded): invPowSum of
    bounded numerators proper + accumulated rational parts proper + `IsProper.deriv`/`sub`
    closure ⇒ each factor remainder proper ⇒ logPart proper
    (`hermiteReduce_logPart_isProper`, public). Decision procedure validated on 5 evals
    (incl. a hand-built derivative recognized integrable). ★ Lessons: `show` against a
    projection of a structure-literal def whose fields contain WF-recursion whnf-times-out —
    `simp only [defName]` instead; `add_le_add le_rfl h` beats guessing left/right variants.
  - **6c-int-4 (2026-07-21): Lazard–Rioboo–Trager log part — the ALGORITHM.**
    `Integrate/LogPart.lean`: `lrtLogPart : DenseFrac R → List (Q(z) × S(z,x))` with
    `∫ b/d = Σᵢ Σ_{Qᵢ(c)=0} c·log Sᵢ(c,x)`. Pieces: bivariate carrier `DensePoly
    (DensePoly R)` (x outermost; `liftX`, `zC`, `zContent`/`zPrimitive` via the dispatched
    gcd), Rothstein–Trager resultant `rtResultant = res_x(d, b − z·d′)` through the EXISTING
    Mathlib-bridged Sylvester `resultant` (certificate hook `toPolynomial_resultant` for
    free; det-based → slow beyond small degrees, PRS-based resultant is the efficiency
    upgrade), **primitive pseudo-remainder sequence** `primPRS` (pseudoDivMod is
    CommRing-generic; coefficient exact-division = field `div` on `DensePoly R`; content
    differences vs true subresultants specialize to CONSTANTS at z = c, so log-derivatives
    are unaffected — the LRT normalization is an efficiency matter here, not correctness),
    squarefree decomposition of the resultant via `DensePolySquarefree` (dispatch pays off:
    no CharZero needed on the defs, only at instances). Factor at exponent i pairs with the
    PRS element of x-size i+1, or `liftX d` when i = deg d; constant factors dropped.
    Structural spec `lrtLogTerms_fst_squarefree` (every Q squarefree + nonconstant).
    VALIDATED on 5 known integrals incl. multi-factor mixed-multiplicity `∫1/(x³−x)` →
    `−log x + ½log(x²−1)` and complex-root `∫1/(x²+1)` (data stays symbolic in Q).
    NEXT (the certificate arc): the differential identity `Σᵢ Tr-sum of c·Sᵢ′/Sᵢ = b/d`
    needs `AdjoinRoot Qᵢ` étale-algebra machinery — multi-session, analogous to the old
    engine's soundness arc; plus properness-shaped uniqueness via `RatFuncProper`.
  - **6c-res-1 (2026-07-21): Resultant area + PRS resultant + `DensePolyResultant` dispatch.**
    `Matrix/Sylvester.lean` git-mv'd to `Resultant/Sylvester.lean`; new area
    `CAlgebra/Resultant/{Sylvester,PRS,Dense}.lean`. **`resultantPRS`** (`Resultant/PRS.lean`):
    Euclidean-descent resultant over ANY computable `[EuclideanDomain S]` coefficients
    (pseudo-divide the larger argument, correct by signs and lc-powers with EXACT `/`,
    pad slack bounds down; WF on `(f.size + g.size, m + n)` lex). ★ **`resultantPRS_eq`**:
    full equivalence with Mathlib's Sylvester-determinant resultant on valid degree bounds —
    the functional induction glues exactly one Mathlib identity per branch
    (`resultant_add_mul_right` for the mod step, `resultant_C_mul_right` for the lc-scale,
    `resultant_add_left/right_deg` for padding, `resultant_comm` + sign-cancel, constant/zero
    base cases); the pseudo-quotient degree bound is derived from the pseudo-division
    identity alone (no implementation facts). `Resultant/Dense.lean`: class
    `DensePolyResultant` (contract = agreement with `Polynomial.resultant` on valid bounds;
    det fallback at 100, PRS at 200 for Euclidean coefficient domains). `rtResultant` in
    LogPart now dispatches — the LRT resultant over `K[z]` runs the PRS (deg-6 denominator:
    instant vs an 11×11 permanent-style det ≈ 40M terms; all 5 LRT regressions byte-identical).
    ★ Lessons: WF-`induct` substitutes scrutinees in base cases (case arities shrink); passing
    `le_of_eq` where an INEQUALITY at a different bound is expected silently pins unification
    — give `by rw [...]; omega` proofs shaped by the expected type.
  - **6c-res-2 (2026-07-21): PRS machinery consolidated under `Resultant/`.**
    `Gcd/Subresultant.lean` git-mv'd to `Resultant/Subresultant.lean` (the subresultant PRS
    is resultant-theoretic; the gcd is one consumer of the descent, like the resultant and
    the LRT sequence); the bivariate helpers (`liftX`, `zC`, `zContent`, `zPrimitive`,
    `primPRS`) moved from `Integrate/LogPart` into `Resultant/PRS`'s bivariate section.
    Import chain: `Resultant/Subresultant` ← `Gcd/Dense` ← `Resultant/PRS` (no cycle).
    Pure move + import rewiring, zero declaration changes. The Resultant area now owns the
    whole PRS family: subresultant-gcd, Euclidean-descent resultant, primitive bivariate
    sequence. Follow-up same day: `Resultant/PRS.lean` split by sequence kind into
    `Resultant/Euclidean.lean` (descent resultant + `resultantPRS_eq`) and
    `Resultant/Primitive.lean` (bivariate lifts/contents/`primPRS`) — the area now reads
    Sylvester / Subresultant / Euclidean / Primitive / Dense. And the class interface
    dropped its `(m, n)` bound parameters: the normalized representation commits the exact
    degree (`size − 1` = `natDegree` unconditionally, `0` included via ℕ-sub), so
    `DensePolyResultant.resultant : DensePoly S → DensePoly S → S` with a HYPOTHESIS-FREE
    contract at the canonical bounds (the same bundling payoff as `hermiteReduce`); the
    4-arg algorithms stay as the underlying implementations. Bonus robustness: `rtResultant`
    no longer hard-codes `d.size − 2` for the second bound — the canonical bounds
    self-adjust if the top coefficient ever degenerates. Follow-up: the bounds removed from
    the ALGORITHMS too — `resultant` (Sylvester det) and `resultantPRS` are now 2-arg at
    canonical degrees with hypothesis-free bridges (`toPolynomial_resultant`,
    `resultantPRS_eq` against Mathlib's resultant at `natDegree` bounds); the 4-arg descent
    survives only as `private resultantPRSAux` (its recursion states genuinely need bound
    bookkeeping — the private-aux idiom); `sylvester` keeps widths (it IS parameterized
    matrix data); new Operations satellite `natDegree_toPolynomial_eq_size_sub_one`
    (unconditional, `0` included).
  - **6c-res-3 (2026-07-21): the descent PARAMETRIZED — one engine, one proof, three
    resultants.** All PRS variants differ only in what they strip from the remainder before
    recursing, so `Resultant/Euclidean.lean` now hosts **`resultantDescent`**, parametrized
    by `clean : DensePoly S → S × DensePoly S` with two obligations: `hsize` (strip doesn't
    grow — feeds termination) and, for the proof only, the reconstruction identity
    `C (clean r).1 * (clean r).2 = r`. **`resultantDescent_eq`** proves the descent = the
    Sylvester determinant for ANY such clean — each strip costs exactly one
    `resultant_C_mul_right`. Instantiations: `resultantPRS` (trivial clean) and
    `resultantPRSPrimitive` (`Resultant/Primitive.lean`: generic `polyContent` = Euclidean
    gcd-fold, `polyPrimitive`, reconstruction + size satellites — no nonzeroness conditions
    anywhere, the `content = 0 ⟹ r = 0` degeneracy handles itself). ★ BENCH: primitive
    **320×** over the trivial descent on a degree-8 bivariate LRT pair (153ms vs 49.4s —
    coefficient blowup vs content control), results equal; registered at priority 300 (over
    Euclidean 200, det 100). Subresultant-as-resultant (the stateful β/ψ variant) would need
    history threading through the descent — not currently worth it with primitive winning;
    recorded. ★ Lesson: `exact lemma _ _ (...)` with underscores for lambda-parameters of a
    WF-def can send the unifier INTO the WF-body (isDefEq timeout on `EuclideanDomain.gcd`)
    — pass the lambdas explicitly; same for `set`-opaquing mapped lists whose functions
    contain WF-defs. Naming follow-up: the family is now uniform —
    `resultantPRSEuclidean` / `resultantPRSPrimitive` (future slot:
    `resultantPRSSubresultant`), bivariate sequence `prsPrimitive` (was `primPRS`),
    instances `euclideanDensePolyResultant` / `primitiveDensePolyResultant`.
  - **6c-res-4 (2026-07-21, IN REVIEW — uncommitted): subresultant exactness arc opened;
    state-threaded descent; theory MIGRATED from the old engine.**
    (1) `resultantDescent` generalized to thread a state `σ` (pads pass it, mod steps update
    it; `PUnit` for the stateless cleans). (2) The equivalence refactored into the
    **invariant-carrying core** `resultantDescent_eq_of_invariant`: the reconstruction
    identity is required only at states satisfying an invariant `I` (entry + swap-closure +
    step-preservation), only for the pseudo-remainders actually cleaned — the KEY
    architectural fact being that unchecked β-divisions are exact only at REACHABLE states,
    so an unconditional `hclean` is impossible for Collins–Brown; the unconditional
    `resultantDescent_eq` is now the `I := True` corollary. (3) `cleanSubresultant`
    UNCHECKED (per user directive — no runtime check), with
    `resultantPRSSubresultant_eq_of_invariant` as the hypothesis-carrying intermediate;
    the dispatch instance is DEREGISTERED until the invariant is discharged.
    (4) **Old-engine theory retired into `DeepWiki/Algebra/`** (git mv, imports rewired
    incl. 5 per-paper Sources catalogs; namespaces kept to avoid mass renames):
    `SubresultantSpec.lean` (912L, determinantal `subresultant` on `R[X]`),
    `PseudoDivision.lean` (315L), `SubresultantPRS/{Telescope,Remainder,ClosedForms}.lean`
    (671L — incl. the EXACT-constant `subresultant_eq_pseudoRem` and the normal-chain
    closed form `subresultant_prs_normal_eq`).
    NEXT (Phase C, the discharge): define the concrete chain invariant (valid-history
    formulation), prove hclean/hstep/hswap from the ClosedForms for NORMAL chains
    (`subresultant_prs_normal_eq`), then the defective case via the collapse lemmas
    (`beta_fold`, `lc_collapse_defective`) — the part the old engine left as its "LRT
    grounding" frontier; then re-register the instance (bench had it at 496ms, between
    primitive 153ms and Euclidean 49.4s). PHASE C OPENED same sitting: ★ the Ducos-β recipe
    (mirrored from the old engine) is WRONG at the first step (β₁ must be ±1, not lc² — the
    deleted runtime check had been silently absorbing exactly this; the old engine never hit
    it because its PRS was used only up-to-similarity for gcd/log-arguments). Replaced by
    the **reduced PRS** (Collins '67 — whose Sources catalog we already hold): state =
    pending divisor α (initially 1), next state lc(f)^{δ+1} — no special cases, and
    `subresultant_prs_normal_eq` is stated in EXACTLY this normalization. New:
    `cleanReduced`/`resultantPRSReduced` (unchecked) +
    `resultantPRSReduced_eq_of_invariant`, and **brick one of the discharge PROVEN**:
    `subresultant_eq_pseudoMod` — the first pseudo-remainder is `(−1)^{δ+1}` times the
    determinantal subresultant `S_{deg g − 1}(tf, tg)`, by instantiating the migrated
    `subresultant_eq_pseudoRem` at the bridged pseudo-division identity
    (`pseudo_identity`/`pseudoDiv_natDegree_le` un-privatized as cross-file bridges).
    REMAINING for the discharge: the inductive telescope (step ℓ's prem = αₗ·subresultant of
    the ORIGINAL pair, via Telescope/ClosedForms), packaged as the concrete invariant.
  - **6c-res-5 (2026-07-21, committed 51fdde82): papers verified; OLD ENGINE FIXED;
    cross-engine integration.** OCR-read Brown–Traub 1971 (in `references/`, catalog
    Doi_10_1145_321662_321665): (33)/(35) confirm `cleanReduced` = Collins' reduced PRS
    verbatim; Lemma 1 (15) confirms brick one; §7 (38)–(41) give the TRUE subresultant-PRS
    recipe — β first-step `(−1)^{δ+1}`, later `−lc(left)·ψ^δ` with UN-updated ψ; ψ-update
    `(−lc right)^δ/ψ^{δ−1}` with the RIGHT element's lc. The old engine's recipe (update-
    first, left-lc) was WRONG — fixed `Compute/Subresultant.lean`'s `subresPRS.go` +
    the `goPsi'`/`goBeta`/`goStep` mirrors in `SubresultantCorrectness.lean` (state 4-tuple's
    ℕ slot repurposed as the first-step flag — zero type churn; conditional chain theorems
    survive verbatim since exactness was always hypothesis-carried). Bronstein-catalog
    worked examples re-verified by native_decide under the corrected recipe (degree
    profiles/filters unchanged). ★ INTEGRATION: the new engine reproduces Bronstein Ex 2.4.1
    EXACTLY — `rtResultant = 45796·(4t²+1)³` coefficient-for-coefficient and
    `lrtLogTerms` factor `= 4t²+1` — now pinned as native_decide theorems IN THE CATALOG
    (`rtResultant_ex241_hex_engine`, `lrtLogTerms_ex241_hex_engine`), the first cross-engine
    agreement facts.
  - **6c-res-6 (2026-07-21, committed 51fdde82): the exactness DISCHARGE — DONE.**
    `ReducedExact 1 f g` proven unconditionally (any computable Euclidean coefficient
    domain), axiom-clean; `resultantPRSReduced_eq` hypothesis-free; instance
    `reducedDensePolyResultant` registered at priority 250. ★ The proof is NOT the planned
    BT §6 global telescope but a strengthened LOCAL invariant, `SubresLedger α f g`
    (`C (α^{deg g − j})` factors out of EVERY `S_j(tf,tg)`, `j < deg g`): trivial entry at
    `α = 1`; head = ledger@`deg g−1` + brick one; swap via `subresultant_swap` with
    power-splitting; step via `subresultant_prs_step` with the eq-37-localized exponent
    identity `(a−b+1)(b−j) = (a−c) + [(a−b+1)(c−j) + (a−b)(b−c−1)]` (Nat.le.dest
    decomposition + ring — omega can't multiply), then cancel `C(α^{b−j})`, `C(lc^{a−c})`
    in the domain; discharge by WF-recursion on `f.size + 2·g.size`
    (`reducedExact_of_ledger` → `reducedExact_all`). Re-bench: primitive 148ms < reduced
    460ms ≪ Euclidean ~49s — 300/250/200 confirmed, dispatch unchanged, cross-agreement
    `decide`-checked. Plan doc `docs/subresultant-exactness-telescope.md` rewritten as the
    post-mortem. This closes the old engine's "LRT grounding" frontier.
  - **6c-res-7 (2026-07-21, committed 66768543): gcd re-expressed over the descent
    engine.** The engine now has TWO projections over one `clean` policy: `resultantDescent`
    (constant ledger → resultant) and new `gcdDescent` (last nonzero element → gcd, no
    bound/scalar bookkeeping). `gcdSubAux` retired: the subresultant β-recipe is now the
    standalone policy `cleanSubresultant` (state `(g, h)`, β = (−1)^{δ+1}·g·h^δ), and
    `gcdSubresultant := gcdDescent cleanSubresultant … (1,1)` — same values, same public
    API (`_dvd_left/right`, `dvd_`, `associated`, Mathlib bridge statements unchanged). The
    universal-property lemmas are generic over any unit-β policy with a nonzero-state
    invariant (`gcdDescent_dvd`, `dvd_gcdDescent` — mirroring
    `resultantDescent_eq_of_invariant`'s contract shape). BONUS: the SAME policy through the
    resultant projection gives `resultantPRSSubresultant`+`_eq` over a FIELD,
    hypothesis-free (every β a unit — the invariant discharges trivially; the DOMAIN-level
    version still needs Brown '78 ψ-integrality, unchanged). Sanity: engine-projected gcd
    recovers d8 up to a unit; field subresultant resultant = primitive on d8/d8′. No
    instance registered for the field variant (primitive still dispatches).
  - **6c-res-8 (2026-07-21, committed 55464d88): the sequence projection.** Third
    engine projection `prsDescent` (returns the cleaned PRS itself from the second entry
    on); the bivariate `prsPrimitive` re-expressed as its z-content-policy instantiation —
    FUEL PARAMETER RETIRED (WF on `g.size` via `zPrimitive_size_le`), LRT call site
    simplified. LRT outputs value-identical (scratch re-run + catalog native_decide pins).
  - **6c-res-9 (2026-07-21, committed 55464d88): ONE KERNEL.** `descentTrace` is now
    the engine's single recursion (walk the PRS under a clean policy, record each divisor +
    extracted constant); all three projections consume it: `prsDescent` = map,
    `gcdDescent` = `lastElem` fold (step/base satellites `gcdDescent_of_size_{ne_,eq_}zero`
    replace `.induct`-unfolds; universal-property proofs re-anchored on
    `descentTrace.induct`), `resultantDescent` = `resultantOfTrace` bound-carrying fold +
    a one-time entry `resultant_comm` (replacing the old fused-swap branch case10).
    Equivalence proof reorganized compositionally as `resultantOfTrace_eq` (same per-branch
    Mathlib identities, trace-identification invariant `∃ st, trace = descentTrace …`;
    NO closed-form telescope needed — foldr keeps it local). Computationally identical
    (β's were already computed by every projection; corrections still only in the resultant
    fold): primitive 163ms / reduced 504ms, all agreement + gcd + LRT value checks
    reproduce. ★ Lean gotchas: WF-def with inner `match` needs `.eq_def` rewrites + `dsimp
    only` for iota; `subst (ha : a = g)` eliminates `g` not `a` — use `rw [ha]`.
    REORG same sitting: kernel extracted to `Resultant/Descent.lean` (`descentTrace` +
    satellites + `prsDescent`/`lastElem`/`gcdDescent` + the generic gcd universal-property
    lemmas, kernel section generalized `EuclideanDomain`→`CommRing` — pseudo-division never
    needed more); `Euclidean.lean` = the resultant fold + equivalence only;
    `Subresultant.lean` = policy + instantiations + exactness arc only.
  - **6c-res-10 (2026-07-21, committed 8061e926): switchable PRS.** New dispatch class
    `DensePolyPRS` (Resultant/Dense.lean): an instance IS a clean policy bundled with
    unconditional strip exactness (`C β * cleaned = r`); `DensePolyPRS.prs` derives as the
    kernel's sequence projection. Instances: trivial 100 (CommRing), content 200
    (EuclideanDomain), z-content 300 at polynomial coefficients (via the dispatched
    `DensePolyGcd`) — the last needed the NEW `C_zContent_mul_zPrimitive` exactness
    (fold-dvd through the gcd class contract + `EuclideanDomain.mul_div_cancel'`;
    zPrimitive respelled with `/`). `lrtLogTerms` now consumes the class (both its
    resultant AND its PRS are dispatched); `prsPrimitive` retired. LRT values identical.
    ★ Gotcha: bivariate `toPolynomial_injective; ext i` recurses into inner-DensePoly
    coefficients — pin with `refine Polynomial.ext fun i => ?_`.
    SAME SITTING: class reshaped to an **invariant-carried contract** (`Inv`/`entry_inv`/
    `inv_step`; `clean_exact` guarded by `Inv` + `g.size ≠ 0`, specialized to the walk's
    `pseudoMod`) — this admits state-conditional policies, and the TRUE subresultant β now
    instantiates at priority 250 over any field (`subresultantDensePolyPRS`, sharing
    `cleanSubresultant` + its spec/step lemmas — de-privatized — with `gcdSubresultant`);
    stateless instances take `Inv := fun _ => True`. Field-carrier prs dispatch is now the
    subresultant policy (250 > content 200); bivariate unchanged (z-content 300).
  - **6c-res-11 (2026-07-21, committed): Reduced.lean split.** The Collins
    reduced-PRS arc (`cleanReduced`, `resultantPRSReduced`(+`_eq*`), `ReducedExact`,
    `exact_div_of_toPolynomial_C_mul`, brick `subresultant_eq_pseudoMod`, `SubresLedger` +
    swap/step + discharge) moved verbatim from `Subresultant.lean` to new
    `Resultant/Reduced.lean`, taking the heavy `import DeepWiki.Algebra.SubresultantPRS`
    with it. `Subresultant.lean` is now purely the field policy + gcd + field resultant
    (light imports), fixing the misnomer (it no longer houses Collins' reduced PRS).
    ★ Verified: `Gcd/Dense.lean`'s transitive import cone = 11 modules, ZERO determinantal
    theory — the whole Integrate stack no longer waits on `SubresultantSpec` to build.
  - **6b DONE:** `Diff/DifferentialBridge.lean` — gave `Polynomial R` a `Differential` instance (via
    `Polynomial.derivative`; Mathlib lacks it) and proved `toPolynomial_differential : toPolynomial p′
    = (toPolynomial p)′` — `toPolynomial` is a differential-ring MORPHISM (the derivation-level
    commuting square every ported engine step transports through). Also found: Mathlib has no
    `Differential (RatFunc R)` either, so the differential FIELD carrier (5c / field-level 6c) needs a
    RatFunc/DenseFrac derivation built by hand (quotient rule + representative-independence).
    **← NEXT: 6c** — differential field carrier (build the `RatFunc`/`DenseFrac` derivation) OR port
    the first engine algorithm (Hermite reduction, which is abstract over `[Differential K]` and can
    now be instantiated at `Polynomial R`) as a commuting square.
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
