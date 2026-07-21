# The elementary antiderivative of the CAlgebra rational integral

**GOAL**: upgrade the log-part soundness capstone from the in-`RatFunc` formal reading
(`toRatFunc g = logSumDeriv (residueSet g) (lrtLogArg …)`, landed `fa67c715`) to the
*represented-object* form: an actual antiderivative element `v = ∑ a·log Sₐ + w` living in
a differential (log-tower) extension of `RatFunc R`, with soundness literally
`algebraMap _ _ (toRatFunc f) = v′`. End state: **every canonical fraction over an
algebraically closed char-0 field has an elementary antiderivative, constructively via the
engine** — Liouville's classical theorem for rational functions, with the witness data
produced by `hermiteReduce` + `lrtLogTerms`.

## Existing infrastructure (survey, 2026-07-21 — reuse, don't rebuild)

The transcendental arc already built the abstract side; the missing work is *bridging*,
not new theory:

- `LiouvilleStructure/Core.lean`:
  `HasWeakLiouvilleForm F K g := ∃ ι [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
  (u : ι → K) (v : K), ↑g = ∑ x, ↑(c x) · logDeriv (u x) + v′` — exactly the shape our
  capstone RHS has (with `K = F = RatFunc R`, `v = 0`).
- `LiouvilleStructure/ElementaryTower.lean`: `IsElementary F a := ∃ S : LiouvilleStage F,
  HasWeakLiouvilleForm F S.carrier a`, with `IsElementary.of_hasWeakLiouvilleForm` (a
  *base* form certifies elementarity — no tower needed for the predicate) and the
  structure theorem `isElementary_iff` (Thm 5.5.2/5.5.3).
- `Engine/LiouvilleLogTower.lean`: `LiouvilleStage F` (finite chains of Liouville steps),
  `LiouvilleStage.base`, `LiouvilleStage.extend (S) (u : S.carrier)
  (hnd : NondegenerateLog u)` — the log-adjunction constructor already exists, gated on
  a nondegeneracy hypothesis.
- The `Differential (RatFunc R)` instance: the Liouville layer and our pinned
  `SymbolicIntegration.instDifferentialRatFunc_deepWiki` must be the SAME instance at
  every use site (they should be — it is the old engine's global instance; verify early,
  this is the classical-vs-real-instance lesson's territory).

## Phases (each gate-green; finish + report, commit only after user review)

### Phase 1 — the base Liouville form + `IsElementary` corollary — DONE (2026-07-21)

In `Integrate/LogPartSound.lean` (or a thin new `Integrate/LogPartElementary.lean` if it
crowds):

- `lrtLogPart_hasWeakLiouvilleForm (g : DenseFrac R) (hnum) (hsf) (hprop) :
  HasWeakLiouvilleForm (RatFunc R) (RatFunc R) (DenseFrac.toRatFunc g)` — shape
  adaptation of `lrtLogTerms_sum_sound`:
  - index `ι := ↥(residueSet g)` (`Fintype` from `Finset`), converting the `Finset` sum
    via `Finset.sum_attach`/`sum_coe_sort`;
  - constants `c a := algebraMap _ _ (Polynomial.C ↑a)` with `(c a)′ = 0` (constant
    derivative satellite — locate or add `deriv_algebraMap_C` for the deepWiki instance);
  - `u a := algebraMap _ _ (lrtLogArg g.num g.den.toPoly ↑a)`, `v := 0`.
  - `Algebra F F` is `Algebra.id`; check `algebraMap = id` rewrites (`algebraMap_self`).
- `lrtLogPart_isElementary … : IsElementary (RatFunc R) (DenseFrac.toRatFunc g)` :=
  `.of_hasWeakLiouvilleForm` of the above.

**Phase 1 notes (as landed):**
- New thin file `Integrate/LogPartElementary.lean` (kept the Liouville import out of
  `LogPartSound`'s cone), wired into the `Integrate.lean` aggregator.
- ★ Universe-monomorphic: `LiouvilleStage`/`IsElementary` carriers live in `Type`, so the
  file binds `{R : Type}` (not `Type u`) — first universe-0 boundary in the CAlgebra
  layer; downstream phases inherit it.
- `deriv_algebraMap_C` homed as an abstract-layer satellite in
  `RationalFunctionDerivative.lean` (extracted from `logDeriv_algebraMap_C_mul_eq`'s
  inline `hlogc`).
- Instance coherence confirmed: the Liouville layer's ambient `Differential (RatFunc R)`
  IS the pinned `instDifferentialRatFunc_deepWiki` (the anonymous global instance in
  `RationalFunctionDerivative.lean`) — the `logDeriv`s matched definitionally; only the
  `RatFunc.C`-vs-`algebraMap ∘ Polynomial.C` spelling needed a simp normalization
  (`simpa [map_zero, lrtLogTerm]`).

### Phase 2 — end-to-end: every canonical fraction is elementary-integrable — DONE (2026-07-21)

- `hermiteReduce_sound`: `f = (rational)′ + poly + logPart`; `polyIntegrate` gives
  `poly = (polyIntegrate poly)′` (existing satellite, used in `hermiteReduce_complete`).
- Combine into one weak Liouville form: log terms from Phase 1 (empty family when
  `logPart.num = 0` — case split; `logPart = 0` branch mirrors `hermiteReduce_complete`'s
  converse direction), `v := toRatFunc (hermiteReduce f).rational
  + toRatFuncHom (polyIntegrate (hermiteReduce f).poly) + (Phase-1 v)`.
- Capstone: `denseFrac_isElementary (f : DenseFrac R) :
  IsElementary (RatFunc R) (DenseFrac.toRatFunc f)` — hypothesis-free (over
  `[IsAlgClosed R] [CharZero R]`): **Liouville's theorem for rational functions**,
  constructive via the engine. This is a headline theorem; consider a
  `RationalIntegration`-side alias/home if the abstract layer wants it stated
  engine-free (it already has `ratFunc_eq_sum_residue_logDeriv` machinery — check for
  overlap before writing).

**Phase 2 notes (as landed):**
- Overlap check: no existing `IsElementary` statement anywhere in the abstract
  `RationalIntegration*` layer — the headline is new. (An engine-free abstract twin via
  `ratFunc_eq_sum_residue_logDeriv` remains possible but was skipped as duplicative.)
- ★ The two-instance boundary was live: `hermiteReduce_sound`'s `′` is the FormalDiff
  scoped instance, the Liouville layer's is the deepWiki global one. Bridged by
  `ratFunc_deriv_eq_deriv : RatFunc.deriv x = x′` (quotient rules on both sides via
  `RatFunc.deriv_div` / `ratFuncDeriv_mk`; the `show` step is the defeq
  global-deriv-is-`ratFuncDeriv` reduction). Lives in `LogPartElementary.lean`; the
  Phase-6 instance unification will subsume it.
- ★ Lean gotcha: `deriv_add` (`(a+b)′ = a′+b′`) does NOT rewrite here — the `′` is a
  coe-applied `Derivation ℤ`, and the ℤ-algebra instances diverge
  (`RatFunc.instAlgebraOfPolynomial R ℤ` vs `Ring.toIntAlgebra`, the Derivation-ℤ
  diamond). Instance-agnostic `map_add` rewrites fine — use it for `′`-additivity on
  `RatFunc`.
- New satellite `toRatFuncHom_polyIntegrate_deriv` (the ∫poly square in global-`′` form);
  `denseFrac_hasWeakLiouvilleForm` case-splits on `logPart.num = 0`
  (`hasWeakLiouvilleForm_tower_of_isDeriv` with `v = rational + ∫poly`) vs the Phase-1
  family with `v := v₀ + rational + ∫poly`.

### Phase 3 — the represented object: an antiderivative element in a log tower — DONE (2026-07-21)

The genuinely new lemma — the *assembly* (converse) direction of the structure theorem:

- `hasWeakLiouvilleForm_exists_antiderivative :
  HasWeakLiouvilleForm F F g → ∃ (S : LiouvilleStage F) (v : S.carrier),
  algebraMap F S.carrier g = v′`.
  Proof by induction on the finite log family: for each `(cᵢ, uᵢ)`, either
  `NondegenerateLog uᵢ` holds in the current stage — `LiouvilleStage.extend` adjoins
  `tᵢ` with `tᵢ′ = logDeriv uᵢ`, contribute `cᵢ·tᵢ` — or the log is degenerate
  (`logDeriv uᵢ` is already a derivative in the current carrier) — absorb into `v`.
  ★ First check `Engine/LiouvilleLogTower.lean` and the transcendental arc for an
  existing assembly lemma ("the log tower is the built instance" — the arc may already
  have this in some form); re-grep widely before declaring it missing.
  ★ `NondegenerateLog`'s exact definition decides the case split's shape — read it
  first; if it is not literally the negation of "is a derivative", the dichotomy needs
  its own small lemma.
- Instantiate at Phase 2: `denseFrac_exists_antiderivative (f : DenseFrac R) :
  ∃ (S : LiouvilleStage (RatFunc R)) (v : S.carrier),
  algebraMap _ _ (DenseFrac.toRatFunc f) = v′` — "the engine's integral, as an element:
  `D v = f`". The witness `v` is (definitionally traceable to)
  `rational + ∫poly + ∑ a·tₐ` — state a shape lemma only if it falls out; do not force
  constructivity bookkeeping the predicate doesn't need.

**Phase 3 notes (as landed):**
- No existing assembly lemma found — it is new, in `ElementaryTower.lean` (section
  `Assembly`), with the dichotomy lemma `exists_antideriv_of_not_nondegenerateLog` homed
  in `LiouvilleLog.lean` next to `NondegenerateLog`.
- ★ `NondegenerateLog` is NOT the literal negation of "logDeriv u is a derivative" — but
  over char 0 the dichotomy holds: from an annihilated monic irreducible `π` (`Dπ = 0`),
  the top-coefficient relation of `coeff_logDerivPoly` yields
  `s := -(π.coeff (deg−1))/deg` with `s′ = logDeriv u` (the recipe already existed inline
  in `logDerivPoly_ne_zero_of_monic`; extracted).
- The induction is `Finset.cons_induction` with the stage universally quantified in the
  motive (the carrier changes per step). Nondegenerate: `LiouvilleStage.extend` +
  generator `t = algebraMap K[X] (RatFunc K) X` with `t′ = ↑(logDeriv ↑u)` via
  `derivExtends`/`logDerivPoly_X`; degenerate: absorb `↑c·s` into `v`.
- ★ ℤ-diamond again: `Derivation.leibniz` fails on `RatFunc` (its own `Algebra ℤ` beats
  `Ring.toIntAlgebra`); the statement-level `deriv_const_mul` (no ℤ-algebra parameters)
  rewrites cleanly — same family as the Phase-2 `map_add` lesson.
- `ElementaryTower.lean` gained `import DeepWiki.SymbolicIntegration.DifferentialFields`
  (for `deriv_const_mul`).
- The `show`-restatement pattern bridges `(S.extend …).carrier ≡ RatFunc S.carrier` and
  base-stage `carrier ≡ F` defeqs at the `ih`/aux application boundaries.

### Phase 4 (optional / stretch)

- Mathlib-shaped: the log-adjunction differential structure and the assembly lemma are
  close to what memory records Mathlib as lacking for transcendental Liouville — assess
  extracting a PR-sized generic core (`Differential` on `RatFunc F` with prescribed
  `D X`, if the tower layer doesn't already subsume it).
- Catalog: if any step formalizes a citable book item (Bronstein §5.5 corollaries for
  rational functions), add the `Sources/Doi_10_1007_b138171` entries.

## Design constraints

- **Instance discipline**: all `Differential (RatFunc R)` uses must resolve to the same
  (deepWiki global) instance; keep `logSumDeriv`-style pinning at definitions, never at
  statements. If the Liouville layer's instance differs, STOP and reconcile first — do
  not paper over with `@`-pins in theorem statements.
- The Phase 1–2 corollaries consume the landed capstones as-is; no statement changes to
  `lrtLogTerms_sum_sound` / `hermiteReduce_sound`.
- `IsElementary` lives in namespace `DeepWiki.SymbolicIntegration.LiouvilleStructure`;
  the CAlgebra corollaries stay in `DeepWiki.CAlgebra.DensePoly` and `open` it.
- Acceptance per phase: full gate + `#print axioms` on the new capstones
  (`propext`/`Classical.choice`/`Quot.sound` only).
