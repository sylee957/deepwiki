# LRT log-part soundness for the CAlgebra engine

**GOAL**: prove soundness (and the Rothstein–Trager completeness/minimality) for
`lrtLogTerms`/`lrtLogPart` (`DeepWiki/CAlgebra/Integrate/LogPart.lean`) — the analog of the
Hermite ladder (`hermiteReduce_sound` / `_logPart_isProper` / `_complete`), closing the
asymmetry where the log part is only native_decide-validated.

## The head start: the abstract layer already exists (old engine, Layer 0)

Stated on Mathlib `Polynomial`/`RatFunc`, engine-independent, in
`DeepWiki/SymbolicIntegration/`:

- `RationalIntegrationAlgorithms/RothsteinTrager/RtResultant.lean` —
  `rtResultant A D := resultant (D.map C) (A.map C − C X · (D′).map C) (deg D) (deg D − 1)`
  over `(K[X])[X]` (**x outermost over K[t] — the same convention as our
  `DensePoly (DensePoly R)`**), with `rtResultant_eval`.
- `…/LrtSubresultant.lean` — `lrtSubresultant A D j` (determinantal), `lrtSubresultant_eval`
  (specialization commutes), and `lazardRiobooTrager A D : List (K[X] × (K[X])[X])` —
  **shape-identical to our `lrtLogTerms`** (squarefree factors of the resultant, zipIdx,
  drop constant factors, `i = deg D` fallback to the lifted `D`).
- `RationalIntegrationGcdLogForm.lean` — the soundness shape
  `ratFunc_eq_sum_residue_of_isSimilar_gcd`: over split squarefree `D = nodal s`,
  `A/D = Σ_a a · logDeriv (g a)` for ANY `g a` similar to `gcd(D, A − a·D′)` — deliberately
  algorithm-switchable.
- `Residues.lean`, `LrtMonicLogs.lean` — residues = roots of `rtResultant`;
  `lazardRiobooTrager_isSimilar_gcd`, `rootMultiplicity_rtResultant_eq_natDegree_gcd`,
  monic-log regularity.

So the new engine owes only **commuting squares** from its computables into that layer.

## Phases (each gate-green; commit after user review)

1. **Bivariate bridge** (`Poly/Bivariate.lean` + `liftX`/`zC` satellites in
   `Resultant/Primitive.lean`): `toPolynomial₂ : DensePoly (DensePoly R) →
   Polynomial (Polynomial R) := (toPolynomial ·).map equiv`, with injectivity, ring-op
   transport, coeff reading, `natDegree` preservation; `toPolynomial₂ (liftX p) =
   (toPolynomial p).map C`; `toPolynomial₂ zC = C X`.
2. **`rtResultant` square**: `toPolynomial (CAlgebra.rtResultant b d) =
   SymbolicIntegration.rtResultant (toPolynomial b) (toPolynomial d)` — via
   `DensePolyResultant.resultant_eq`, the operand bridge (phase 1 + the 6b
   `toPolynomial_differential` square), resultant-commutes-with-`map` (the old engine's
   `subresultant_map` family), and canonical-degree alignment (needs `deg A < deg D`,
   `D` nonconstant, `CharZero` so the operand degree is exactly `deg D − 1`).
3. **PRS-element similarity square** (the crux): the dispatched sequence's degree-`i`
   element is similar over `K(t)` to `lrtSubresultant A D i`. Route: `DensePolyPRS`'s
   `clean_exact` shows the walk is a classical PRS over `K(t)[x]`; the cataloged
   Fundamental Theorem (`subresultant_prs_telescope`) gives element ∼ determinantal
   subresultant; the z-primitive strip is the Lazard–Rioboo choice surviving
   specialization (`LrtMonicLogs` handles the abstract side).
4. **Lookup correctness**: `find? (·.size = i + 2)` finds the degree-`i` element —
   multiplicity bridge (`rootMultiplicity_rtResultant_eq_natDegree_gcd`) + the walk's
   degree coverage; the `i = deg d` fallback case.
5. **Assembly**: `lrtLogTerms` bridges componentwise to `lazardRiobooTrager` up to
   similarity (needs sqfDecomp ↔ `squarefreeFactorization` agreement — uniqueness of
   squarefree decomposition), then `lrtLogPart_sound` by
   `ratFunc_eq_sum_residue_of_isSimilar_gcd`, hypotheses exactly Hermite's exports
   (`hermiteReduce_logPart_isProper`, `logPart_den_squarefree`).
6. **Completeness/minimality**: the produced constants are exactly the residues
   (`Residues.lean`), i.e. the minimal constant-field extension — the Rothstein–Trager
   second half.

## Status

- Phase 1 DONE (2026-07-21, gate PASS): `Poly/Bivariate.lean` — `toPolynomial₂`
  with coeff reading (`@[simp]`), injectivity, zero/one/add/sub/mul/C transport,
  `natDegree` preservation, `ne_zero`; `toPolynomial₂_liftX` + `toPolynomial₂_zC` beside
  their definitions in `Resultant/Primitive.lean`.
- Phase 2 DONE (2026-07-21): `Integrate/LogPartSound.lean` (leaf; the heavy
  RothsteinTrager import stays off the computable cone) — `toPolynomial_rtResultant`:
  the dispatched bivariate resultant reads through the bridge as the abstract
  `rtResultant`, under `2 ≤ d.size`, `b.size < d.size`, `[CharZero R]`. Support:
  `toPolynomial_resultant₂` (Bivariate.lean, via Mathlib's `resultant_map_map` — MATHLIB
  HAS the map lemma, no port needed) and `natDegree_rtResultant_operand` (beside the
  abstract `rtResultant` def — the canonical-vs-fixed degree alignment; proof: upper bound
  by `natDegree_sub_le`, exactness by the nonzero `t`-linear top coefficient with a
  degree-contradiction instead of numeral coefficient juggling).
- Phase 3 CORE DONE (2026-07-21): `prs_isSimilar_subresultant`
  (LogPartSound.lean) — for a size-ordered entry pair, the `k`-th dispatched sequence
  element (`k ≥ 1`) bridges to a polynomial `IsSimilar` to
  `subresultant (t₂f) (t₂g) (deg t₂f) (deg t₂g) (deg t₂S)`. Route exactly as planned: the
  ℕ-indexed `zChain` view (`zChain_shift` reindexing, `prs_getElem?_eq_zChain`
  correspondence, `prs_ne_zero` aliveness), the bridged chain relation from
  `pseudoDivMod_spec` + `C_zContent_mul_zPrimitive`, hypotheses discharged into
  `subresultant_prs_similar_elt`. New satellites: `zPrimitive_zero`, `zContent_ne_zero`
  (Primitive.lean). ★ Gotcha: omega treats `zChain f g (l+1+1)` and `zChain f g (l+2)` as
  DIFFERENT atoms — normalize indices via type-ascribed `have`s (defeq, so ascription is
  free). REMAINING in phase 3: the `k = 0` base case (element = the entry `g`; needs
  `subresultant A B n m` at `j = m` similar to `B` — check SubresultantSpec for a base
  lemma) — CLOSED same sitting: `prs_mem_isSimilar_subresultant` covers ALL walk elements
  (`k = 0` via the degenerate closed form `subresultant_deg_ge_normal` at `j = deg B`,
  which was already in SubresultantSpec; `k ≥ 1` via the telescope), under a strict
  size-ordered entry.
- Phase 4 CORE DONE (2026-07-21): `prs_covers` — if the `i`-th principal
  subresultant coefficient (psc) of the bridged entry pair is nonzero, the walk CONTAINS an
  element of `x`-degree `i`. Proof: strong induction on `g.size` with a per-step
  found/recurse/vanish trichotomy — found (`i+1 = r.size` or `= g.size`), recurse (psc
  transfers through `subresultant_prs_step`'s coefficient identity), vanish
  (`deg r < i < deg g`: `subresultant_prs_step_gap` zeroes the gap indices,
  `subresultant_prs_step_top` + a low-degree-coefficient argument zeroes the defective-top
  index; terminal `prem = 0` steps use `(C_poly, β) := (0, 1)`). Two reusable
  coefficient-extraction helpers (`hkill`/`hshape`/`hval` — C-scaled step identities with
  low-degree right sides kill the `i`-th coefficient). `find?` glue (Mathlib
  `List.find?_isSome`/`find?_some`/`find?_mem`) folds into the phase-5 assembly.
- Phase 5 DONE (2026-07-21). ★ KEY DISCOVERY: the abstract endpoint
  `lazardRiobooTrager_output_isSimilar_gcd` (LazardRiobooTragerCorrectness.lean) already
  handles BOTH branches (the `i = deg D` fallback and the subresultant branch) specialized
  at ANY residue over `[IsAlgClosed K]` — and its conclusion (similar to the nonzero gcd)
  yields for free both the psc-nonvanishing input `prs_covers` needs AND the specialized
  `S_det(a) ≠ 0` input the specialization lemma needs. DONE so far:
  - 5b `isSimilar_map_eval_of_content_eq_one` (Specialize section; instance-arg
    `[StrongNormalizedGCDMonoid R]`, the old engine's `[GCDMonoid K[X]]`-style pattern —
    generic fields lack the instance, ℚ has it): a `K[t]`-similarity with a content-1 left
    side specializes at every point where the right side survives. Route: content of the
    similarity equation → `Associated c₁ (c₂·content X)` (`content_C_mul` ×2 +
    `content_primPart` + `normalize_eq_normalize_iff_associated`) → `P = C ↑v · primPart X`
    with `v` a unit (= nonzero constant, `Polynomial.isUnit_iff`) → map `evalRingHom a`.
  - 5c primitivity: `dvd_zContent` + `coeff_eq_zContent_mul` + `zContent_zPrimitive_isUnit`
    (Primitive.lean satellites; the unit-content argument via the dispatched-gcd class
    contract) and the bridge `content_toPolynomial₂_zPrimitive` (Mathlib content = 1, via
    `C_dvd_iff_dvd_coeff` + equiv-pullback).
  - 5d DONE (gcd-free form): `prs_elem_isSimilar_lrtSubresultant_eval` — any dispatched
    sequence element, specialized wherever the determinantal `lrtSubresultant` at the
    element's degree survives (hypothesis `hXa`, discharged later from the abstract
    endpoint), is similar to that specialized subresultant. Entry element = the top-index
    subresultant ON THE NOSE (`subresultant_deg_ge_normal` at `j = m = n−1`: both
    exponents 0); later elements via primitivity specialization.
    ★★ INSTANCE LESSON (cost a debugging detour): fields carry
    `StrongNormalizedGCDMonoid` AUTOMATICALLY via
    `CommGroupWithZero.instStrongNormalizedGCDMonoid` — but it needs `[DecidableEq K]`,
    which the abstract layer fills with `Classical.decEq` (its files run classical) while
    our engine binds a REAL `[DecidableEq R]`. The two chains produce NON-DEFEQ `gcd`
    instance terms (`Decidable` is not proof-irrelevant), so any statement of OURS that
    freshly mentions `gcd` cannot unify with the abstract theorems' `gcd` — whnf timeout.
    NEVER add `[StrongNormalizedGCDMonoid R]` as a variable (it duplicates the automatic
    one — a second diamond), and keep engine-side statements gcd-FREE; compose with the
    abstract `gcd` similarity only through terms flowing out of the abstract theorems
    (unification then reuses THEIR instance).
  - 5e-i DONE: the multiplicity bridge `rootMultiplicity_of_sqfDecomp_root` — a root of
    the `j`-th dispatched squarefree-decomposition factor has multiplicity exactly `j+1`
    in the input. Route: `powProdP` staircase mirror + `toPolynomial_powProd` bridge;
    `rootMultiplicity_powProdP` by list induction with the found/not-found split, where
    pairwise coprimality comes from ONE hypothesis `Squarefree L.prod` (via
    `Squarefree.squarefree_of_dvd`, `(X−a)² ∣ prod` contradictions), discharged from the
    class contract (`associated_prod` + `squarefree_sqfreePart` +
    `squarefree_toPolynomial_iff`); `associated_powProd` transports the multiplicity
    (`rootMultiplicity_eq_of_associated`). All with `n = 1` staircase start giving `j+1`.
  - 5e-ii DONE — **THE CAPSTONE**: `lrtLogTerms_isSimilar_gcd` (axiom-clean): over
    `[IsAlgClosed R]` with separable `D` and a proper input, for EVERY pair `(Q, S)` that
    `lrtLogTerms` produces and EVERY root `a` of `Q`, the specialized bridged log argument
    is `IsSimilar` to `rtLogGcd A D a = gcd(D, A − a·D′)`. Proof: membership unpacking
    (filterMap + `List.exists_mem_zipIdx`), the multiplicity readout (5e-i + the resultant
    square + new abstract `rtResultant_ne_zero` from the root-product form), the fallback
    branch via the output-spec's `D`-case, the find?-branch via 5d + coverage
    (`find? = none` is refuted by `prs_covers` fed with the psc-nonvanishing extracted
    from the spec's degree fact). ★★ The instance-mismatch endgame: consume the abstract
    side ONLY through the new bundle `lazardRiobooTrager_output_spec` (in
    LazardRiobooTragerCorrectness.lean), stated against **`rtLogGcd`** — a definition with
    the classical instance BAKED IN — so the engine side never re-elaborates `gcd`; also
    new `rootMultiplicity_rtResultant_le` (abstract) replaces local gcd-degree reasoning.
  - **`lrtLogTerms_sum_sound` DONE (2026-07-21, gate PASS, axiom-clean)** — the summed
    soundness: over `[IsAlgClosed R]`, separable `D`, proper input:
    `A/D = Σ_{a ∈ residues} a · logDeriv (lrtLogArg b d a)` in `RatFunc R`, where
    `lrtLogArg` selects the produced pair covering each residue (and `1` off-residues,
    where the gcd is a nonzero constant — forced by the converse root lemma
    `exists_sqfDecomp_root_of_isRoot`: a positive multiplicity always produces a covering
    pair). Composition pieces all landed:
    (a) `ratFunc_eq_sum_rtLogGcd` (new abstract `RtLogForm.lean`): the NON-MONIC
        switchable log-form — `D = C lc · nodal(roots)`, residue/rtLogGcd invariance under
        the lc-scaling (`gcd_mul_left` + `normalize_eq_one` on the unit `C lc`);
    (b) `image_residue_eq_roots_rtResultant` (residues = rtResultant roots);
    (c) `exists_sqfDecomp_root_of_isRoot` (converse coverage);
    (d) `lrtLogArg` — naming the dite as a DEF was essential: two spellings of the same
        dite carry different invisible `Decidable` witnesses and refuse `rfl`;
    (e) two more instance-diamond potholes: `Multiset.toFinset`/`Finset.image` under
        classical-vs-real `DecidableEq` (bridged by `ext` — membership is instance-free;
        NB `apply Finset.sum_congr` with sequential goals, not `refine … (fun _ _ => rfl)`
        — eager elaboration sees unresolved metavars), and ★ TWO `Differential (RatFunc)`
        instances exist in the repo (old engine's global
        `SymbolicIntegration.instDifferentialRatFunc_deepWiki` vs our scoped
        `FormalDiff.…`) — NOT defeq; the sum statement pins the abstract one explicitly.
        FOLLOW-UP (cleanup): unify the two RatFunc differential instances.
  The original composition plan for reference:
  the abstract log-form `ratFunc_eq_sum_residue_of_isSimilar_gcd` is stated over
  `D = Lagrange.nodal s id` (monic, split, squarefree). The composition needs:
  (a) the monic normalization: for separable `D` over `[IsAlgClosed]`,
      `D = C (lc D) * nodal (D.roots.toFinset) id` and the `A/D` scaling; the
      `gcd(nodal, ·)`-vs-`gcd(D, ·)` constant-invariance — do this IN THE ABSTRACT LAYER
      (classical instances), ideally as a non-monic wrapper of the log-form;
  (b) the residue bridge: `s.image (residue)` ↔ roots of `rtResultant` (Residues.lean has
      the characterization);
  (c) the converse multiplicity lemma (5f): `rootMultiplicity a p = j+1` → `a` roots the
      `j`-th sqfDecomp factor (same staircase argument, reverse direction) — so every
      residue is hit by a produced pair;
  (d) the piecewise family `g a := if a is a residue then (specialized S_a) else 1`
      (non-residues: `gcd` is a nonzero constant, similar to `1`), with the capstone
      discharging the similarity at residues;
  (e) `logDeriv_algebraMap_eq_of_isSimilar` to swap `g` for the gcd inside the sum.
  Then phase 6 (completeness/minimality: the produced `Q`-roots are exactly the residues —
  half of which is already the capstone's multiplicity readout).

## Gotchas / notes

- The abstract layer's bivariate order matches ours exactly (x outermost, coefficients
  K[t]); `liftX ↦ ·.map C`, `zC ↦ C X`.
- Old-engine `lrtSubresultant` fixes bounds `(deg D, deg D − 1)`; our engine computes at
  canonical degrees — alignment needs the operand's exact degree (CharZero argument).
- Import weight: the soundness file may import the determinantal theory
  (`SubresultantSpec`) — keep it a leaf (`Integrate/LogPartSound.lean`-style), NOT on the
  `LogPart.lean` computable path, so the gcd-cone stays light.

## Follow-up

The transport-machinery refactor of `LogPartSound.lean` (bundled denotation hom, single
size measure, `WalkData` bundle, `RtData` instance-boundary API, file split) is planned in
`docs/refactor-lrt-transport.md`.
