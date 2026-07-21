# Refactor: the LRT transport machinery

**GOAL**: `DeepWiki/CAlgebra/Integrate/LogPartSound.lean` (~1300 lines, landed `3b0341ac`)
proves the right theorems but is transport-dominated — the mathematics is roughly a third;
the rest is per-theorem bridging plumbing. Restructure it into a cubical (commuting-square)
discipline: bundled denotations, one measure, one walk bundle, one instance-boundary API.
The theorem *statements* (`lrtLogTerms_isSimilar_gcd`, `lrtLogTerms_sum_sound`,
`hermiteReduce_logPart_sum_sound`, and the square/coverage lemmas) survive verbatim — this
is proof- and file-structure work only.

## Diagnosis (why it reads messy)

1. **Unbundled denotation.** `toPolynomial₂` is a plain def, so every ring-op transport is
   a bespoke satellite (`toPolynomial₂_mul/_add/_sub/_C/…`) and every equation crosses the
   bridge via a hand-rolled `congrArg toPolynomial₂ … simpa only […]` block.
2. **Mixed measures.** Three measures of one object circulate — `size`,
   `(toPolynomial ·).natDegree`, `(toPolynomial₂ ·).natDegree` — converted at every use
   site (`rw [toPolynomial₂_natDegree, natDegree_toPolynomial_eq_size_sub_one]` ×~15).
   This caused the omega atom-mismatch bugs (`l+1+1` vs `l+2` inside `zChain`) and most of
   the `have h1/h2 …; omega` noise.
3. **Copy-pasted walk plumbing.** `prs_isSimilar_subresultant` and `prs_covers` each
   rebuild the same bundle from scratch: aliveness (`hidx`), per-step size drop
   (`hstep_size`), the monotone size chain (`hmono`), entry ordering (`hord`), and the
   bridged chain relation (`hrel`).
4. **Ad-hoc instance boundary.** The classical-vs-real `DecidableEq` divide (see
   `docs/lrt-soundness-calgebra.md`, gotchas) is patched at five separate places:
   `rtLogGcd`-pinning, the `lazardRiobooTrager_output_spec` bundle,
   `rootMultiplicity_rtResultant_le` relocation, the `toFinset`/`image` membership-`ext`
   transport, and the explicit `@Differential.logDeriv …` instance pin.

## Phases (each gate-green; commit after review)

### Phase 1 — bundle the denotation (`Poly/Bivariate.lean`) — DONE (2026-07-21)

- `noncomputable def toPolynomial₂Hom : DensePoly (DensePoly R) →+* Polynomial (Polynomial R)`
  := `(Polynomial.mapRingHom (equiv (R := R)).toRingHom).comp (equiv (R := DensePoly R)).toRingHom`,
  with `@[simp] toPolynomial₂Hom_apply : toPolynomial₂Hom p = toPolynomial₂ p`.
  Then `map_mul/map_sub/map_pow/map_dvd/map_list_prod` etc. come for free; retire the
  bespoke `toPolynomial₂_mul/_add/_sub/_one/_zero` satellites gradually (keep `_C`,
  `_coeff`, `_natDegree`, injectivity — genuinely non-hom facts).
- ~~Named simp set~~ (user decision: no custom attributes/macros yet) — bridge steps
  list their lemmas explicitly in `simp only [...]`; the reusable vocabulary is
  `map_*` + `toPolynomial₂Hom_apply` + `toPolynomial₂_coeff/_C` + the bridges
  (`toPolynomial₂_liftX`, `toPolynomial₂_zC`, `toPolynomial_deriv`) + the boundary
  composite `natDegree₂_eq_size_sub_one`.
- Rewrite the existing `congrArg`-blocks (`hrel` in the chain lemmas, `hid`, `hprembr`,
  the `toPolynomial_pseudoDivMod`-map step) through the hom + simp set.

### Phase 2 — one measure at the engine boundary — DONE (2026-07-21)

- Convention: **engine-side lemmas speak `size` only.** The abstract boundary converts
  once via exactly two lemmas (already exist):
  `natDegree_toPolynomial_eq_size_sub_one` and `toPolynomial₂_natDegree`.
- Use the composite `natDegree₂_eq_size_sub_one : (toPolynomial₂ p).natDegree = p.size - 1`
  (landed in Phase 1) so no proof ever chains the two manually.
- Restate the operand/liftX satellites in size form (`liftX_size`, `operand_size`,
  already exist) and make the degree forms (`liftX_natDegree₂`, `operand_natDegree₂`)
  one-line corollaries — not the other way around.
- Sweep `LogPartSound` proofs: replace each `rw [toPolynomial₂_natDegree,
  natDegree_toPolynomial_eq_size_sub_one] … omega` dance with the composite lemma; keep
  omega's atoms uniform (all `size`).

**Phase 2 notes (as landed):**
- Satellite block inverted to size-primary: `liftX_ne_zero`, hypothesis-free
  `liftX_size (d) : (liftX d).size = d.size` (zero case is `rfl`), `operand_ne_zero`,
  `operand_size` are the primary facts; `liftX_natDegree₂` / `operand_natDegree₂` /
  `operand_ne_zero₂` are one-line corollaries via `natDegree₂_eq_size_sub_one`.
- 13 chained-conversion sites in `LogPartSound` replaced with the composite; the
  endpoint (`prs_elem_isSimilar_lrtSubresultant_eval`) no longer re-derives
  `hlxsize`/`hopsize`/`hopne` inline — they are direct satellite calls (5 `have`-blocks
  → 3 one-liners).
- Remaining `natDegree_toPolynomial_eq_size_sub_one` uses are the sanctioned *single*
  univariate boundary conversions (`toPolynomial`-level, not the two-lemma dance).

### Phase 3 — the walk bundle (`Integrate/LogPartChain.lean`, split out)

- New file holding the chain view: `zStep`, `zChain`, `prs_z_eq`,
  `prs_getElem?_eq_zChain`, `prs_ne_zero`, `prs_shape_mem`.
- New structure:
  ```
  structure WalkData (f g : DensePoly (DensePoly R)) (k : ℕ) where
    alive     : ∀ j ≤ k, zChain f g (j+1) ≠ 0
    step_size : ∀ l ≤ k, (zChain f g (l+2)).size < (zChain f g (l+1)).size
    mono      : ∀ dlt l, l + dlt ≤ k → (zChain f g (l+dlt+1)).size ≤ (zChain f g (l+1)).size
    ord       : ∀ l ≤ k, (zChain f g (l+1)).size ≤ (zChain f g l).size
    rel       : ∀ l ≤ k-1, C (α l) * F l = C (β l) * F (l+2) + F (l+1) * Q l   -- bridged
  ```
  (α/β/F/Q as the file's current definitions, promoted from proof-local `set`s to
  private defs parameterized by `f g`.) One constructor
  `WalkData.ofGetElem? : (prs f g)[k]? = some S → g.size ≤ f.size → WalkData f g k`.
- `prs_isSimilar_subresultant` and `prs_covers` destructure the bundle; their bodies
  shrink to the genuinely mathematical case analyses (telescope application; the
  found/recurse/vanish trichotomy).

### Phase 4 — the abstract instance-boundary API (`RothsteinTrager/RtData.lean`)

- One record produced under `open scoped Classical`, consumed by the engine:
  ```
  structure RtData (A D : K[X]) (a : K) where
    gcdVal        : K[X]                       -- := rtLogGcd A D a (the baked instance)
    ne_zero       : gcdVal ≠ 0
    natDegree_eq  : gcdVal.natDegree = (rtResultant A D).rootMultiplicity a
    output_sim    : IsSimilar ((branch …).map (evalRingHom a)) gcdVal
  theorem rtData [IsAlgClosed K] (hD : D.Separable) (hA : …) (a) : RtData A D a
  ```
  subsuming `lazardRiobooTrager_output_spec` + `rootMultiplicity_rtResultant_le` (the
  bound becomes `natDegree_eq ▸ natDegree_le_of_dvd`-free: export it as a field or a
  record satellite). Rule of thumb, now API: **the engine never elaborates `gcd`,
  `toFinset`, `Finset.image`, or `logDeriv` against abstract-layer terms** — it consumes
  record fields; set-level index transports stay membership-`ext` one-liners.
- Move `isSimilar_map_eval_of_content_eq_one` to the abstract layer (engine-independent
  `K[t][x]` content math; natural home near `IsSimilar` in `Algebra/PseudoDivision.lean`
  or a sibling `Algebra/SimilaritySpecialize.lean`).
- Move `entry_subresultant_eq_lrt` + the operand satellites
  (`operand_bridge`, `operand_natDegree₂`, `operand_ne_zero₂`, `operand_size`,
  `liftX_size`) next to `liftX`/`zC` in `Resultant/Primitive.lean` (satellites live with
  their definitions).

### Phase 5 — file split + capstone re-plumb

- `Integrate/LogPartSound.lean` retains: the resultant square, the specialization lemma
  application, `prs_elem_isSimilar_lrtSubresultant_eval`, the multiplicity bridge
  (`powProdP` block — or split further to `Integrate/LogPartMultiplicity.lean` if it
  crowds), `lrtLogArg`, and the three capstones — each now a short braid of bundle
  destructurings.
- Re-verify: full gate + `lean_verify` axiom checks on the three capstones (must stay
  `propext`/`Classical.choice`/`Quot.sound`).

### Phase 6 (separate arcs, not this refactor)

- **Unify the two `Differential (RatFunc)` instances** (old engine global
  `SymbolicIntegration.instDifferentialRatFunc_deepWiki` vs our scoped
  `FormalDiff.…` — not defeq; the sum statements pin the old one explicitly). Probably:
  redefine the `FormalDiff` scoped one as the old instance (or delete it and re-export),
  then drop the `@`-pins.
- **Refine-kernel experiment**: `LogPartSound` is transport-dominated — the best test
  case yet for `DeepWiki/Refine` (relation = graph of `toPolynomial₂`, parametricity
  instances per op, squares generated by the transfer tactic). Blocked on the kernel's
  MetaM resolver (see `docs/refine-transfer-kernel.md`).

### Phase 1 notes (as landed)

- No custom simp attribute (user decision — no macro machinery yet); simp calls list the
  bridge lemmas explicitly. (If ever revisited: `register_simp_attr` must live in its own
  module — an attribute is not usable in its defining file.)
- `natDegree₂_eq_size_sub_one` (the Phase-2 boundary composite) added early, untagged.
- The ring-op satellites (`_zero/_one/_add/_sub/_mul`) kept their names/statements but are
  now `map_*` one-liners over `toPolynomial₂Hom`.
- All four congrArg blocks rewired; `hid` now maps the DensePoly-level `pseudoDivMod_spec`
  through the hom directly (the old outer-`toPolynomial`-then-`Polynomial.map` dance is
  gone). Gotcha: `simpa`'s closing match uses reducible transparency — when the last step
  must see through projections (`pseudoDiv` = `(pseudoDivMod ·).1`), use
  `simp only [...] at h; exact h` instead.

## Invariants for the refactor

- No statement changes to the landed theorems; downstream users (none yet beyond the file
  itself) unaffected.
- Values untouched (proof-only); the gate plus the three axiom checks are the acceptance
  bar per phase.
- The instance-mismatch lessons in `docs/lrt-soundness-calgebra.md` are the design
  constraints for Phase 4 — do not reintroduce fresh abstract-term elaborations
  engine-side.
