# Hermite tower soundness — plan (discharging the reduced-part `hherm`)

Goal: prove `cHermiteReduceTowerG` correct so the reduced-part field identity `hNrmField`
(`field_identity_of_cIntegrateReducedG_of_residueMatch`, LogPartTowerSoundness) is reduced to
only the Rothstein–Trager residue-match frontier, matching the split/Laurent footing.

Unlike the split frontier (one clean abstract theorem mirroring the computable version), Hermite is a
**composition of three algorithms**: Yun squarefree factorization (`cSqfreeYunFFG`) + per-factor
inner reduction loop (`cHermiteReduceTowerInnerWf`) + multi-factor `foldl` assembly. The abstract
Hermite theorems in `HermiteCorrectness.lean` are over a DIFFERENT model (`CPoly`/`toPoly`/`d/dx`,
fuel-indexed), so they cannot be reused verbatim; they must be **ported** to the tower
(`CPolyG`/`toPolyG`/monomial derivation `D = implicitDeriv (toPolyG Dt)`, fuel-free Wf).

## The three milestones

### M1 — the tower single-step Hermite identity ✓ DONE (b885089a)
`towerFractionFieldDerivG_hermite_step` (`Computable/HermiteTowerStep.lean`). Ports
`hermiteInner_step_ratFunc` — which is `d/dx`-specialized only through `ratFuncDeriv_algebraMap` — to
the tower derivation `towerFractionFieldDerivG Dt`. The polynomial-image bridge is
`towerFractionFieldDerivG_amG` (the `den = 1` case of `towerFractionFieldDerivG_div`). Statement: for
`U, V ≠ 0`, `D = implicitDeriv (toPolyG Dt)`, and the Diophantine relation
`B·(U·DV) + C·V = -A·C((j+1)⁻¹)`,

    amG A / (amG U · amG V^(j+2))
      = D_tower(amG B / amG V^(j+1)) + amG(-(C(j+1))·C - U·DB) / (amG U · amG V^(j+1)).

This is the calculus kernel — the per-step power-drop the inner loop telescopes. **This is the genuine
mathematical content of Hermite reduction; the rest is bookkeeping + Yun.**

Key facts that made it clean (the split playbook again): the abstract identity was already
derivation-generic (`hermite_reduction_step` over any `[Field F] [Differential F]`), and the
Diophantine solver already has its correctness lemma `toPolyG_cdiophantineG`
(`b·p + c·q = rhs`), which supplies M1's `hrel` at each loop step (with `p = u·Dv`, `q = v`,
`rhs = -a/(j+1)`) modulo the coprimality side-conditions `gcd(u·Dv, v)` degree-0 + nonzero.

### M2 — the inner-loop field identity (the per-factor `hstep`) ✓ DONE (2385ec0e)
`cHermiteReduceTowerInnerWf_spec_acc` (`Computable/HermiteTowerStep.lean`). Accumulator-general inner
loop invariant, a faithful port of `hermiteInner_spec_acc` to the fuel-free Wf tower loop
(FuelFreeDiophantine:220 — induct on the counter `j` directly, no fuel):

    ⟦A/(u·v^(j+1))⟧ + D_tower(⟦g⟧)  =  D_tower(⟦result.g⟧) + ⟦result.a/(u·v)⟧.

At counter `j+1`: extract `(B,C) = cdiophantineG (u·Dv) v (-A/(j+1))`, feed the Bézout relation to M1
(`towerFractionFieldDerivG_hermite_step`), telescope via the accumulator fraction-add
`fieldFrac_step_add` (`⟦(g₁·Vpow+B·g₂)/(g₂·Vpow)⟧ = ⟦g₁/g₂⟧ + ⟦B/Vpow⟧`) and the derivation's
`map_add`. Close with `linear_combination hstep + ihA`. GOTCHAS: `map_add` must be `rw`'d on `ihA`
*before* `hA'eq` introduces `Polynomial.C (↑j+1)` (else it splits `C(↑j+1)` into `C↑j + C 1`, which
`ring` treats as a distinct atom); `toK_cnatCastG_oneShot` gives `↑(j+1)` needing `Nat.cast_add_one`
to match M1's `↑j+1`; the Bézout hypothesis is stated in already-mapped polynomial form (M3 discharges
it via `toPolyG_cdiophantineG`, carrying the coprimality side-conditions from Yun).

Specializing `g = (0,1)` (⟦0⟧=0) gives the per-factor identity `D_tower(⟦gloc⟧) = ⟦A/(u·v^(j+1))⟧ −
⟦a_final/(u·v)⟧`, which is exactly the `hstep` element `cHermiteReduceTowerG_telescope_seed`
(NormalPartSoundness:175) consumes.

### M3-bridge — the whole-step field identity from exact division ✓ DONE (f5341c18)
`hermiteTowerStep_field_identity` (`Computable/HermiteTowerStep.lean`). KEY STRUCTURAL INSIGHT: the def
`cHermiteReduceTowerG` computes the residual `hNum/Dstar` **directly** as `a/d - D(g)`
(`resNum/resDen = (a·gden² - d·gp)/(d·gden²)`, `gp` the quotient numerator, `hNum = resNum·Dstar/resDen`).
So the whole-step identity `D_tower(⟦g⟧) + ⟦hNum/Dstar⟧ = ⟦a/d⟧` is a **clean algebraic assembly**
(mirrors `canonicalReconstruction`): quotient rule (`towerFractionFieldDerivG_div`) + the exact-division
relation `⟦hNum⟧·⟦d·gden²⟧ = ⟦resNum⟧·⟦Dstar⟧`, closed by `field_simp`/`ring`. Reduces `hherm` to the
single **exact-division** frontier (carried as the one hypothesis).

### M3-radical — decompose the exact-division into radical + pole-cancellation ✓ DONE (c21504f4)
`hermiteTowerStep_field_identity_of_radical` + the ported pure lemma `dvd_clearedIdentity_of_radical`
(`D=S·W ∧ W·gd2∣R → D·gd2∣R·S`, field-generic). The exact-division `resDen ∣ resNum·Dstar` factors into
two named sub-facts, so the whole-step identity now takes:
- `hSD : d = Dstar·W` — the squarefree radical `Dstar = ∏ᵢ vᵢ` divides `d` with cofactor `W = ∏ᵢ vᵢ^{i-1}`;
- `hWgd : W·gden² ∣ resNum` — Hermite pole-cancellation (the `W`-poles of `a/d − D(g)` cancel).
Tower analog of `hermiteReduce_residual_correct_of_radical`.

### M3 — the two remaining sub-facts — PENDING (deepest; no existing tower theorem)
1. **Yun radical split `d = Dstar·W`** — needs `cSqfreeYunFFG` product correctness `∏ᵢ vᵢ^i = d`.
   `cSqfreeYunFFG` currently has **no** correctness theorem (used only in defs); the abstract ℚ Yun
   spine (`yunFactorizationAbs`, `sqfreeFactPart` in HermiteCorrectness) is not connected to the tower.
2. **Pole-cancellation `W·gden² ∣ resNum`** — the genuine Hermite guarantee. Provable per-factor from
   M1/M2, but with the multiplicity subtlety: the outer fold passes the SAME global `a` and `u = d/vⁱ`
   to each factor's inner loop, so per-factor identities don't naively telescope.

Both are fresh multi-session algorithm-correctness proofs (port the ℚ Yun spine to the tower + the
pole-cancellation assembly), on the same footing as the RT residue-match and split-coprimality frontiers.

## Status

- [x] **M1 DONE** (b885089a) — tower single-step Hermite identity.
- [x] **M2 DONE** (2385ec0e) — inner-loop invariant + `fieldFrac_step_add`.
- [x] **M3-bridge DONE** (f5341c18) — whole-step field identity from exact division
  (`hermiteTowerStep_field_identity`); `hherm` reduced to the exact-division frontier.
- [x] **hherm discharged downstream** (be5c7215) — `field_identity_of_cIntegrateReducedG_of_residueMatch_of_exact`;
  reduced-part soundness needs only exact-division + RT match.
- [x] **M3-radical DONE** (c21504f4) — exact-division split into Yun radical `d=Dstar·W` +
  pole-cancellation `W·gden²∣resNum` (`hermiteTowerStep_field_identity_of_radical`).
- [x] **Yun radical split DONE** (ce9c68e8, `YunTowerCorrect.lean`) — `toPolyG_yunRadical_split`
  discharges `hSD` (`d = Dstar·W`) via `Dstar ∣ d` (a clean go-loop product-divides invariant, no
  `YunInv`/`sqfreeFactPart` needed); reduces to only `GcdFFCorrect` (unconditional at ℚ).
- [ ] M3 — pole-cancellation `W·gden²∣resNum` (the remaining sub-fact; genuinely needs the full Yun
  multiplicity structure + per-factor pole tracking). The abstract engine (`YunInv`,
  `yunStep_emit_assoc`, `yunLoopAbs_forall₂`, `yunFactorizationAbs_prodPow_assoc`) is all present for it.
  **★ EMPIRICALLY CONFIRMED TRUE for m≥2** (native `#eval`, 2026-07-04): the cleared Hermite identity
  holds for `d=t²(t−1)³` (m=2), `d=t³(t−1)²` (m=2), `d=t²(t−1)³(t−2)⁴` (m=3). So the naive-looking
  global-`a`/sum fold IS correct (the per-factor leftovers conspire to a radical-denominator residual) —
  pole-cancellation is a REAL theorem, **not** an `m≤1` limitation; the objective is attainable. The
  proof is a port of the abstract `hermiteReduce_residual_correct_of_radical` to the tower.

## Pole-cancellation — precise proof roadmap (next session)

The abstract pole-cancellation is `prod_dvd_residNum` (HermiteCorrectness:2850): `∏Vk^{ik−1} ∣ R` where
`R = C(1−m)·A + Σ residNumIncr` — **conclusion is purely polynomial** (derivation-independent). Its
structure, and how each hypothesis maps to a tower fact already in hand:

| abstract hypothesis | tower source |
|---|---|
| `hstep` (per-factor `gloc′ = A/D − residNum/D`) | **M2** `cHermiteReduceTowerInnerWf_spec_acc` (have it) |
| `hpw` (kept factors pairwise coprime) | Yun structural — needs multiplicity correspondence |
| `hpow` (`Vk^ik ∣ D`) | Yun structural — needs multiplicity correspondence |
| `hnd` (kept factors nodup) | Yun structural — needs multiplicity correspondence |
| `D = Dstar·W`, `W = ∏Vk^{ik−1}` | **Y4** `toPolyG_yunRadical_split` (radical ∣ d; extend to the exact `W = ∏Vk^{ik−1}` form) |

Two work items:
1. **Generalize** `prod_dvd_residNum` + `dvd_residNum_factor` + `total_fold_residual_over_D` (~200 L of
   `IsQRegular` valuation theory over `RatFunc ℚ` with `d/dx`) to an **arbitrary derivation** on
   `RatFunc K` — the conclusion is polynomial, only the `hstep`/`hdiff` steps touch `′`, so it should
   generalize; this is the bulk.
2. **Yun structural facts** over the tower (kept factors pairwise coprime, `Vk^ik ∣ d`, nodup) — needs
   the `YunInv`/`sqfreeFactPart` **multiplicity correspondence** (extend `YunTowerCorrect.lean`; the
   abstract `yunFactorizationAbs_pairwise_isRelPrime`/`_prodPow_assoc` provide the targets).

Then feed M2 (item hstep) + Y4-extended (radical) + item-2 (structural) into the generalized
`prod_dvd_residNum` to get `W·gden²∣resNum`, discharging `hWgd`.

Once M2+M3 land, `hNrmField` for the reduced part is discharged down to the RT residue-match frontier,
matching the primitive/hyperexp footing (see `bronstein-compositional-architecture.md`).

## Yun side COMPLETE (2026-07-04) — pole-cancellation isolated to one valuation lemma

`YunTowerCorrect.lean` now proves the full multiplicity correspondence and every structural input to
`prod_dvd_residNum`:
- `cSqfreeYunFFG_forall₂` — tower factors `~Forall₂ [sqfreeFactPart A 1, A 2, …]` (via entry `YunInv`
  + `map_toPolyG_cSqfreeYunFFGgoWf_eq` denoting `yunLoopAbs` + the phantom-`A,i` irrelevance).
- `cSqfreeYunFFG_isRelPrime` (`hpw`), `cSqfreeYunFFG_pow_dvd` (`hpow`), radical split (`hSD`), M2
  (`hstep`), zipIdx-nodup (`hnd`) — **all inputs proven**.

The pole-cancellation `W∣R` is now isolated to a **single** deeply derivation-dependent lemma:
`deriv_fold_sub_glocIncr_isQRegular` (the `IsQRegular` valuation of `D(fold − gloc_k)` at `Vk`). The rest
of `dvd_residNum_factor`/`prod_dvd_residNum` (`dvd_num_of_isQRegular`, `list_prod_dvd_of_pairwise`, the
pow-divides addition) is pure polynomial and portable. Remaining: port that one valuation lemma +
`total_fold_residual` (fold-sum of the M2 identities) to the tower derivation, then assemble.

## Valuation core + CAPSTONE COMPLETE (2026-07-04) — pole-cancellation done, 3 frontiers isolated

`HermiteValuationTower.lean` now closes the entire valuation development and the whole-step identity:
- `deriv_fold_sub_isQRegularG` — the deep `IsQRegularG Vk (D⟦g⟧−D⟦gloc_k⟧)` (ported to the tower
  derivation `towerFractionFieldDerivG`).
- `prod_vkidx_dvd_R` — `∏vk^idx ∣ R` (tower `prod_dvd_residNum`), from per-factor `dvd_R_of_factor` +
  `powers_pairwise_coprime`.
- `resNum_eq_R_mul_gden_sq` — `resNum = R·gden²` (field-algebra bridge via `R_residual_identity` +
  the quotient rule + `amG` injectivity).
- `hWgd_of_multiplicity` — the pole-cancellation `W·gden² ∣ resNum`, reduced to `W ∣ ∏vk^idx`.
- **`cHermiteReduceTowerG_field_identity`** (CAPSTONE) — the whole-step
  `D_tower(⟦g⟧) + ⟦hNum/Dstar⟧ = ⟦a/d⟧`, via `hermiteTowerStep_field_identity_of_radical` +
  `toPolyG_yunRadical_split` (hSD) + `hWgd_of_multiplicity` (hWgd).

**The reduced-part (Hermite) soundness of the tower reduction is proven, modulo three clean frontiers**
carried as hypotheses:
1. **`hWdvd`** — `W ∣ ∏kept vk^idx` (the Yun multiplicity-product `W = ∏vk^idx`; the only remaining
   structural fact — assemble from `cSqfreeYunFFG_forall₂` + `primPart_associated_prod_sqfreeFactPart`
   bridging the fold product to the Finset product, with `toPolyG_cHermiteReduceTowerG_Dstar_dvd`).
2. **`hcopgcd`** — per-factor gcd `gcd(u·Dv, v)` deg-0/nonzero (standard Hermite precondition; discharges
   to `v` squarefree + coprime `u`/`v'`).
3. **`hgd0`/`hDstar0`** — fold-denominator nonzero.

Next: discharge `hWdvd` (multiplicity-product), then `hgd0`/`hDstar0`, then wire the capstone into the
LogPart/reduced-part soundness assembly (`field_identity_of_cIntegrateReducedG_of_residueMatch`).

## hWdvd reduced to Yun reconstruction (2026-07-04)

`hWdvd` (`W ∣ ∏vk^idx`) is now discharged from a single clean frontier via `hWdvd_of_reconstruction`
(`HermiteValuationTower.lean`):
- `prodPow_eq_prod_mul_zipIdxPow` (`YunTowerCorrect.lean`) — `prodPow s M = (∏mₖ^s)·∏ₖmₖ^k`.
- `prodPow_one_cSqfreeYunFFG` — `prodPow 1 L = L.prod · FiltProd` (drop-k0 via `prod_map_filter_eq_of_one`).
- radical split `d = Dstar·W`, and `L.prod = toPolyG Dstar`; `Associated.of_mul_left` cancels `Dstar`.

So `hWdvd ← hrecon : Associated (toPolyG d) (prodPow 1 ((cSqfreeYunFFG d).map toPolyG))` — "Yun
factorization reconstructs its input up to associates". The whole pole-cancellation now rests on:
1. **`hrecon`** — Yun reconstruction. Remaining gap: `(cSqfreeYunFFG d).length = maxmult` (loop stops at
   degree 0), then `prodPow 1 (range len).map sqfreeFactPart ~ primPart d ~ d` via
   `deflation_natDegree_eq_zero_iff` + `primPart_associated_prod_sqfreeFactPart` (Finset↔range coverage).
   Abstract analogue: `squarefreeFactorization_forall₂` (length exactly `m`); need the computable
   `cSqfreeYunFFGgoWf` length = `m` bridge.
2. **`hcopgcd`** — per-factor gcd coprimality (standard Hermite precondition).
3. **`hgd0`/`hDstar0`** — fold-denominator nonzero.

## hrecon piece (1) done; piece (2) = loop-length (2026-07-04)

`prodPow_one_sqfreeFactPart_range_associated` (`HermiteCorrectness.lean`) proves the ABSTRACT half:
`prodPow 1 ((range n).map (sqfreeFactPart A ∘ (1+·))) ~ pp(A)` for `n ≥ maxmult` (extra factors are
`sqfreeFactPart = 1`, dropped via `Finset.prod_subset`). Plus reusable `prodPow_append_singleton`,
`prodPow_range_map_eq_finset`.

So `hrecon` now reduces to piece (2): `(cSqfreeYunFFG d).length ≥ maxmult`. Then chain
`prodPow_associated (cSqfreeYunFFG_forall₂)` ~ `prodPow_one_sqfreeFactPart_range_associated` ~
`associated_primPart_self` gives `hrecon`.

KEY OBSERVATION for the finish: the **divides** direction `prodPow 1 (map toPolyG factors) ∣ d` is
FREE — each `vk^(1+k) ∣ d` (`cSqfreeYunFFG_pow_dvd`), pairwise coprime (`cSqfreeYunFFG_isRelPrime`),
so `list_prod_dvd_of_pairwise` applies (mirror `prod_vkidx_dvd_R`). Then `hrecon` (Associated) needs only
`deg(prodPow 1 factors) = deg d`, i.e. `LEN ≥ maxmult` so no multiplicity is dropped — provable either by
the loop-terminates-at-degree-0 analysis (`deflation_natDegree_eq_zero_iff`) or the
divides-plus-degree route.

## hrecon PROVEN — hWdvd frontier ELIMINATED (2026-07-04)

The Yun reconstruction `cSqfreeYunFFG_reconstruction : toPolyG d ~ prodPow 1 (Yun factors)` is now
fully proven (`YunTowerCorrect.lean`):
- `length_cSqfreeYunFFGgoWf_ge` — the go-loop runs `≥ maxmult−(i−1)` steps (fuel induction; working `b`
  is `C c·squarefreePart(deflation (i−1))` so `cdegG b=0 ⟺ maxmult≤i−1`).
- `length_cSqfreeYunFFG_ge` — entry: `maxmult ≤ length` (fuel bound `maxmult ≤ cyunBoundG` via
  `sup_count_le_natDegree_primPart` + `primPart_dvd` + `length_cnormG_of_ne`).
- assembly: `forall₂` through `prodPow_associated` ~ `prodPow_one_sqfreeFactPart_range_associated` ~
  `associated_primPart_self`.

So `hWdvd_of_reconstruction` discharges `hWdvd` unconditionally; `hWgd_of_multiplicity` and
`cHermiteReduceTowerG_field_identity` no longer take it. **The whole-step tower-Hermite field identity
now rests on only TWO frontiers**: `hcopgcd` (per-factor gcd coprimality — a standard Hermite
precondition) and `gden`/`Dstar ≠ 0`.

Remaining: (1) `hcopgcd` — discharge from `v` squarefree + coprime `u`/`v'`, or carry; (2) `gden`/`Dstar
≠ 0`; (3) wire into `field_identity_of_cIntegrateReducedG_of_residueMatch` (the `toPolyG hNum'=.2.1`
exact-division bridge).

## FINAL: capstone rests on ONLY hcopgcd (2026-07-04)

`cHermiteReduceTowerG_field_identity` now takes only `hd0`/`hpp` + `hcopgcd`. Discharged internally:
`gden≠0` (`toPolyG_cHermiteReduceTowerG_den_ne_zero` via `foldl_den_ne_zero` + `hden_of`), `Dstar≠0`
(radical split), `hWdvd` (`cSqfreeYunFFG_reconstruction`). `hcopgcd` is the genuine differential-
NORMALITY side condition (`v` coprime `D(v)`; false for `v=t` under hyperexponential `D`) — a correct
hypothesis matching Bronstein's `hnorm`, not a gap. **The tower-Hermite pole-cancellation soundness is
complete modulo exactly one genuine Bronstein side condition** (+ the unconditional-at-ℚ gcd frontier).

Only bookkeeping remains: wire into `field_identity_of_cIntegrateReducedG_of_residueMatch` (the
`toPolyG hNum' = toPolyG .2.1` exact-division bridge).

## Optional wiring — actionable recipe (2026-07-04)

The capstone `cHermiteReduceTowerG_field_identity` produces the whole-step identity with middle
numerator `hNum'` (radical form: `cdivWf (cmulG resNum' Dstar) resDen`, `resNum'`/`Dstar`/`resDen` in
the *projections* `.1.1/.1.2/.2.2`). The consumer `field_identity_of_cIntegrateReducedG_of_residueMatch`
(LogPartTowerSoundness) needs the middle numerator as `.2.1`. These are `toPolyG`-equal (both exact-div
of `toPolyG`-equal args). The reusable representation-independent bridge
`CPolyEuclidean.toPoly_div_congr` is in place.

Recipe to finish (verified via MCP goal inspection — `.2.1` unfolds to `cnormG(cdivWf (cmulG resNum_int
Dstar_int) resDen_int)` over the internal fold `g = List.foldl (guarded-body) ([0],[1]) zipIdx`, which
is the SAME fold the projections `.1.1=cnormG g.1` etc. denote): prove
`toPolyG (cHermiteReduceTowerG Dt a d).2.1 = toPolyG hNum'` by `conv_rhs/lhs => rw
[cHermiteReduceTowerG]`, `set g := List.foldl … zipIdx` and `set Dstar := List.foldl (·cmulG·) [1] …`
to collapse the many fold occurrences, `simp only [toPolyG_cnormG]`, then
`CPolyEuclidean.toPoly_div_congr` with
`hP`/`hQ` closed by `toPolyG_cmulG/csubG/cmonomialDeriv` normalization and `hdvd1` from the pole-
cancellation (`hWgd_of_multiplicity` transported by `·Dstar` + the radical split `d=Dstar·W`). ~40–80L,
mechanical. Then discharge the consumer `hherm` by rewriting its `.2.1` middle term. Left undone: the
core objective (pole-cancellation) is complete and gate-verified; this only connects it to the
end-to-end reduced-part assembly (which already works modulo `hexact`).

### Wiring cost correction (2026-07-04)

Deeper inspection: `.2.1`'s internal `resNum`/`Dstar`/`resDen` are built from the RAW fold `g`
(`List.foldl … zipIdx`), NOT the `cnormG`'d projections. The pole-cancellation support lemmas
(`hWgd_of_multiplicity`, `toPolyG_cHermiteReduceTowerG_den_ne_zero`, the `hdvd1` divisibility) are all
stated on the projections `.1.2`/`.2.2`. So after unfolding `.2.1` the goal is in raw-fold terms and
cannot directly consume those lemmas — the `hQ1`/`hdvd1` subgoals of
`CPolyEuclidean.toPoly_div_congr` need raw-fold
restatements (or a projection↔rawfold `toPolyG` bridge for each). This makes the wiring ~100L+, not the
~40–80L first estimated. It remains OPTIONAL bookkeeping: the pole-cancellation soundness itself is
complete and gate-verified; this only connects it to the end-to-end assembly, which already works modulo
`hexact`. `CPolyEuclidean.toPoly_div_congr` is in place as the core utility whenever it's picked up.

## WIRING COMPLETE (2026-07-04)

Done — the estimate was wrong, the wiring landed cleanly (~one build cycle) thanks to the right
`CPolyEuclidean.toPoly_div_congr` orientation:
- `toPolyG_hNum'_eq_2_1` (HermiteValuationTower) — the capstone's radical numerator `hNum'` denotes the
  def field `.2.1`. Applied `CPolyEuclidean.toPoly_div_congr` through a private dense-reader adapter,
  with **P1/Q1 = the projection form** (unfolding `.2.1`
  on the RHS to the raw fold), so the nonzero (`hQ1`) and divisibility (`hdvd1`) side-goals stayed
  projection-based and reused `den_ne_zero` + `hWgd_of_multiplicity` (transported by the radical split);
  the symmetric `hP`/`hQ` raw=projection equalities closed by `simp [cHermiteReduceTowerG, toPolyG_*]`.
  The projection-vs-rawfold "complication" dissolved because only `hP`/`hQ` touch raw terms, and those
  need no support lemmas.
- `field_identity_of_cIntegrateReducedG_of_residueMatch_of_hcopgcd` (Assemble) — discharges the
  consumer's `hherm` via the capstone + bridge. **The reduced normal part integrates correctly modulo
  ONLY `hcopgcd` (normality), `hmatch` (caller RT residue match), and `hgcd` (ℚ-unconditional).** The
  `.rational.1 = H.1.1` defeq is accepted as in the sibling `_of_exact`.

The tower-Hermite reduced-part soundness is now fully assembled end-to-end from the pole-cancellation.
