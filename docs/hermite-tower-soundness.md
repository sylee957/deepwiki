# Hermite tower soundness — plan (discharging the reduced-part `hherm`)

Goal: prove `cHermiteReduceTowerGWf` correct so the reduced-part field identity `hNrmField`
(`field_identity_of_cIntegrateReducedGWf_of_residueMatch`, LogPartTowerSoundness) is reduced to
only the Rothstein–Trager residue-match frontier, matching the split/Laurent footing.

Unlike the split frontier (one clean abstract theorem mirroring the computable version), Hermite is a
**composition of three algorithms**: Yun squarefree factorization (`cSqfreeYunFFGWf`) + per-factor
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
Diophantine solver already has its correctness lemma `toPolyG_cdiophantineGWf`
(`b·p + c·q = rhs`), which supplies M1's `hrel` at each loop step (with `p = u·Dv`, `q = v`,
`rhs = -a/(j+1)`) modulo the coprimality side-conditions `gcd(u·Dv, v)` degree-0 + nonzero.

### M2 — the inner-loop field identity (the per-factor `hstep`) ✓ DONE (2385ec0e)
`cHermiteReduceTowerInnerWf_spec_acc` (`Computable/HermiteTowerStep.lean`). Accumulator-general inner
loop invariant, a faithful port of `hermiteInner_spec_acc` to the fuel-free Wf tower loop
(FuelFreeDiophantine:220 — induct on the counter `j` directly, no fuel):

    ⟦A/(u·v^(j+1))⟧ + D_tower(⟦g⟧)  =  D_tower(⟦result.g⟧) + ⟦result.a/(u·v)⟧.

At counter `j+1`: extract `(B,C) = cdiophantineGWf (u·Dv) v (-A/(j+1))`, feed the Bézout relation to M1
(`towerFractionFieldDerivG_hermite_step`), telescope via the accumulator fraction-add
`fieldFrac_step_add` (`⟦(g₁·Vpow+B·g₂)/(g₂·Vpow)⟧ = ⟦g₁/g₂⟧ + ⟦B/Vpow⟧`) and the derivation's
`map_add`. Close with `linear_combination hstep + ihA`. GOTCHAS: `map_add` must be `rw`'d on `ihA`
*before* `hA'eq` introduces `Polynomial.C (↑j+1)` (else it splits `C(↑j+1)` into `C↑j + C 1`, which
`ring` treats as a distinct atom); `toK_cnatCastG_oneShot` gives `↑(j+1)` needing `Nat.cast_add_one`
to match M1's `↑j+1`; the Bézout hypothesis is stated in already-mapped polynomial form (M3 discharges
it via `toPolyG_cdiophantineGWf`, carrying the coprimality side-conditions from Yun).

Specializing `g = (0,1)` (⟦0⟧=0) gives the per-factor identity `D_tower(⟦gloc⟧) = ⟦A/(u·v^(j+1))⟧ −
⟦a_final/(u·v)⟧`, which is exactly the `hstep` element `cHermiteReduceTowerG_telescope_seed`
(NormalPartSoundness:175) consumes.

### M3-bridge — the whole-step field identity from exact division ✓ DONE (f5341c18)
`hermiteTowerStep_field_identity` (`Computable/HermiteTowerStep.lean`). KEY STRUCTURAL INSIGHT: the def
`cHermiteReduceTowerGWf` computes the residual `hNum/Dstar` **directly** as `a/d - D(g)`
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
1. **Yun radical split `d = Dstar·W`** — needs `cSqfreeYunFFGWf` product correctness `∏ᵢ vᵢ^i = d`.
   `cSqfreeYunFFGWf` currently has **no** correctness theorem (used only in defs); the abstract ℚ Yun
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
- [x] **hherm discharged downstream** (be5c7215) — `field_identity_of_cIntegrateReducedGWf_of_residueMatch_of_exact`;
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
matching the primitive/hyperexp footing (see `risch-typeclass-architecture.md`).

## Yun side COMPLETE (2026-07-04) — pole-cancellation isolated to one valuation lemma

`YunTowerCorrect.lean` now proves the full multiplicity correspondence and every structural input to
`prod_dvd_residNum`:
- `cSqfreeYunFFGWf_forall₂` — tower factors `~Forall₂ [sqfreeFactPart A 1, A 2, …]` (via entry `YunInv`
  + `map_toPolyG_cSqfreeYunFFGgoWf_eq` denoting `yunLoopAbs` + the phantom-`A,i` irrelevance).
- `cSqfreeYunFFGWf_isRelPrime` (`hpw`), `cSqfreeYunFFGWf_pow_dvd` (`hpow`), radical split (`hSD`), M2
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
- **`cHermiteReduceTowerGWf_field_identity`** (CAPSTONE) — the whole-step
  `D_tower(⟦g⟧) + ⟦hNum/Dstar⟧ = ⟦a/d⟧`, via `hermiteTowerStep_field_identity_of_radical` +
  `toPolyG_yunRadical_split` (hSD) + `hWgd_of_multiplicity` (hWgd).

**The reduced-part (Hermite) soundness of the tower reduction is proven, modulo three clean frontiers**
carried as hypotheses:
1. **`hWdvd`** — `W ∣ ∏kept vk^idx` (the Yun multiplicity-product `W = ∏vk^idx`; the only remaining
   structural fact — assemble from `cSqfreeYunFFGWf_forall₂` + `primPart_associated_prod_sqfreeFactPart`
   bridging the fold product to the Finset product, with `toPolyG_cHermiteReduceTowerGWf_Dstar_dvd`).
2. **`hcopgcd`** — per-factor gcd `gcd(u·Dv, v)` deg-0/nonzero (standard Hermite precondition; discharges
   to `v` squarefree + coprime `u`/`v'`).
3. **`hgd0`/`hDstar0`** — fold-denominator nonzero.

Next: discharge `hWdvd` (multiplicity-product), then `hgd0`/`hDstar0`, then wire the capstone into the
LogPart/reduced-part soundness assembly (`field_identity_of_cIntegrateReducedGWf_of_residueMatch`).

## hWdvd reduced to Yun reconstruction (2026-07-04)

`hWdvd` (`W ∣ ∏vk^idx`) is now discharged from a single clean frontier via `hWdvd_of_reconstruction`
(`HermiteValuationTower.lean`):
- `prodPow_eq_prod_mul_zipIdxPow` (`YunTowerCorrect.lean`) — `prodPow s M = (∏mₖ^s)·∏ₖmₖ^k`.
- `prodPow_one_cSqfreeYunFFGWf` — `prodPow 1 L = L.prod · FiltProd` (drop-k0 via `prod_map_filter_eq_of_one`).
- radical split `d = Dstar·W`, and `L.prod = toPolyG Dstar`; `Associated.of_mul_left` cancels `Dstar`.

So `hWdvd ← hrecon : Associated (toPolyG d) (prodPow 1 ((cSqfreeYunFFGWf d).map toPolyG))` — "Yun
factorization reconstructs its input up to associates". The whole pole-cancellation now rests on:
1. **`hrecon`** — Yun reconstruction. Remaining gap: `(cSqfreeYunFFGWf d).length = maxmult` (loop stops at
   degree 0), then `prodPow 1 (range len).map sqfreeFactPart ~ primPart d ~ d` via
   `deflation_natDegree_eq_zero_iff` + `primPart_associated_prod_sqfreeFactPart` (Finset↔range coverage).
   Abstract analogue: `squarefreeFactorization_forall₂` (length exactly `m`); need the computable
   `cSqfreeYunFFGgoWf` length = `m` bridge.
2. **`hcopgcd`** — per-factor gcd coprimality (standard Hermite precondition).
3. **`hgd0`/`hDstar0`** — fold-denominator nonzero.
