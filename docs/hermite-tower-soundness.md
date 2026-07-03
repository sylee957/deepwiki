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

Once M2+M3 land, `hNrmField` for the reduced part is discharged down to the RT residue-match frontier,
matching the primitive/hyperexp footing (see `risch-typeclass-architecture.md`).
