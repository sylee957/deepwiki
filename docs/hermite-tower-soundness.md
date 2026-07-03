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

### M3 — the exact-division divisibility + Yun — PENDING (deepest)
The one remaining frontier is the exact-division relation `resDen ∣ resNum·Dstar` for the actual
`cHermiteReduceTowerGWf` output — Hermite's **pole-cancellation guarantee**: after reduction, the
residual `a/d - D(g)` has denominator dividing the squarefree radical `Dstar`. This is where M1/M2 (the
per-factor reduction identities showing each factor's high-multiplicity pole drops) + Yun
`cSqfreeYunFFGWf` correctness (factors multiply to `d`, pairwise coprime/squarefree → `Dstar` structure)
feed in. Note the multiplicity subtlety: the outer fold passes the SAME global `a` and `u = d/vⁱ` to each
factor, so the per-factor sum doesn't naively telescope — the divisibility is genuinely the crux, on the
same footing as the RT residue-match and split-coprimality frontiers. `HermiteCorrectness.lean` has the
abstract Yun spine over `ℚ` (`yunFactorizationAbs`, `sqfreeFactPart`).

## Status

- [x] **M1 DONE** (b885089a) — tower single-step Hermite identity.
- [x] **M2 DONE** (2385ec0e) — inner-loop invariant + `fieldFrac_step_add`.
- [x] **M3-bridge DONE** (f5341c18) — whole-step field identity from exact division
  (`hermiteTowerStep_field_identity`); `hherm` reduced to the exact-division frontier.
- [ ] M3 — the exact-division divisibility `resDen ∣ resNum·Dstar` (Hermite pole-cancellation) + Yun
  `cSqfreeYunFFGWf` correctness (deepest; the genuine remaining crux).

Once M2+M3 land, `hNrmField` for the reduced part is discharged down to the RT residue-match frontier,
matching the primitive/hyperexp footing (see `risch-typeclass-architecture.md`).
