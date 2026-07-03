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

### M2 — the inner-loop field identity (the per-factor `hstep`) — PENDING
Port `hermiteInner_spec_acc` (HermiteCorrectness:238, a ~60-line induction over the downward counter)
to `cHermiteReduceTowerInnerWf` (FuelFreeDiophantine:220, fuel-free — so induct on `j` directly, no
fuel). At counter `j+1`: extract `(b,c) = cdiophantineGWf (u·Dv) v (-a/(j+1))`, establish the Bézout
relation via `toPolyG_cdiophantineGWf` (carrying the coprimality side-conditions as hypotheses — they
come from Yun, M3), apply M1, and telescope with the accumulator fraction
`g' = (g.1·V^{j+1} + b·g.2, g.2·V^{j+1})`.

Deliverable shape: the per-factor identity `D_tower(⟦gloc⟧) = ⟦a/(u·v^i)⟧ - ⟦a_final/u⟧`, which is
exactly the `hstep` element that `cHermiteReduceTowerG_telescope_seed`
(NormalPartSoundness:175) consumes. Needs first: a `fieldFrac`-add lemma for the `CPolyG × CPolyG`
accumulator (the `toQFun_qadd` analog), then the induction.

### M3 — Yun `cSqfreeYunFFGWf` correctness + multi-factor assembly — PENDING (deepest)
The factor list from `cSqfreeYunFFGWf` must be shown to (a) multiply back to `d`, (b) be pairwise
coprime and squarefree (supplying M2's coprimality side-conditions), (c) have the right multiplicities.
`HermiteCorrectness.lean` has the abstract Yun spine over `ℚ` (ambient instances, `yunFactorizationAbs`,
`sqfreeFactPart`) — a separate, substantial algorithm-correctness proof. This is a genuine
multi-session piece and the deepest of the three.

## Status

- [x] **M1 DONE** (b885089a) — tower single-step Hermite identity.
- [ ] M2 — inner-loop invariant (faithful port of `hermiteInner_spec_acc`; ~80 lines + accumulator
  add-lemma).
- [ ] M3 — Yun correctness + assembly (deepest; separate algorithm).

Once M2+M3 land, `hNrmField` for the reduced part is discharged down to the RT residue-match frontier,
matching the primitive/hyperexp footing (see `risch-typeclass-architecture.md`).
