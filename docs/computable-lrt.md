# Computable Lazard–Rioboo–Trager (symbolic-residue reduced integration)

**Goal.** Close the last `PrimitiveFrontier` field `hreduced` *without root-finding*, by giving the reduced
integrator a **symbolic** residue-log part (LRT): the log arguments are computed over `K` via subresultants,
never by enumerating the residues. This handles *all* residues (rational **and** algebraic) and removes the
`candidates`/pole-finding dependency for correctness.

## The asset: the abstract LRT theory is already proven

`DeepWiki/SymbolicIntegration/` (Mathlib layer) has the full stack:
- `LazardRiobooTragerCorrectness.lazardRiobooTrager_output_isSimilar_gcd` — LRT output is similar to the RT
  gcd, over `[IsAlgClosed K]` (all residues symbolic).
- `RationalIntegrationGcdLogForm.ratFunc_eq_sum_residue_gcd` — `A/D = Σ_{β∈s} (A(β)/D'(β))·(D'/(t−β))` residue
  identity (the split-denominator RT sum).
- `Subresultants` (Sylvester-det subresultants + `subresultant_map`/`_C_mul`), `SubresultantPRS`
  (`subresultant_eq_pseudoRem`, `subresultant_prs_closed_top`, `subresultant_isSimilar_gcd`),
  `RiobooCoprimality`, `RtResultantCorrectness`.

So the **mathematics is done**. The gap is a *computable* integrator whose output the abstract theory
certifies.

## The gap and the plan

The engine's reduced integrator (`cLogPartGWf`) uses an explicit rational-candidate list; there is **no
computable subresultant / LRT integrator**. The pattern to reuse: `cResidueResultantTowerGWf` computes the
residue resultant `R(z)` by **interpolation in `z`** (evaluate `cresultantWf` at `z=0,1,…,deg` and
`cinterpolateG`) — avoiding bivariate polynomials. The LRT log-arguments admit the same treatment.

**Status (2026-07-04): L1–L3 DONE and `native_decide`-validated** — the computable root-free LRT integrator
is built. `∫1/(t²−1)` over `ℚ(t)` yields the symbolic log part `[(z²−1/4, S₁)]` with `S₁(z,t)=1−2z·t`
(residues `±1/2` stay implicit as roots of `z²−1/4`; `S₁` at each residue is the actual log argument). L4 (the
abstract correctness bridge) and L5 (swap the primitive base) remain.

Phases (each its own gate-green commit):

- **L1 — computable subresultant `cSubresultantG p q j`** over `CPolyG α`: the `j`-th subresultant
  *polynomial* of `p,q`, with `toPolyG_cSubresultantG` = the abstract `subresultant` (via the Sylvester det
  `subresultant_eq_det_polyCol`). **Foundation available:** the fraction-free **Bareiss engine**
  (`Computable/Algebraic/BareissEngine.lean`, `qfClearMatrix`) computes the det; the subresultant is a det
  with one polynomial column (expand along it → `Σ (poly entry)·(scalar cofactor det)`).
- **L2 — the parametric log-argument `cLrtLogArgG Dt hNum Dstar`**: for each squarefree factor `Rᵢ` of the
  residue resultant `R(z)` (degree `i`), the degree-`i` subresultant `Sᵢ(z,t)` of `Dstar` and
  `hNum − z·D(Dstar)`, computed by **interpolation in `z`** (evaluate `cSubresultantG` at `z=0,1,…` per
  `t`-coefficient). Output: a list `[(Rᵢ, Sᵢ(z,t))]` over `K`, no roots.
- **L3 — the LRT reduced integrator `cIntegrateReducedLrtG`**: Hermite rational part (reuse
  `cHermiteReduceTowerGWf`) + `cLrtLogArgG` symbolic log part. `IntegralResultG` with logs keyed by the
  `(Rᵢ, Sᵢ)` pairs (a symbolic-residue `logs` variant).
- **L4 — correctness bridge**: `IsIntegralResultG Dt cn dn (cIntegrateReducedLrtG …)` from
  `lazardRiobooTrager_output_isSimilar_gcd` + `ratFunc_eq_sum_residue_gcd`, discharging the residue match
  *without* `hden`/`hres`/pole-finding. This closes `hreduced` for a new `RischTowerPrimitiveLrt` instance.
- **L5 — swap the primitive base** to the LRT integrator; `PrimitiveFrontier` becomes hypothesis-free
  (only the shared `[Fact (GcdFFCorrect α)]` + `[CharZero]`), completing the sound primitive solver.

## Honest scope

L1 is the foundational brick. L2–L4 are the substance (the symbolic log part + its correctness), reusing the
already-proven abstract LRT — which removes the hardest mathematics but is still a real algorithm+bridge
build. This is the genuine path to a root-finding-free `hreduced`.
