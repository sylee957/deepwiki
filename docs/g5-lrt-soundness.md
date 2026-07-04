# G5 — full-algebraic symbolic-log soundness for `cIntegrateReducedLrtG`

**Goal (user-chosen, 2026-07-04).** Prove `IsIntegralResultLrtG` for the root-free LRT reduced integrator
`cIntegrateReducedLrtG` handling **all** residues (roots of `Rᵢ` in the algebraic closure), which removes the
rational-residue restriction and closes `hreduced` via the root-free route. This is the analytic heart of
Bronstein Thm 5.6.1 over the tower — research-level, executed in passes. All *algebraic* prerequisites
(G1–G4c) are DONE and gate-clean.

## The target and what's already reusable

The reduced soundness is `IsIntegralResultG Dt a d res := towerFractionFieldDerivG Dt (rational) +
logResidueSumG Dt res.logs = a/d`. The candidate route factors it (`field_identity_of_reducedG_of_residueMatch`,
`LogPartTowerSoundness.lean`) into:
- **`hherm`** — the Hermite half `D(g) + hNum/Dstar = a/d`. **`cIntegrateReducedLrtG` shares the *same*
  Hermite part** (`cHermiteReduceTowerGWf`), so `hherm` transfers verbatim from the existing capstone.
- **`hmatch`** — the residue-log-derivative sum equals `hNum/Dstar`. **This is the only gap.**

For the *enumerated* case (residues in a `Finset s ⊂ K`, `Dstar = Lagrange.nodal s id` splits over `K`),
`hmatch` is DONE (`cIntegrateReducedGWf_logs_eq_per_root` + `ratFunc_eq_sum_residue_gcd`). The LRT route's
`hmatch` sums over the roots of `Rᵢ` in `K̄` — the algebraic-closure residue sum.

## Strategy: base-change to `K̄` + injectivity descent (avoids full Galois descent)

Let `K = CFieldSpec.K α`, `K̄ = AlgebraicClosure K`. `RatFunc K ↪ RatFunc K̄` (base change) is a *ring-hom
that intertwines the tower derivation* and is **injective**. Plan:

1. **State soundness over `K̄`.** Over `K̄`, `Dstar` splits: `toPolyG Dstar` (mapped to `K̄`) `= ∏(t − βⱼ)`,
   roots `βⱼ ∈ K̄`. The residues are `Rᵢ`'s roots in `K̄`. Define the symbolic-log denotation
   `logResidueSumLrtG` as the honest `K̄`-sum `Σᵢ Σ_{Rᵢ(c)=0 in K̄} c · logDeriv(Sᵢ(c,t))` where `Sᵢ(c,t) =
   Σₖ (eval₂ (algebraMap K K̄) c (toPolyG Sᵢ[k])) tᵏ`.
2. **Prove the `K̄`-`hmatch` by reusing the tower machinery over `K̄`.** Over `K̄` everything splits, so the
   enumerated `cIntegrateReducedGWf_logs_eq_per_root`-style argument applies with `s = (toPolyG Dstar).roots
   in K̄`. The bridges are the DONE pieces:
   - `Rᵢ`'s roots `= ` the residues, grouped by multiplicity `i` (via G4b `toPolyG_cResidueResultantTowerGWf`
     = `rtResultantGen`, whose roots are the residues by G2 `roots_rtResultantGen`; `cSqfreeYunFFGWf`
     multiplicity `↔` `rootMultiplicity`).
   - `Sᵢ(c,t) ~ gcd(Dstar, hNum − c·B)` at a residue `c` (via G4c `toPolyG_cSubresultantParam_getD`
     = `lrtSubresultantGen` coeff, then G3 `lazardRiobooTrager_output_isSimilar_gcd_gen`:
     `lrtSubresultantGen.map (evalRingHom c) ~ gcd`).
   - `Σ_c c·logDeriv(gcd) = hNum/Dstar` (the analytic identity) — the general-derivation / `K̄` analog of
     `ratFunc_eq_sum_residue_gcd`, using the tower `logResidueSumG_eq_of_residue_match` differential content.
3. **Descend to `K`.** The Hermite/rational side and `hNum/Dstar` are base-changes of `K`-objects. The
   `K̄`-identity `D_K̄(g) + logResidueSumLrtG_K̄ = (a/d)_K̄`, precomposed with the injective base change,
   gives the `K`-statement `IsIntegralResultLrtG Dt a d (cIntegrateReducedLrtG …)` — because the log sum,
   being symmetric in the roots of each `Rᵢ` (an integer-coefficient symmetric function of the residues), is
   itself the base change of a `K`-rational function (or: prove the `K̄`-identity and note both sides descend).

## Pass breakdown (each its own gate-green commit)

- **P1 — the `K̄` denotation + `IsIntegralResultLrtG` definition.** `logResidueSumLrtG` (the `K̄` root-sum),
  `IsIntegralResultLrtG Dt anum aden (res : LrtResultG α)` (`towerFractionFieldDerivG` on `res.rational` +
  the `K̄` log sum `= anum/aden`, stated so it descends). Gate-green definitions.
- **P2 — the residue↔root grouping.** `Rᵢ`'s roots in `K̄` are the residues of multiplicity `i`
  (`cSqfreeYunFFGWf` mult ↔ `rootMultiplicity` of `rtResultantGen`, via G4b + G2). Reuse
  `cResidueResultantTowerGWf` = `rtResultantGen`.
- **P3 — `Sᵢ` at a residue = the RT gcd.** `toPolyG_cSubresultantParam_getD` (G4c) + `lazardRiobooTrager_
  output_isSimilar_gcd_gen` (G3), specialised at each root `c` of `Rᵢ`; the normality `hB` from
  `isCoprime_X_sub_C_implicitDeriv_iff` (the genuine `hcopgcd`).
- **P4 — the `K̄` analytic identity** `Σ_c c·logDeriv(gcd) = hNum/Dstar`: the general-derivation `K̄` analog
  of `ratFunc_eq_sum_residue_gcd`, reusing the tower `logResidueSumG_eq_of_residue_match`. The genuinely-new
  analytic content (Bronstein 5.6.1's simple-pole partial fraction over the tower).
- **P5 — descent + assembly.** Base-change injectivity `RatFunc K ↪ RatFunc K̄` intertwining the derivation;
  assemble P2–P4 into the `K̄`-`hmatch`; combine with the transferred `hherm` via
  `field_identity_of_reducedG_of_residueMatch`; descend to `IsIntegralResultLrtG` over `K`. Then swap the
  primitive base to `cIntegrateReducedLrtG` ⟹ `hreduced` closed WITHOUT the rational-residue restriction.

## Honest scope

P1–P3, P5-assembly are engineering over DONE pieces. **P4 is the genuine new mathematics** (the tower
simple-pole partial-fraction / residue identity over `K̄`), and the descent (P5) needs the base-change-
intertwines-derivation lemma. This is the multi-pass frontier the user chose; everything it stands on is
proven.
