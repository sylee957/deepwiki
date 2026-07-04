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

- **P1 — the denotation + `IsIntegralResultLrtG` definition.** Design determined (2026-07-04): **don't build
  a `Differential (AlgebraicClosure K)` instance** (only `existsUnique_differentialAlgebra_intermediateField`
  exists). Instead **parameterize over a differential extension `E`** — `extendDerivFun`/`extendDeriv`
  (`FractionFieldDeriv.lean`) are already generic over any field with a base `Derivation ℤ E[X] E[X]`, and
  `Differential.implicitDeriv ((toPolyG Dt).map (algebraMap K E))` is the `E`-tower derivation on `E[X]` (needs
  only `[Differential E]`). Exact turn-key definitions:
  ```
  -- `Sᵢ` (z-poly per t-power) evaluated at a residue `c ∈ E`: the E[t] poly `Σₖ (Sᵢ[k] at z=c)·tᵏ`
  noncomputable def evalLrtArg {E} [Field E] [Algebra (CFieldSpec.K α) E]
      (Si : List (CPolyG α)) (c : E) : E[X] :=
    (Si.zipIdx.map (fun p => C ((toPolyG p.1).eval₂ (algebraMap (CFieldSpec.K α) E) c) * X ^ p.2)).sum
  -- E-tower derivation on RatFunc E
  noncomputable def towerDerivExt {E} [Field E] [Algebra (CFieldSpec.K α) E] [Differential E]
      (Dt : CPolyG α) : Derivation ℤ (RatFunc E) (RatFunc E) :=
    extendDeriv (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E)))
  -- algebraic residue sum over E: Σᵢ Σ_{c ∈ roots(Rᵢ in E)} c·(Δ Sᵢ(c,t))/Sᵢ(c,t)
  noncomputable def logResidueSumLrtG {E} [Field E] [Algebra (CFieldSpec.K α) E] [Differential E]
      (Dt : CPolyG α) (logs : List (CPolyG α × List (CPolyG α))) : RatFunc E :=
    (logs.map (fun p => (((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots.map (fun c =>
      algebraMap E (RatFunc E) c *
        (towerDerivExt Dt (algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c))
          / algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c)))).sum)).sum
  -- soundness: over ANY diff. extension E where each Rᵢ splits, the identity holds (base-changed)
  def IsIntegralResultLrtG (Dt anum aden : CPolyG α) (res : LrtResultG α) : Prop :=
    ∀ (E) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [DifferentialAlgebra (CFieldSpec.K α) E],
      (∀ p ∈ res.logs, ((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).Splits (RingHom.id E)) →
      towerDerivExt Dt (⟦res.rational over E⟧) + logResidueSumLrtG Dt res.logs = ⟦anum/aden over E⟧
  ```
  ⚠️ **design-critical** — verify the shape (non-vacuous; the `E`-quantification + splitting hypothesis is the
  right descent vehicle; `evalLrtArg`/`towerDerivExt` typecheck against `extendDeriv`'s exact signature)
  before building on it. Gate-green once it typechecks.
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
