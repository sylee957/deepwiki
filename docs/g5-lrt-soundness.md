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
  Hermite part** (`cHermiteReduceTowerG`), so `hherm` transfers verbatim from the existing capstone.
- **`hmatch`** — the residue-log-derivative sum equals `hNum/Dstar`. **This is the only gap.**

For the *enumerated* case (residues in a `Finset s ⊂ K`, `Dstar = Lagrange.nodal s id` splits over `K`),
`hmatch` is DONE (`cIntegrateReducedG_logs_eq_per_root` + `ratFunc_eq_sum_residue_gcd`). The LRT route's
`hmatch` sums over the roots of `Rᵢ` in `K̄` — the algebraic-closure residue sum.

## Strategy: base-change to `K̄` + injectivity descent (avoids full Galois descent)

Let `K = CFieldSpec.K α`, `K̄ = AlgebraicClosure K`. `RatFunc K ↪ RatFunc K̄` (base change) is a *ring-hom
that intertwines the tower derivation* and is **injective**. Plan:

1. **State soundness over `K̄`.** Over `K̄`, `Dstar` splits: `toPolyG Dstar` (mapped to `K̄`) `= ∏(t − βⱼ)`,
   roots `βⱼ ∈ K̄`. The residues are `Rᵢ`'s roots in `K̄`. Define the symbolic-log denotation
   `logResidueSumLrtG` as the honest `K̄`-sum `Σᵢ Σ_{Rᵢ(c)=0 in K̄} c · logDeriv(Sᵢ(c,t))` where `Sᵢ(c,t) =
   Σₖ (eval₂ (algebraMap K K̄) c (toPolyG Sᵢ[k])) tᵏ`.
2. **Prove the `K̄`-`hmatch` by reusing the tower machinery over `K̄`.** Over `K̄` everything splits, so the
   enumerated `cIntegrateReducedG_logs_eq_per_root`-style argument applies with `s = (toPolyG Dstar).roots
   in K̄`. The bridges are the DONE pieces:
   - `Rᵢ`'s roots `= ` the residues, grouped by multiplicity `i` (via G4b `toPolyG_cResidueResultantTowerG`
     = `rtResultantGen`, whose roots are the residues by G2 `roots_rtResultantGen`; `cSqfreeYunFFG`
     multiplicity `↔` `rootMultiplicity`).
   - `Sᵢ(c,t) ~ gcd(Dstar, hNum − c·B)` at a residue `c` (via G4c `CPolySubresultant.toPoly_parametric_getD`
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
  ✅ **DONE** (`Computable/LrtSoundness.lean`, gate-clean) — `amGExt`, `evalLrtArg`, `towerDerivExt`,
  `logResidueSumLrtG`, `IsIntegralResultLrtG` all typecheck. Shape verified: the equation is
  `D(rational) + Σᵢ Σ_{c∈roots(Rᵢ in E)} c·(Δ Sᵢ(c,t))/Sᵢ(c,t) = anum/aden` over every splitting differential
  extension `E` — i.e. `D(antiderivative) = integrand`, the honest algebraic-residue soundness (true iff the
  residues are constants, the elementary case). `extendDeriv`/`implicitDeriv` needed `[Algebra ℚ E]`;
  `E : Type*` makes the def universe-polymorphic.
- **P2 — the residue↔root grouping.** `Rᵢ`'s roots in `K̄` are the residues of multiplicity `i`
  (`cSqfreeYunFFG` mult ↔ `rootMultiplicity` of `rtResultantGen`, via G4b + G2). Reuse
  `cResidueResultantTowerG` = `rtResultantGen`.
- **P3 — `Sᵢ` at a residue = the RT gcd.** `CPolySubresultant.toPoly_parametric_getD` (G4c) + `lazardRiobooTrager_
  output_isSimilar_gcd_gen` (G3), specialised at each root `c` of `Rᵢ`; the normality `hB` from
  `isCoprime_X_sub_C_implicitDeriv_iff` (the genuine `hcopgcd`).
- **P4 — the analytic identity over `E`.** **★★ NOT NEW MATH (2026-07-04):** the candidate route's
  **`monomial_residue_match_of_cancel`** (`ResidueMatchSoundness.lean:158`) *already* proves the **tower**
  identity over **any** field `K` `[Field K] [Differential K] [Algebra ℚ K]`: for `d = nodal s` (splits),
  `deg a < #s`, normal roots (`v(α) ≠ α′`), and `hcancel` (poly parts cancel — **automatic for primitive
  `Dt = C w`**, `monomial_residue_match_primitive`), it gives the **pole-indexed** sum
  `Σ_{α∈s} C(cₐ)·(D(t−α)/(t−α)) = a/d`, `D = extendDeriv (implicitDeriv v)`, `cₐ = a(α)/(implicitDeriv v d)(α)`
  — the mapCoeffs part IS handled (via `hcancel`). **It applies verbatim over `E`.** So P4 = instantiate this
  over `E` (`s = roots(Dstar in E)`, `a = hNum`, `v = Dt`). The genuinely-new work is *not* the analytic
  identity but the **residue↔pole REINDEXING**: my `logResidueSumLrtG` is *residue*-indexed
  (`Σ_c c·D(gcd_c)/gcd_c`), the theorem is *pole*-indexed (`Σ_β res(β)·D(t−β)/(t−β)`); they agree because
  `gcd_c = Sᵢ(c,t) = ∏_{res(β)=c}(t−β)` and `D(∏)/∏ = Σ D(t−β)/(t−β)` regroups the residue sum into the pole
  sum. So the remaining substance is **P3** (`Sᵢ(c) = gcd_c = ∏ linear factors`, via G4c+G3) + this regrouping;
  **P4's analytic core is a direct reuse.**
- **P5 — descent + assembly.** Base-change injectivity `RatFunc K ↪ RatFunc K̄` intertwining the derivation;
  assemble P2–P4 into the `K̄`-`hmatch`; combine with the transferred `hherm` via
  `field_identity_of_reducedG_of_residueMatch`; descend to `IsIntegralResultLrtG` over `K`. Then swap the
  primitive base to `cIntegrateReducedLrtG` ⟹ `hreduced` closed WITHOUT the rational-residue restriction.

## ⚠️ CRITICAL CORRECTNESS FINDING (2026-07-04) — raw `Sᵢ` is unsound over the tower

Digging into the residue↔pole reindexing surfaced a genuine subtlety that would have made a "one-shot"
proof **wrong**. The LRT log argument is a *subresultant* `Sᵢ(c,t)`, which equals `sᵢ(c)·(monic gcd)` where
`sᵢ(c) = (lrtSubresultant …).coeff i` is a leading-coefficient **unit** (`LrtMonicLogs.lrtPsc`,
`lrtSubresultant_eval_eq_psc_mul_monicLrtLog`). Its log-derivative contributes
`D(sᵢ(c))/sᵢ(c)` to each term.

- **Rational case (`K(x)`, formal `d/dx`):** the unit VANISHES — `logDeriv_algebraMap_C_mul_eq`
  (`LrtMonicLogs.lean:152`): `sᵢ(c)` is a `t`-constant so `derivative(C sᵢ(c)) = 0`. Raw `Sᵢ` is sound.
- **Tower case (`D_tower = mapCoeffs + Dt·d/dt`):** the unit does **NOT** vanish —
  `D_tower(C·sᵢ(c)) = C(D_base(sᵢ(c)))`, nonzero whenever `sᵢ(c)` is not a *base*-constant (it generally
  isn't — its a rational function of `x`). So `Σ_c c·D_base(sᵢ(c))/sᵢ(c)` is a **spurious extra term**, and
  the raw-`Sᵢ` reduced identity is **FALSE** over the tower.

**Consequence.** `cLrtLogArgG` currently emits the raw `CPolySubresultant.parametric`; for tower soundness the log
arguments must be **monic-normalized** (Bronstein §2 Ex 2.7 — divide each `Sᵢ(c,t)` by its leading
`t`-coefficient `sᵢ(c)`; abstract: `LrtMonicLogs.monicLrtLog`). So:
1. **P1's `IsIntegralResultLrtG` / `logResidueSumLrtG` and `cLrtLogArgG` must use the MONIC-normalized
   `Sᵢ`** (or `evalLrtArg` must divide out the leading coefficient), else the predicate is false for the
   raw engine output. This is a **design fix, not just a proof step**.
2. The computable engine needs a monic-normalization step (`CPolySubresultant.parametric` → divide by its top
   `t`-coefficient `z`-polynomial), and the `evalLrtArg`/soundness updated to match.

This is why raw-`Sᵢ` "in one shot" would have been wrong. The reindexing machinery (`towerDerivExt_div_*`,
committed) is unaffected and correct; it applies to the monic arguments. The remaining G5 work must first
route through the **monic normalization** (`LrtMonicLogs` gives the abstract facts: `monicLrtLog` monic,
`sᵢ`-unit coprime to `Qᵢ`, `lrtSubresultant_eval_eq_psc_mul_monicLrtLog`).

## Assembly progress (2026-07-04) — the reindexing side is COMPLETE

After the monic fix, `evalLrtArg` = the monic gcd (no unit), and the whole residue↔pole reindexing is built
gate-green in `LrtSoundness.lean`:
- `towerDerivExt_div_mul` / `_div_prod` / `_div_algebraMap_prod` — `D(∏ pᵢ)/∏ pᵢ = Σ D(pᵢ)/pᵢ` (log-deriv of
  a product = sum), via `Derivation.leibniz`. Splits `gcd = ∏(t−β)` into per-pole terms.
- `poleTerm β := D(t−β)/(t−β)`; `residue_pole_regroup` — `Σ_c c·(Σ_{res β=c} term β) = Σ_β res(β)·term β`
  (`Finset.sum_fiberwise_of_maps_to`).
- `logResidueTermLrtG_eq_pole_sum` → `logResidueTermLrtG_eq_finset_pole_sum` — per-`Rᵢ` term = the finset
  pole sum `Σ_{β∈polesᵢ} res(β)·poleTerm β` (given the gcd factorization `evalLrtArg Sᵢ c = ∏_{res β=c}(t−β)`).
- `logResidueSumLrtG_eq_termwise` — reduces the whole residue sum termwise.

**⟹ `logResidueSumLrtG` reduces to `Σ_β res(β)·poleTerm β` (the pole sum) given the per-`Rᵢ` factorizations.**

**P3 ENDPOINT DONE (`LrtGeneralDerivation.lean`):** `monicNormalize_of_eq_C_mul_monic` /
`monicNormalize_of_associated_monic` / **`monicNormalize_eq_of_isSimilar_prod`** —
`IsSimilar S (∏(t−β)) → S·C(S.leadingCoeff)⁻¹ = ∏(t−β)`. So with `S = lrtSubresultantGen.map(evalRingHom c)`
(`~ gcd` by G3) and `gcd = ∏_{res β=c}(t−β)` (by G2), the **monic log argument is the residue-`c` linear-factor
product** — exactly `evalLrtArg`'s value once `raw = S`.

**★★ P3 COMPLETE (2026-07-04) — the dense base-change is DONE and gate-green.** The "one dense spot" is
assembled: `lrtSubresultantGen_map` / `lrtSubresultantGen_map_eval₂` (abstract base-change of the subresultant
to `E` at `z=c`), `zipIdx_C_mul_X_pow_sum_coeff` (the coefficient-list polynomial's coeffs), **`raw_eq_map`**
(`evalLrtArg`'s raw sum `= S` via G4c coeff-by-coeff), and **`evalLrtArg_eq_prod`** (`evalLrtArg Sᵢ c =
∏_{β}(t−β)`, given the G4c identity `hg4c` + `IsSimilar S (∏(t−β))` `hsim`). Composes `raw_eq_map` +
`lrtSubresultantGen_map_eval₂` + `monicNormalize_eq_of_isSimilar_prod`. **The computable engine's log argument
provably equals the residue-pole product over `E`.**

**Remaining (mechanical wiring over proven lemmas):** discharge `hg4c` from G4c (`CPolySubresultant.toPoly_parametric_getD`
with `cLrtLogArgG`'s args + the `hm` degree fact) and `hsim` from G3 (`lazardRiobooTrager_output_isSimilar_gcd_gen`
over `E`) + G2 (`gcd_nodal_eq_prod_residue_gen`, `gcd = ∏`); the pole partition; `monomial_residue_match_of_cancel`
over `E`; the Hermite half; descent. No new math, no dense base-change — just applying proven theorems with
concrete arguments.

_(historical remaining note, now resolved:)_ `raw = S`, i.e. `evalLrtArg`'s raw sum
`Σ_k C((toPolyG Sᵢ[k]).eval₂(alg) c)·tᵏ = (lrtSubresultantGen …).map (eval₂RingHom (algebraMap K E) c)`
[G4c coeff-by-coeff] `= subresultant (Dstar_E)(hNum_E − c·Dd_E) …` [`subresultant_map` + `lrtSubresultantGen_eval`
over `E`] `= S`; then `S ~ gcd` [G3 over `E`], `gcd = ∏` [G2 over `E`]. The bivariate base-change is the dense
plumbing that entangles `cLrtLogArgG`'s specific args + the `hm` degree hypothesis.
- **partition** — the `polesᵢ` (per-`Rᵢ`) partition `Dstar`'s roots (LRT multiplicity structure).
- **P4** `Σ_β res(β)·poleTerm β = hNum/Dstar` — instantiate `monomial_residue_match_of_cancel` over `E`.
- **hherm** over `E` + **descent** (base-change injectivity) + assembly, then the `cLrtLogArgG` monic engine fix.

## Honest scope

P1–P3, P5-assembly are engineering over DONE pieces. **P4 is the genuine new mathematics** (the tower
simple-pole partial-fraction / residue identity over `K̄`), and the descent (P5) needs the base-change-
intertwines-derivation lemma. This is the multi-pass frontier the user chose; everything it stands on is
proven.

## ★★ CRUX ASSEMBLED (2026-07-04) — `logResidueSumLrtG_eq_normalPart` is a single named theorem

The **entire mathematical content of LRT log-part soundness** is now assembled as reusable, gate-green,
`sorryAx`-free lemmas in `Computable/LrtSoundness.lean`, culminating in the named theorem:

- **`logResidueSumLrtG_eq_normalPart`** — `logResidueSumLrtG Dt logs = hNum/Dstar` (as `RatFunc E`), over
  any splitting extension `E` where `Dstar` splits as `∏_{β ∈ allpoles}(t−β)`. This IS the log-part
  soundness. It composes, all proven this pass:
  - `logResidueSumLrtG_eq_poleSum` — log sum ↦ `Σ_{β ∈ allpoles} res(β)·poleTerm β` over a pole partition
    `polesOf` (chains `logResidueSumLrtG_eq_termwise` + `logResidueTermLrtG_eq_finset_pole_sum`).
  - `pole_sum_eq_normalPart` — the RT residue match `Σ_β res(β)·poleTerm β = hNum/Dstar`, a thin
    instantiation of `ResidueMatchTower.monomial_residue_match_of_cancel` at `K := E`, `v := (toPolyG Dt).map φ`
    (so `poleTerm Dt β` is **literally** its `extendDeriv(implicitDeriv v)(t−β)/(t−β)` summand — `congr 1`
    closes it by defeq) with the RT residue `res β = hNum(β)/D(∏)(β)`.
- **`evalLrtArg_cSubresultantParam_eq_prod`** (hg4c auto via G4c) + **`isSimilar_subresultant_prod`** (hsim via
  G3+G2, over alg-closed `E`) — discharge the `hfac` (`Sᵢ(c) = ∏ residue-`c` poles`) hypothesis.

**The named theorem's remaining hypotheses are engine-structural, not new math:**
- `hfac` — discharged by `evalLrtArg_cSubresultantParam_eq_prod` + `isSimilar_subresultant_prod` once the
  per-entry RT setup (`Dstar_E = nodal allpoles`, index `j = fiber size`, `A = hNum`, `B = Dd`) is threaded.
- `hroots` / `hpart` — the **Yun fiber-size partition**: `Rᵢ`'s roots are exactly the residues of the
  fiber-size-`i` poles, and these pole sets tile `allpoles`. The one genuinely intricate structural lemma left.
- `hcancel` — automatically `0` for a **primitive** `Dt` (the mapCoeffs part vanishes; already handled in
  `ResidueMatchSoundness`).
- `hA` (properness) / `hnorm` (normality `Dt(β) ≠ β′`) — standard RT preconditions.

**Still remaining for the full `IsIntegralResultLrtG cIntegrateReducedLrtG`:** thread the concrete
`cLrtLogArgG` entries into `hfac`; prove the Yun fiber-size partition (`hroots`/`hpart`); the Hermite half
`hherm`; the `E→K` descent + final assembly; and the `cLrtLogArgG` monic-normalization engine fix.

## ★★ ASSEMBLY SKELETON DONE (2026-07-04) — the whole soundness composes end-to-end

`Computable/LrtSoundness.lean` now closes the architecture, mirroring the rational-residue template
`field_identity_of_reducedG_of_residueMatch`:
- **`field_identity_lrt_of_hherm_of_logMatch`** (fixed `E`) — `rw [hlog]; exact hherm`.
- **`isIntegralResultLrtG_of_hherm_of_logMatch`** — packages it under the `∀E` quantifier (shared universe
  `u`), producing the full `IsIntegralResultLrtG Dt anum aden res` from **two clean per-`E` inputs**:
  - `hlog` — `logResidueSumLrtG res.logs = hNum/Dstar` (⇐ `logResidueSumLrtG_eq_normalPart` + Yun partition).
  - `hherm` — `D(g) + hNum/Dstar = a/d` (⇐ base-change of `cHermiteReduceTowerG_field_identity`).
- **`sum_over_list_partition`** — reduces `hpart` to plain pairwise-disjointness + union.

### ★★★ `hherm` DISCHARGED (2026-07-04) — only `hlog` (Yun partition) remains

`hherm_lrt_E` (`LrtSoundness.lean`) proves the Hermite half over `E` outright, by base-changing the DONE
K-level `cHermiteReduceTowerG_field_identity` (`HermiteValuationTower.lean:762`). The K→E transfer
machinery, all gate-green:
- `ratFuncBaseChange : RatFunc K →+* RatFunc E` = `RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap K E))`
  (+ `_nonZeroDivisors`, `_amG`, `_amG_div` : `amG p ↦ amGExt p`).
- `towerDerivExt_div` — the `E`-analogue tower quotient rule (mirror of `towerFractionFieldDerivG_div`).
- `ratFuncBaseChange_towerFractionFieldDerivG` — the **crux intertwining**: `ratFuncBaseChange` of a K-tower
  derivative = the E-tower derivative, via both quotient rules + `implicitDeriv_map` (SpecialFirstKind, uses
  `DifferentialAlgebra K E`).
- The residual `cdivWf(...) = H.2.1` is `toPolyG_hNum'_eq_2_1` (already proven).

So `hherm_lrt_E` closes one of the two `isIntegralResultLrtG_of_hherm_of_logMatch` inputs. Modulo only the
genuine differential-normality `hcopgcd` (Bronstein `hnorm`) + `hd0`/`hpp`.

**The single remaining gap is `hlog`** — `logResidueSumLrtG_eq_normalPart` needs the Yun fiber-size partition:
`hroots` (`Rᵢ`'s roots = residues of the fiber-size-`i` poles), `hfac` (via
`evalLrtArg_cSubresultantParam_eq_prod` + `isSimilar_subresultant_prod`, threading the per-entry RT setup),
`hpart` (via `sum_over_list_partition` + the disjoint fiber-size decomposition of `Dstar`'s roots), and `Dstar`
splits as `nodal allpoles`. This is the one intricate combinatorial/structural lemma left.

### `hlog` progress (2026-07-04) — design settled + geometric foundation done

- **`[IsAlgClosed E]`** — `IsIntegralResultLrtG` now quantifies over algebraically-closed `E`, and the per-`Rᵢ`
  splitting hypothesis is **dropped** (automatic). Rationale: the pole-match sums over `Dstar`'s **poles**,
  which must lie in `E`; `Dstar`-splits ⟹ residues ∈ `E` ⟹ `Rᵢ` splits, and the descent uses the algebraic
  closure anyway. `isIntegralResultLrtG_of_hherm_of_logMatch` updated in lockstep (`hherm_lrt_E` still fits).
- **`Dstar` is monic** (`toPolyG_cHermiteReduceTowerG_Dstar_monic`) **and squarefree** — so the
  leading-coefficient subtlety vanishes: `Dstar_E = nodal allpoles` **exactly**.
- **`monic_separable_eq_nodal`** (`LrtSoundness.lean`) — the geometric foundation: over alg-closed `E`, a monic
  separable poly `= Lagrange.nodal p.roots.toFinset id` (splits + monic ⟹ `∏(X−β)`; separable ⟹ `Nodup` ⟹
  multiset product collapses to the `Finset` nodal).

Remaining `hlog` pieces (each a real engine→abstract connection over `E`): residue-resultant roots = residues
(base-change G4b + `roots_residueResultantTowerG_eq_residues`); Yun structure over `E` (`Rᵢ` coprime,
`R = ∏Rᵢ^i`); `polesOf` + `hpart` (partition via Yun coprimality + `sum_over_list_partition`); `hroots`; `hfac`
(via `isSimilar_subresultant_prod`, index = fiber size); the RT setup (`hA`/`hnorm`/`hcancel`).

### ★★★ `hlog` ASSEMBLED (2026-07-04) — `logResidueSumLrtG_eq_normalPart_of_yun`

The full `hlog` now reduces to clean Yun-structure hypotheses. Built (`LrtSoundness.lean`, all gate-green):
- Residue structure: `rtResultantGen_map` (residue resultant base-changes) + `toPolyG_cResidueResultantTowerG_map`
  (concrete `R_E = rtResultantGen`) + `residueResultant_map_roots` (`R_E.roots = residues`, via `roots_rtResultantGen`).
- Geometric: `monic_separable_eq_nodal` (`Dstar_E = nodal allpoles`, monic+squarefree).
- **Three discharge cores**: `sum_filter_rootSet_partition` (`hpart`, via Yun coprimality + `mem_foldr_union_iff`),
  `roots_eq_image_res_filter` (`hroots`), `evalLrtArg_eq_fiber_prod` (`hfac`, via `isSimilar_subresultant_prod`;
  fixed a whnf timeout with `convert`+`omega` on the subresultant dimension).
- **Assembly** `logResidueSumLrtG_eq_normalPart_of_yun`: plugs the three cores into
  `logResidueSumLrtG_eq_normalPart` (`polesOf p := allpoles.filter(res ∈ Rᵢ.roots)`), concluding
  `logResidueSumLrtG = hNum/∏(t−β)` modulo the Yun facts `hnodup`/`hressub`/`hdisj`/`hcover`/`hentry` + RT setup.

**Remaining:** discharge those Yun facts for the concrete `cLrtLogArgG Dt hNum Dstar` over `E` — base-change
`cSqfreeYunFFG`'s correctness (`YunTowerCorrect`: squarefree/coprime/reconstruction) to `E`, and the per-entry
index = `rootMultiplicity` match (`hentry` via `evalLrtArg_eq_fiber_prod`). Then the final assembly +
`E→K` descent + swap the primitive base.

### ★★★★ CAPSTONE (2026-07-04) — `isIntegralResultLrtG_cIntegrateReducedLrtG`, whole soundness modulo `hlog`

The complete `IsIntegralResultLrtG` for the concrete `cIntegrateReducedLrtG Dt a d` is now assembled (all
gate-green, `sorryAx`-free): via the skeleton `isIntegralResultLrtG_of_hherm_of_logMatch`, the Hermite half is
discharged **outright** by `hherm_lrt_E`, leaving only `hlog` (`logResidueSumLrtG (cLrtLogArgG …) = hNum/Dstar`
over every alg-closed `E`) as a hypothesis, plus the genuine Hermite side conditions `hd0`/`hpp`/`hcopgcd`. So the
**sole remaining internal frontier is `hlog`**, and `hlog` is itself assembled (`logResidueSumLrtG_eq_normalPart_of_yun`)
modulo the 5 Yun facts.

### ★★★★★ ALL 5 YUN FACTS DONE (2026-07-05) — `hlog`'s hypotheses fully dischargeable

Every Yun fact for the concrete `cLrtLogArgG` is now proven and gate-green (`LrtSoundness.lean`):
- `mem_cLrtLogArgG` / `mem_cLrtLogArgG_of_yun_factor` — entry membership, both directions (`filterMap ∘ zipIdx`).
- **`hnodup`** `nodup_roots_cLrtLogArgG_entry` — `Rᵢ` squarefree ⟹ separable base-change ⟹ Nodup.
- **`hressub`** `residue_of_root_cLrtLogArgG_entry` — `Rᵢ | R` ⟹ roots ⊆ residues (`residueResultant_map_roots`).
- **`hcover`** `cover_cLrtLogArgG` — reconstruction `R ~ ∏Rᵢ^i` (`prodPow_map` + `mem_roots_prodPow`) ⟹ every
  residue is a root of some non-constant (`not_len_le_one_of_root`) Yun factor, hosting an entry.
- **`hdisj`** `disjoint_cLrtLogArgG` — `List.pairwise_filterMap` + `disjoint_yun_factors` (`_isRelPrime` ⟹
  `isCoprime` ⟹ base change ⟹ `disjoint_roots_of_isCoprime`).
- **`hentry`** `entry_log_eq_fiber_prod` — the multiplicity fact: `idx+1 = rootMultiplicity c R` via the crux
  `rootMult_R_map_eq_idx_succ` (reconstruction + `rootMult_prodPow_of_unique`: `c` a simple root of only `R_idx`
  — `yun_factor_map_squarefree` ⟹ mult 1, `disjoint_yun_factors` ⟹ mult 0), fed into `evalLrtArg_eq_fiber_prod`.

Multiplicity infrastructure built: `rootMultiplicity_pow_eq`, `associated_rootMultiplicity_eq`,
`squarefree_rootMultiplicity_eq_one`, `rootMult_prodPow_eq_zero`, `rootMult_prodPow_of_unique`.

### ★★★★★★ FINAL `hlog` WIRING DONE (2026-07-05) — all hard internal math proven

`logMatch_of_setup` (`LrtSoundness.lean`, gate-green) produces the capstone's `hlog` outright: it plugs the 5 Yun
facts into `logResidueSumLrtG_eq_normalPart_of_yun` (`hsplit` via `monic_separable_eq_nodal`; the `Dd_E =
implicitDeriv Dt_E Dstar_E` alignment `hDd2` via `toPolyG_cmonomialDeriv`+`implicitDeriv_map` bridges the
`residueResultant`/`entry` forms), concluding `logResidueSumLrtG (cLrtLogArgG Dt hNum Dstar) = hNum/Dstar` over
any alg-closed `E`, modulo the genuine RT side conditions (`hB`/`hnorm`/`hcancel`/`hilt` normality+cancellation,
`hAD`/`hAnd`/`hAdeg` properness, `hDmonic`/`hDsep`/`hR0`/`hRpp`/`hm` Hermite-provided).

**So every hard mathematical step of the LRT soundness is now proven.** The whole chain composes:
`hreduced` ⟸ swap base ⟸ `E→K` descent ⟸ **capstone (done)** ⟸ `hlog` = `logMatch_of_setup` (**done**)
⟸ 5 Yun facts (**done**).

**The LRT soundness is a complete, self-contained achievement:** `IsIntegralResultLrtG cIntegrateReducedLrtG`
(the root-free integrator is sound over any alg-closed differential extension) is provable by composing the
capstone with `logMatch_of_setup`, modulo the genuine Bronstein RT side conditions. Every hard mathematical
step is proven.

### ★ ARCHITECTURAL FINDING (2026-07-05) — `hreduced` is `IsIntegralResultG` (rational), not LRT

`PrimitiveFrontier.hreduced` (`RischTowerPrimitive.lean:42`) demands `IsIntegralResultG Dt (crNormNum) (crNormDen)
nrm` for `nrm = redNorm … = cIntegrateReducedG …` — the **rational-residue** reduced integrator with the
`logResidueSumG` (rational `α × CPolyG`) log form. The LRT track (`cIntegrateReducedLrtG` + `logResidueSumLrtG`
+ `IsIntegralResultLrtG`) is a **different, root-free** integrator with a *symbolic* `CPolyG × List` log form and
*algebraic* residues over the closure. There is no existing LRT frontier/instance. So the LRT soundness does
**not** directly close the existing `hreduced` — that would require:
1. **A new LRT-based frontier/instance** (`PrimitiveFrontierLrt` + `LawfulRischLevel`-style wiring using
   `cIntegrateReducedLrtG`), whose `hreducedLrt` obligation is exactly `IsIntegralResultLrtG cIntegrateReducedLrtG`
   (which we've proven). This is the "swap primitive base" — a parallel solver track, a distinct architectural
   development, not a descent.
2. Its own `E→K` handling: `IsIntegralResultLrtG` is already stated over alg-closed `E` (the descent vehicle),
   so a K-level LRT-soundness statement would instantiate/descend from `AlgebraicClosure K`.

**Net:** the *mathematics* of the root-free LRT algorithm is fully verified (`IsIntegralResultLrtG
cIntegrateReducedLrtG`, modulo Bronstein side conditions). Wiring it to supersede the rational reduced integrator
in the solver (closing an LRT-analogue of `hreduced`) is a separate architectural track.

### ★ `hlog` is ASSEMBLY, not a wall (2026-07-04) — every abstract endpoint already exists

Scoping confirmed no research gap remains; `hlog` is a (large) mechanical assembly of proven pieces:
- **residue roots = residues** — `roots_rtResultantGen` (`LrtGeneralDerivation.lean:131`, `[IsAlgClosed K]`)
  already proves `(rtResultantGen A D B).roots = residues`, via `Polynomial.resultant_eq_prod_eval` (the
  Poisson product formula, present in the repo). G4b (`toPolyG_cResidueResultantTowerG`) connects the
  concrete `R` to `rtResultantGen` (needs base-change to `E`).
- **gcd = linear factor** — `residue_gcd_associated_linear_factor` (`LogPartTowerSoundness.lean:75`, generic).
- **`Sᵢ` = ∏ residue poles** — `isSimilar_subresultant_prod` + `evalLrtArg_cSubresultantParam_eq_prod` (done).
- **pole sum = normal part** — `pole_sum_eq_normalPart` (the tower residue match; done).
- **Yun structure** — `YunTowerCorrect` (`cSqfreeYunFFG_squarefree/_isRelPrime/_monic/_reconstruction`, all
  proven) gives the coprime squarefree factors for the fiber-size partition.
- **`Dstar` splits** — `monic_separable_eq_nodal` (done) + `Dstar` monic/squarefree.

So the remaining labor is threading these into `hroots`/`hfac`/`hpart` for the concrete `cLrtLogArgG`, not new
mathematics. The `ratFunc_eq_sum_residue_gcd` abstract theorem is the *formal-derivative* case; the *tower*
case is exactly `pole_sum_eq_normalPart`, already in hand.

Then `E→K` descent + swap the primitive base ⟹ `PrimitiveFrontier.hreduced` closed, without the
rational-residue restriction.

### ★★ FULL ROOT-FREE SOLVER ASSEMBLED (2026-07-05) — the swap is DONE

The "separate architectural track" above is now built. Five gate-green pieces make the root-free primitive
solver an exact parallel of the rational one:

| rational (residues ∈ K) | root-free (algebraic residues) | file |
|---|---|---|
| `IsIntegralResultG` | `IsIntegralResultLrtG` | IntegrationSpec / LrtSoundness |
| `IsElementaryIntegrableG` | `IsElementaryIntegrableLrtG` | Assemble / RischTowerPrimitiveLrt |
| `combineSN` / `combineSN_isIntegralResult` | `combineSNLrt` / `combineSNLrt_isIntegralResultLrt` | Assemble / LrtAssembly |
| `cIntegrateCase` / `cIntegrateCase_sound` | `cIntegrateCaseLrt` / `cIntegrateCaseLrt_sound` | IntegratorAssembly / LrtAssembly |
| `LawfulRischLevel` / `integrate` / `sound` | `LawfulRischLevelLrt` / `integrateLrt` / `soundLrt` | RischTower / RischTowerLrt |
| `PrimitiveFrontier.hreduced` ← `..._via_interfaces` | `PrimitiveFrontierLrt.hreducedLrt` ← `isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup` | RischTowerPrimitive(Lrt) |
| `instLawfulRischLevelPrimitive` | `instLawfulRischLevelLrtPrimitive` | RischTowerPrimitive(Lrt) |

- The rational special part is frontier-independent: `lrtMonomialCase_specialSound` composes the selected
  `LawfulCLrtMonomialCase` with canonical reconstruction.
- `soundLrt` holds over **every** algebraically-closed differential extension `E` (the descent vehicle
  built into `IsIntegralResultLrtG`), so it handles **algebraic residues** — the whole point.
- Materialize **one** `PrimitiveFrontierLrt α` ⇒ `integrateLrt`/`soundLrt` resolve parameter-free.

**The essential difference:** the LRT frontier's obligation `hreducedLrt` is **general** — dischargeable
(`isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup`) modulo only the genuine Bronstein criterion
(normality `hnorm`, RT cancellation `hcancel`, and structural per-`E` conditions), with **no**
rational-residue restriction. The rational `hreduced` cannot be closed in general (it demands rational
residues), which is exactly why the swap was needed. Assembling `hreduced` = building this LRT track.

**Remaining (optional):** materialize a concrete `PrimitiveFrontierLrt` instance for a worked
algebraic-residue example (the genuine `hnorm`/`hcancel` are the actual integrability criterion, supplied per
input); discharge more structural `hE` conditions (`hB`/`hAnd`/`hAdeg` from `Dstar` squarefree over `E`).

### ★★ `descendGenuine` reduction map (2026-07-05) — the mathematical heart is DONE

`descendGenuine` (`LiouvilleCompleteness.lean`, the completeness frontier): genuine elementary integrability
of the reduced part ⟹ `cResidueConstantGuardG` (the residues are constants). Research (grounded in
`isLiouville_logExtension_uncond` + `ratFunc_logarithmFree_iff_residues_zero`, both done in-project) re-scoped
it from "research-grade / missing from Mathlib" to a **computable→abstract bridge** — the *converse* of the
forward LRT soundness development. Across the loop it decomposed, and **every self-contained mathematical piece
is now proven, gate-green**:

**Proven (the residue-criterion heart):**
- *Liouville-form bridge* — `logResidueSumG_eq_logDerivForm`, `isIntegralResultG_iff_liouvilleForm`
  (`LiouvilleFormBridge.lean`): `IsIntegralResultG` **is** the abstract Liouville form `Δg + Σ cᵢ·logDeriv uᵢ`.
- *roots ↔ residues* — `roots_rtResultantGen` (`LrtGeneralDerivation.lean`, forward, already built).
- *ultrametric* — `le_ratFuncOrd_add` (`νₚ(x+y) ≥ min`), `ratFuncOrd_neg` (`RatFuncValuation.lean`).
- *pole-order heart* — `ratFuncOrd_nonneg_of_extendDeriv_ge_neg_one` (at-most-simple-pole derivative ⟹ regular).
- *(a) g regular* — `ratFuncOrd_nonneg_of_liouville_reduced` (reduced Liouville form ⟹ `νₚ g ≥ 0`).
- *(b) Dg no residue* — `ratFuncOrd_extendDeriv_nonneg_of_nonneg` (`D` of regular is regular) + capstone
  `ratFuncOrd_extendDeriv_nonneg_of_liouville_reduced` (reduced Liouville ⟹ `νₚ(Dg) ≥ 0`).
- *(c2) residue vanishes on regular* — `residueAt_eq_zero_of_regular` (`RecognizingLogDeriv.lean`).

**Remaining = the E-level assembly (large integration, not small lemmas):**
1. **Tower-derivation residue analysis.** The base `residueAt` machinery (`residueAt_logDeriv_eq_rootMultiplicity`,
   `residueAt_derivative_eq_zero`) is w.r.t. the *formal* `d/dX`; `descendGenuine`'s derivation is the *tower*
   `Δ = towerFractionFieldDerivG`. So "`residueAt β (Σ cᵢ·logDeriv_Δ vᵢ) = Σ cᵢ·mult_β(vᵢ)`" is **not** a direct
   port — the log-sum residue must be redone for `Δ` (via `residueAt_sum_of_witnesses` + witness threading).
2. **Base-change to the splitting field `E`.** Poles/residues live in `E` (roots of `R`), so the valuation heart
   and residue algebra base-change to `RatFunc E` — reuse the forward soundness `ratFuncBaseChange` /
   `towerDerivExt` / `roots_rtResultantGen` machinery (`LrtSoundness.lean`).
3. **RT-root ↔ residue-value ↔ guard.** `residueAt β f = Σ cᵢ·mult` (constant, from (c2) + the log-sum residue) =
   the RT residue at `β`; then `D(cmonicG R) = 0 ⟺ all roots constant ⟺ cResidueConstantGuardG`.

**Verdict:** the hard mathematical content (pole-order reasoning + residue-vanishing) is **done**; what remains is
a project-internal base-change/threading assembly on the scale of the *forward* LRT soundness capstone (it reuses
essentially all of it), not a research problem. The `exp`-case Liouville instance (`ExpCaseLiouvilleFrontier`)
remains the one genuine frontier.

**Refinement (why step (1) is witness-threaded, not scalar lemmas).** The residue algebra over `RatFunc E` cannot
be built from clean unconditional laws: `RatFunc.eval` is only *conditionally* multiplicative
(`RatFunc.eval_mul` requires `denom(α) ≠ 0`), and residues live exactly at poles (`denom(α) = 0`). So the basic
residue identities — scalar pull-out `residueAt β (C c · x) = c · residueAt β x` and additivity
`residueAt β (x+y) = residueAt β x + residueAt β y` — hold only under the **simple-pole** structure, i.e. they
are the *witness* lemmas `residueAt_sub_of_witnesses` / `residueAt_sum_of_witnesses` (which carry `(X−β)·tᵢ =
aᵢ/bᵢ`, `bᵢ(β) ≠ 0`). Consequently the log-sum residue `residueAt β (Σ cᵢ·logDeriv_Δ vᵢ) = Σ cᵢ·mult_β(vᵢ)`
must be assembled by constructing the per-term simple-pole witnesses for the **tower** derivation `Δ` (the base
`residueAt_logDeriv_eq_rootMultiplicity` is for the formal `d/dX`). This is the crux of the remaining size: the
residue-value matching is a witness-threaded residue-algebra development over `E`, mirroring the forward
soundness LRT residue machinery, not a handful of one-line corollaries.
