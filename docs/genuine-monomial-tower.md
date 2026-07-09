# Genuine monomial tower — normality as a tower fact, not a per-input tax

## The insight

`LrtReducedGenuineData`'s "genuine Bronstein conditions" are **not** independent per-integrand conditions.
The three normality ones (`hE`, and via `hE` also `hR0`; to come `hcopgcd`, `hm`) all follow from a **single
input-independent fact** about the tower level's monomial:

> `η = Dt` is **not a derivative** — at every alg-closed extension `E`, `η ∉ range(D_E)`.

This is exactly Bronstein's monomial condition (Def 5.1.1 / Lemma 5.1.2: `Dt` not the derivative of an element
⟺ `t` is a genuine monomial ⟺ `Const(k(t)) = Const(k)`). Being about `Dt` alone, it is provided **once per
tower level**, not per integrand — and, crucially, for a **concrete** genuine tower (`ℚ(x)(log x)…`) it is
**provable** (`1/x` is not the derivative of an algebraic function), so the frontier *vanishes* on concrete
towers rather than being an eternal `∀`-hypothesis.

Why each condition follows from `η ∉ range D`:
- **`hE`** (`η ≠ β′` at a pole `β`): `β′ = D β ∈ range(D)`, and `η ∉ range(D)`, so `η ≠ β′`. **One line.**
- **`hm`** (`D(Dstar)` drops degree by one): the sub-leading coeff is `D(cₙ₋₁) + n·η`; if it were `0`, then
  `η = D(−cₙ₋₁/n) ∈ range(D)` — contradiction.
- **`hcopgcd`** (normality of `d`'s repeated factors): for a linear factor `t−β`, normality `gcd(t−β, D(t−β))=1`
  ⟺ `η ≠ β′` = `hE`; higher factors reduce the same way.
- **`hR0`** already derives from `hE` (`hR0_of_normalityData`), hence from the monomial property.

`hAD` (properness `deg hNum < deg Dstar`) is *not* a normality condition at all — it is **guaranteed by Hermite
reduction** and should be a discharged theorem. `hDt0` (`deg Dt = 0`) is the primitive-case **scope tag**.

## Status — all three normality conditions subsumed; frontier now `{hDt0, hAD, hE}`

- **✅ `hE` (2026-07-06).** `GenuinePrimitiveMonomialLrt Dt` (input-independent, `LrtSoundness.lean`) +
  `lrtPoleNormalityData_of_genuineMonomial` (per-input `hE` in one line). **The structure field
  `LrtReducedGenuineData.hE` is now `GenuinePrimitiveMonomialLrt Dt`** (was per-input `LrtPoleNormalityData`);
  `_of_genuine` derives the per-input normality (hence `hR0`) from it.
- **✅ `hm` (2026-07-06).** **Removed from the structure.** `natDegree_implicitDeriv_eq_of_monic_of_not_range`
  (`LrtGeneralDerivation`, the exact `D(cₙ₋₁)+nη≠0` argument) + `eta_not_range_der` (`η ∉ range D_K` via the
  property at `K̄` + `deriv_algebraMap` descent) + `hm_of_genuineMonomial` (the `cdegG`/`cmonomialDeriv` bridge,
  deg-0 case separate). `_of_genuine` derives `hm` from `hgen.hE`.
- **✅ `hcopgcd` (2026-07-06).** **Removed from the structure.** The deepest normality condition (Yun factors'
  normality: `gcd(d/vᵐ·D(v), v)` is a unit) — assembled from three pieces in `LrtResidueResultantDischarge`:
  - `isCoprime_implicitDeriv_of_genuineMonomial` — `IsCoprime v (D v)` for monic squarefree `v` (base-change to
    `K̄` via `isCoprime_map`, `v` splits `monic_separable_eq_nodal`, `isCoprime_prod_X_sub_C_implicitDeriv_iff` +
    the monomial property). The normality math.
  - `isCoprime_cofactor_yunFactor` — the cofactor coprimality `IsCoprime (d/vᵐ) v`: over `K̄`, `v` splits; at
    each root `β` of `v`, `rootMult β d = idx+1` (`rootMult_R_map_eq_idx_succ`, the residue-multiplicity toolkit)
    equals `rootMult β (vᵐ)` (β simple), forcing `rootMult β (d/vᵐ) = 0` — β not a root of the cofactor. (Went
    through the *root-multiplicity* toolkit already built for the residue analysis, not a `List.prod`
    reconstruction-cancellation.)
  - `natDegree_cgcdWf_eq_zero_of_isCoprime` — the `cgcdWf`-unit bridge (`IsCoprime.isUnit_of_dvd'`).
  - `hcopgcd_of_genuineMonomial` assembles them (`IsCoprime.mul_left` + the `zipIdx`→`get` bridge
    `List.mk_mem_zipIdx_iff_getElem?`); `_of_genuine` derives `hcopgcd` from `hgen.hE`.

## `hDt0` retired by if-branching — frontier now `{hAD, hE}`

The **decidability criterion**: an `if`-branch discharges a hypothesis iff the algorithm can *test* it at
runtime — then the branch *knows* it holds, so it stops being a frontier hypothesis.

- **`hDt0`** (`deg Dt = 0`) — **DECIDABLE** (`cdegG Dt` computable) ⟹ **RETIRED (2026-07-06).**
  `cIntegrateCaseLrt` now guards its body with `if cdegG Dt = 0 then … else none`. Faithful: the whole LRT
  solver is a tower of *primitive* levels (`primitiveGuardedCase`/`towerPrimitiveCaseLrt`, `deg Dt = 0`
  throughout), so on valid inputs the guard is always-true (behaviour unchanged) and a successful run *decides*
  `deg Dt = 0`. `cIntegrateCaseLrt_sound` derives `hDt0` from the guard (`cdegG_eq_natDegree`); the guard is
  threaded through `reducedSoundLrt`/`hreducedLrt`, the connectors, both instances, and
  `isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine`. **`hDt0` removed from `LrtReducedGenuineData`.**
  This also *fixed an over-strong frontier*: the structure was formerly demanded for **all** `Dt` (incl.
  `deg Dt ≠ 0`, where `hDt0` is false). Axiom-clean.
- **`hE`** (`η ∉ range D`) — **UNDECIDABLE** (existential over an infinite field: you cannot `if`-test "is `Dt`
  the derivative of *some* element"). Stays external — Bronstein's standing monomial hypothesis (Thm 5.1.1),
  provable on a concrete tower. The single genuine mathematical frontier.
- **`hAD`** (`deg hNum < deg Dstar`) — decidable, but **NOT a clean `if` guard**, and the discharge is a real
  project. For a *polynomial* integrand (`∫x²`) the normal part is `0/1`, so `hAD` is `0 < 0` = **false**; an
  `if hAD` guard would make `cIntegrateCaseLrt` return `none`, *breaking polynomial integration*. So `hAD` needs
  the canonical-rep properness **discharge**. ★ **It IS generically dischargeable** (corrected 2026-07-06 — not
  carrier-specific: the building blocks `cextendedEuclideanSplitWf_snd_degree_lt` and
  `cHermiteReduceTowerG_residual_proper_of_degree_le_one` are generic over `α`), but it is a **~150–200L
  multi-piece assembly**, mapped below.

## The `hAD` discharge — roadmap (~150–200L, generic; steps 1+2a LANDED 2026-07-06)

`crNormNum = (cextendedEuclideanSplitWf dnds.1 dnds.2 qr.2 uw.1 uw.2).2`, `crNormDen = dnds.1`
(from `canonicalRepresentationFastG`, `Tower/WellFounded.lean`), so:

1. **✅ crNorm properness `deg crNormNum < deg crNormDen`** (`crNormNum_degree_lt_crNormDen`,
   `CanonicalReconstructionCharZero`, commit `e02807e8`) — the never-done "cleanup target", now LANDED
   generically (`.degree` form, unconditional on `d ≠ 0`, incl. `crNormNum = 0` via `⊥ < deg dₙ`). From
   `cextendedEuclideanSplitWf_snd_degree_lt` + the split `d = ds·dn`
   (`cSplitFactorFastG_isSplittingFactorizationGen`) + special⊥normal Bézout
   (`isCoprime_of_isSpecial_isNormalSqfree`, `toPolyG_cbezoutOneWf`) + remainder bound (`cmodWf_length_lt`).
2. **✅ (2a) Generic `.degree` leftover-proper** (`cHermiteReduceTowerG_leftover_proper_of_degree_le_one`,
   `NormalPartSoundness`, commit `61198cf6`) — `deg (…).2.1 < deg (…).2.2` from `deg a < deg d` + `deg Dt ≤ 1`
   + the per-factor `hv`/`hb` + residual divisibility `hdvd` (+ `hresDen`/`hDstar`).
3. **✅ (2b) FULL `.degree` discharge** (`hAD_degree_of_genuineMonomial`, `LrtResidueResultantDischarge`,
   commit `dea5c480`, axiom-clean) — `deg (…).2.1 < deg (…).2.2` from **only** `(hgcd, hd0, hpp, deg Dt ≤ 1,
   deg a < deg d, hgen)`. Every leftover-proper hypothesis discharged: `hv`/`hb` (Yun `get_ne_zero` +
   `cdiophantineG_fst_degree_lt`), `hDstar`/`hresDen` (`Dstar_monic`/`den_ne_zero`), and **`hdvd`** from
   `hWgd_of_multiplicity` (`hcopgcd` derived from `hgen`) via the `d = W·Dstar` cancellation, bridging the raw
   fold `g` to the `cnormG`-projections through `toPolyG` (`set g` + `toPolyG_cnormG` leaf rewrites `hg1`/`hg2`).
   The residual-divisibility assembly — the hard mathematical core — is DONE.
4. **✅ (step 3) `.degree`→`.natDegree` + the `cn = 0` edge + FIELD REMOVED** (commits `ad5295e3`→`f0d5ddf6`,
   axiom-clean). `_of_genuine` now takes `haProper` (`deg a < deg d`, supplied by `crNormNum_degree_lt_crNormDen`
   at the canonical normal part) and **case-splits on `deg Dstar`**:
   - `deg Dstar ≥ 1`: `.degree hAD` → `.natDegree hAD` via `Polynomial.natDegree_lt_natDegree` (case `hNum=0` →
     `0 < deg Dstar`), then the existing residue path (`…_of_setup`).
   - `deg Dstar = 0` (no poles, the `0<0` edge, ⟺ trivial normal part): the **no-poles soundness**
     `isIntegralResultLrtG_cIntegrateReducedLrtG_of_noPoles` — assembled from the *hAD-independent* Hermite
     identity `hherm_lrt_E` + the empty log part `cLrtLogArgG_eq_nil_of_cdegG_zero` (constant `Dstar` ⟹ constant
     residue resultant `cdegG_cResidueResultantTowerG_eq_zero_of_cdegG_zero` ⟹ empty Yun factorization
     `cSqfreeYunFFG_eq_nil_of_cdegG_zero`) + the vanishing leftover numerator (`H.2.1 = 0` from `.degree hAD`).
   The `hAD` field is dropped ⟹ **`LrtReducedGenuineData = {hE}`**.

## ✅ DONE — the frontier is a single genuine monomial property

`LrtReducedGenuineData = {hE}` = `GenuinePrimitiveMonomialLrt Dt` (`η = Dt ∉ range D`). Every side condition —
`hcopgcd`, `hR0`, `hm`, `hnorm`, `hAD`, and the `hDt0` scope guard — flows from this single input-independent
tower fact, provable on a concrete genuine tower. Matches Bronstein exactly: `hE` = Thm 5.1.1's monomial
hypothesis; the no-poles case-split = §5.6's empty residue set (`deg(0) = −∞` faithful, p.129). All axiom-clean.

Remaining (optional): pull `hE` out of the per-input `LrtReducedGenuineData` structure (the `a d` params are now
vestigial — `hE` depends only on `Dt`); a `GenuineMonomialTower` class discharging `[PrimitiveFrontierLrt]`
unconditionally on a concrete tower.

## Next (optional)

1. **Discharge `hAD`** per the roadmap above → `LrtReducedGenuineData = {hE}`, the single genuine monomial property.
2. **Pull `hE` out of the per-input structure** (it depends only on `Dt`, provided once per tower level).
3. **`GenuineMonomialTower` class** capturing the invariant for a whole concrete tower, from which
   `[PrimitiveFrontierLrt]` is discharged unconditionally on that tower.
