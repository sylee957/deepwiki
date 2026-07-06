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

## Next

1. **Discharge `hAD`** from the Hermite properness invariant (`cHermiteReduceTowerGWf_numer_degree_lt_of_degree_le_one`,
   concrete-carrier — algorithm-derived, belongs nowhere in the frontier).
2. **Collapse** to `{GenuinePrimitiveMonomialLrt Dt, hDt0 (scope)}`, then **pull the monomial property out of the
   per-input structure** (provided once per `Dt`).
3. **`GenuineMonomialTower` class** capturing the invariant for a whole concrete tower, from which
   `[PrimitiveFrontierLrt]` is discharged unconditionally on that tower.
