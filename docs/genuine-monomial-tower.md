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

## Status

- **✅ DONE (2026-07-06).** `GenuinePrimitiveMonomialLrt Dt` (input-independent, `LrtSoundness.lean`) +
  `lrtPoleNormalityData_of_genuineMonomial` (per-input `hE` in one line). **The structure field
  `LrtReducedGenuineData.hE` is now `GenuinePrimitiveMonomialLrt Dt`** (was the per-input `LrtPoleNormalityData
  Dt a d`); `isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine` derives the per-input normality (hence
  `hR0`) from it. So the frontier's normality now depends only on the monomial, not the integrand.

## Next

1. **Derive `hm` from `GenuinePrimitiveMonomialLrt`** (the `D(cₙ₋₁)+nη≠0` argument — a K-level bridge:
   `toPolyG_cmonomialDeriv` + monic-`Dstar` sub-leading-coeff + `η ∉ range D_K` from the property at `K̄`).
2. **Derive `hcopgcd`** (normality of Yun factors ⟺ `η ≠ β′` via `isCoprime_X_sub_C_implicitDeriv_iff`).
3. **Discharge `hAD`** from the Hermite properness invariant (algorithm-derived, belongs nowhere in the frontier).
4. **Collapse the frontier** to `{GenuinePrimitiveMonomialLrt Dt (monomial), hDt0 (scope)}` — everything else
   derived. Then **pull the monomial property out of the per-input structure** (provided once per `Dt`).
5. **`GenuineMonomialTower` class** capturing the invariant for a whole concrete tower (each level a genuine
   monomial), from which `[PrimitiveFrontierLrt]` is discharged unconditionally on that tower.
