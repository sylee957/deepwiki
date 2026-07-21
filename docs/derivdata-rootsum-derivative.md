# The computable derivative of the integral records

**GOAL (achieved, including the API flip — no separate denotation object)**: a
computable, `DenseFrac R`-valued derivative of the result records — **the records'
`.deriv`** (`ResultLrt.deriv`, `ResultRatIntegral.deriv`, in `Integrate/DerivData.lean`)
— with `(ratIntegrate f).deriv = f` the **decidable** primary spec. There is no
`derivDenote`: the `RatFunc` reading is spelled `DenseFrac.toRatFunc res.deriv`, and the
squares characterize it as the derivative of the represented antiderivative
(`ResultLrt.toRatFunc_deriv : toRatFunc res.deriv = (res.terms.map lrtPairTerm).sum`;
`ResultRatIntegral.toRatFunc_deriv` adds the rational/polynomial contributions — both
under the pair-nonvanishing contract `hS`, discharged for engine output by
`lrtIntegrate_pairs_ne_zero`). `RatIntegrateSpec.lean` is deleted — its assembly lives
inside `ratIntegrate_sound`'s proof; the denotational LRT soundness survives as
`lrtIntegrate_pairTerm_sum` (LogPartSpec). Primary specs in
`Integrate/DerivDataSpec.lean`: `lrtIntegrate_sound`/`_complete` (hsf+hprop, no hnum)
and `ratIntegrate_sound`/`_complete` (hypothesis-free). Frontend: record-form
`integrateExpr_sound`/`_complete` against `e.toFrac`; the AST bridge is
`toExpr_deriv (hS) : res.toExpr.deriv = toRatFunc res.deriv` and
`toRatFunc_integrateExpr_deriv : toRatFunc (integrateExpr e).deriv = e.eval`, giving
`integrateAst_sound/complete` at the `RatFunc` level.

## The route: resultant deformation (no trace, no modular inverse)

The only noncomputable piece of `res.deriv` is the root sum
`∑_{Q(α)=0} α · Sₓ(α,x)/S(α,x)`. Routes considered:

- Trace in the étale algebra `K[z]/(Q)` — needs mod-`Q` inverse (extended Euclid, new)
  + a trace-equals-root-sum bridge (heavy Mathlib work). Rejected.
- Power sums via Newton identities — needs Vieta/Newton over root multisets. Rejected.
- **Chosen — resultant deformation**: for `F(t) := Res_z(Q(z), S(z,x) + t·z·Sₓ(z,x))`
  over the coefficient ring `K[x][t]`, the product formula
  `Res(Q,T) = lc(Q)^{deg T} ∏_{Q(α)=0} T(α)` gives
  `F(t) = c·∏_α (S(α,x) + t·α·Sₓ(α,x))`, hence

  ```
  ∑_{Q(α)=0} α·Sₓ(α,x)/S(α,x) = F'(0)/F(0) = F.coeff 1 / F.coeff 0
  ```

  — computable with the existing total resultant dispatch (default Sylvester instance
  over the `CommRing` `K[x][t]`), constant factors and degree-inflation `lc`-powers
  cancel in the ratio, and `normalize` makes the quotient canonical (degenerate records
  fall to the canonical zero).

## Phases

### Phase 1 — computable core + decidable self-checks — DONE (2026-07-21)

- `zSwap : DensePoly (DensePoly R) → DensePoly (DensePoly R)` — transpose the `x`-outer
  engine representation of `S` to `z`-outer (coefficient-matrix transpose).
- `rootSumDeriv (Q : DensePoly R) (S : DensePoly (DensePoly R)) : DenseFrac R` — the
  deformed resultant's `coeff 1 / coeff 0` (in `Integrate/DerivData.lean`).
- `ResultLrt.deriv` (sum over pairs), `ResultRatIntegral.deriv`
  (`rational′ + ofPoly (poly′) + logs.deriv`) — originally named `derivData`, renamed
  in the Phase-2 API flip.
- **Validation (historical)**: three `native_decide` self-checks
  (`(ratIntegrate f).deriv = f` on concrete log / rational / mixed inputs) validated the
  computable core during Phase 1; they were **removed** once Phase 2 proved the general
  theorem `ratIntegrate_sound`, which subsumes them.

**Phase 1 notes (as landed)**: all three self-checks passed on the first run — the
deformation identity is empirically exact at the data level (not just denotationally):
the produced `DenseFrac` literally reconstructs the input's canonical `num`/`den`.
Degree-inflation `lc`-powers and resultant sign conventions cancel in the `F₁/F₀`
ratio as predicted; `normalize` canonicalizes.

### Phase 2 — the square (abstract correctness) — DONE (2026-07-21)

Everything landed in `Integrate/DerivDataSpec.lean` (+ homes in `Poly/Bivariate.lean`),
gate-clean, axiom-clean (`propext/Classical.choice/Quot.sound`):

- **Per-pair square** `toRatFunc_rootSumDeriv : toRatFunc (rootSumDeriv Q S)
  = lrtPairTerm (Q, S)` under `Squarefree (toPolynomial Q)` + the per-root
  nonvanishing of the specialized log argument. Route as planned: engine→Mathlib via
  `DensePolyResultant.resultant_eq` + `resultant_map_map` through the reading homs
  `tRead`/`xConst`/`kConst`; split `Q` by `Splits.eq_prod_roots` (nodup roots from
  squarefree via `PerfectField.separable_iff_squarefree`); product formula via
  `resultant_C_mul_left` + `resultant_prod_left` + `resultant_X_sub_C_pow_left`;
  deformed-product coefficients (Phase-2a lemmas); ratio via
  `sum_mul_prod_erase_div_prod`.
- **Homes**: `zSwap`, `coeff_coeff_zSwap`, `zEval`, `coeff_zEval`, `toPolynomial_zEval`
  and the swap-eval bridge `toPolynomial₂_zSwap_eval` moved to `Poly/Bivariate.lean`
  (CommRing level); `toPolynomial_X` moved from `Frontend/Expr.lean` to
  `Poly/Operations.lean`; `rootSumDeriv`'s section gained the missing
  `[DensePolyGcd R]` (it had silently baked the default gcd instance).
- **Record squares**: `ResultLrt.toRatFunc_derivData` (squarefreeness from the record
  invariant; nonvanishing as a hypothesis) and `ResultRatIntegral.toRatFunc_derivData`.
- **Contract discharge**: `lrtIntegrate_pairs_ne_zero` — the produced pairs' specialized
  log arguments are nonzero (via `lrtLogTerms_isSimilar_gcd` + `rtData_gcdVal`/
  `RtData.ne_zero`; the `rtData` instance-boundary record sidesteps the classical-vs-real
  gcd-instance mismatch).
- **Capstone (hypothesis-free, decidable)**:
  `ratIntegrate_derivData : (ratIntegrate f).derivData = f` — via
  `DenseFrac.toRatFunc_injective` + the record square + `ratIntegrate_sound`.

**Proof-engineering notes**: never let `congr`/`rfl` defeq-compare a `resultant`
application against anything (whnf unfolds the Sylvester determinant — 200k-heartbeat
timeout); rewrite with `Finset.prod_congr rfl h` instead. Give `resultant_prod_left` its
`s`/`f` arguments explicitly (a `by simp` side goal with metavars hangs). Pass the record
argument of `ResultRatIntegral.toRatFunc_derivData` explicitly (a `_` forces projection
inversion through `hermiteReduce`). Under `open scoped FormalDiff`, pin the RatFunc
instance with `attribute [local instance 2000]
SymbolicIntegration.instDifferentialRatFunc_deepWiki`.

## Conventions

Computable-first with `native_decide` validation is the established pattern (per the
transcendental-Risch precedent); Phase 2 is the required invariant arc, not optional.
Gate-green per phase; commit only after review.
