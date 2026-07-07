# Reorg: DiffPoly fraction-field derivative

Target module: `DeepWiki.SymbolicIntegration.Core.Differential.DiffPolyFractionDeriv`

Move the quotient-rule derivative on `FractionRing (DiffPoly K)` out of
`Core/Differential/DifferentialPolynomials.lean`. The source file should define
the differential-polynomial carrier, `ddx`, and substitution/evaluation maps; the
new leaf should define the fraction-field derivative induced by `ddx`.

Decls to move:
- `fracDerivAux` (private)
- `fracDerivAux_wd` (private)
- `fracDeriv`
- `fracDeriv_mk`
- `diffPoly_fraction_mk_eq_of_cross_mul`
- `fracDeriv_algebraMap`
- `fracDeriv_add`
- `fracDeriv_mul`
- `fracDeriv_smul`
- `fracKDeriv`
- `fracKDeriv_apply`
- `fracKDeriv_algebraMap`

Impact:
- `wiki rdeps fracKDeriv --depth 3`: `fracKDeriv_lFrac`,
  `iterate_fracKDeriv_hFrac`, the Schultz catalog alias `eq_2_11_invariant`, and
  the moved local satellites.
- `wiki rdeps fracDeriv --depth 3`: only the moved satellites plus
  `fracKDeriv_lFrac` through `fracKDeriv_apply`.
- Direct import impact found by `rg`: `LaurentCoefficients/Base.lean` imports
  `DifferentialPolynomials` and uses `fracKDeriv`; it should import the new leaf.

Unify:
- None in this commit. This is a pure declaration relocation preserving names and
  proofs.

Steps:
1. Create `DiffPolyFractionDeriv.lean` importing `DifferentialPolynomials`.
2. Move the fraction-field derivation block unchanged.
3. Update `LaurentCoefficients/Base.lean` and the root aggregator import.
4. Gate the new module and `LaurentCoefficients.Base`.
5. Run the full gate, rebuild wiki graph, commit.
