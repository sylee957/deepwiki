# Differential Algebra Fraction-Field Uniqueness Cleanup

## Target module

`DeepWiki.SymbolicIntegration.Core.Differential.DerivationExt`

## Declarations to retire

- `derivation_fractionRing_unique_of_restrict`

## Impact

- `scripts/wiki rdeps DeepWiki.SymbolicIntegration.derivation_fractionRing_unique_of_restrict --depth 2`
  - `Sources.Doi_10_1007_b138171.Chapter3.ex_3_2_1`
  - `Sources.Doi_10_1007_b138171.Chapter3.ex_3_2_2`

## Unify list

- Use the existing core theorem `derivation_ext_fractionRing` for the source
  examples rather than keeping a duplicate wrapper in the worked examples file.

## Steps

1. Point the two source example aliases at `derivation_ext_fractionRing`.
2. Delete `derivation_fractionRing_unique_of_restrict`.
3. Gate `DifferentialAlgebraExamples` and the Chapter 3 source catalog.
4. Run the full gate, rebuild the wiki graph, and commit.
