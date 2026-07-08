# Subresultant PRS reorganization

## Target module

Split `DeepWiki.SymbolicIntegration.SubresultantPRS` into a compatibility aggregator plus leaf modules under
`DeepWiki.SymbolicIntegration.SubresultantPRS.*`.

## Declarations to move

- `SubresultantPRS.Telescope`
  - `isSimilar_subresultant_padding`
  - `subresultant_prs_similar`
  - `subresultant_prs_telescope`
  - `subresultant_prs_telescope_explicit`
  - `subresultant_prs_vanish`
- `SubresultantPRS.Remainder`
  - `subresultant_prs_similar_remainder`
  - `subresultant_prs_similar_remainder_top`
  - `subresultant_prs_similar_elt`
  - `subresultant_isSimilar_gcd`
  - `IsSimilar.exists_fractionRing`
  - `subresultant_prs_eq_fractionRing`
  - `subresultant_prs_similar_elt_top`
- `SubresultantPRS.ClosedForms`
  - `subresultant_eq_pseudoRem`
  - `subresultant_prs_closed_top`
  - `lc_prod_collapse_normal`
  - `subresultant_prs_normal_eq`
  - `shift_prod`
  - `beta_fold`
  - `lc_collapse_defective`
  - `subresPRS_gamma`
  - `subresPRS_beta`
  - `subresPRS_gamma_ne_zero`
  - `subresultant_prs_gap_zero`
  - `subresultant_prs_defective_eq`

## Impact

`scripts/wiki rdeps` shows the public declarations are used by the source catalogs and the subresultant-correctness wrappers:

- `subresultant_prs_telescope`: Loos/Brown-Traub/Singer catalogs and `SubresultantCorrectness.ChainEndpoint`.
- `subresultant_prs_similar_elt`: Loos/Singer catalogs, `ChainEndpoint`, and `PseudoRemainderSequence`.
- `subresultant_prs_normal_eq`: Singer catalog only.
- `subresultant_prs_defective_eq`: Collins/Loos/Singer catalogs.

Existing imports of `DeepWiki.SymbolicIntegration.SubresultantPRS` remain valid through the root aggregator.

## Unify list

- Keep all declaration names and theorem statements unchanged.
- Keep the public root import `DeepWiki.SymbolicIntegration.SubresultantPRS` as the downstream-facing API.
- Separate PRS telescope transport from endpoint/remainder bridges and from normal/defective closed-form algebra.

## Steps

1. Move the existing body under `SubresultantPRS/ClosedForms.lean` and make the root file an aggregator.
2. Gate the moved leaf and root import.
3. Split telescope declarations into `Telescope.lean`; import it from `ClosedForms.lean`; gate.
4. Split remainder/fraction-ring declarations into `Remainder.lean`; import it from `ClosedForms.lean`; gate.
5. Run downstream catalog/correctness gates, full `scripts/check.sh`, rebuild the wiki graph, and commit.
