# Primitive PRS regularity reorg

## Target modules

Split `DeepWiki.SymbolicIntegration.Computable.PrimPRSRegular` into focused
proof-stage modules under `DeepWiki/SymbolicIntegration/Computable/PrimPRSRegular/`:

- `Content`: nonzero leading coefficients, pseudo-remainder multiplier witnesses,
  and primitive-part associatedness.
- `Degree`: `t`-degree/normalized-length readings, single-step degree drop, inner
  pseudo-division termination, and primitive-part degree preservation.
- `Assembly`: the `CPrimPRSGenFuelOk` bookkeeping predicate, the
  `cPrimPRSGenAssocReg_of_regular_of_correct` reduction, and restatement examples.

Delete the old flat `Computable/PrimPRSRegular.lean` module and update the only
known importer, `Computable.lean`, to import `PrimPRSRegular.Assembly` directly.

## Declarations to move

`Content`:

- `toPolyG_gblcCore_ne_zero`
- `toGBCoeffPoly_gbpsremainderCore_ne_zero`
- `toGBPolyG_gbpsremainderCore_ne_zero`
- `associated_toGBPolyG_gbprimitivePartCore_total`

`Degree`:

- `natDegree_toGBCoeffPoly_le`
- `gbdegCore_eq_natDegree`
- `gbnormCore_length_eq_natDegree_succ`
- `toPolyG_gblcCore_eq_leadingCoeff`
- `gbStepReduce`
- `toGBCoeffPoly_gbStepReduce`
- `natDegree_gbStepReduce_lt`
- `gbisZeroCore_gbnormCore`
- `gbnormCore_length_pos`
- `toGBCoeffPoly_gbpsremainderCore_eq_zero_of_zero`
- `gbpsremainderCore_degree_lt`
- `natDegree_toGBPolyG`
- `natDegree_toGBCoeffPoly_gbprimitivePartCore`
- `gbnormGuard_iff_premDegree`

`Assembly`:

- `CPrimPRSGenFuelOk`
- `cPrimPRSGenAssocReg_of_regular_of_correct`

## `wiki rdeps` impact

`cPrimPRSGenAssocReg_of_regular_of_correct`, `gbpsremainderCore_degree_lt`, and
`gbnormGuard_iff_premDegree` currently have no direct downstream users outside
their restatement examples.

`toGBPolyG_gbpsremainderCore_ne_zero` is used by
`cPrimPRSGenAssocReg_of_regular_of_correct`.

`associated_toGBPolyG_gbprimitivePartCore_total` is used by
`cPrimPRSGenAssocReg_of_regular_of_correct` and
`natDegree_toGBCoeffPoly_gbprimitivePartCore`.

The only module import of the old flat file is `Computable.lean`.

## Unify list

- Keep primitive-PRS regularity proof stages under one `PrimPRSRegular/`
  namespace-directory.
- Keep executable `GBPolyCore` operations in their existing defining modules.
- Do not change declaration names or meanings.
- Do not leave a compatibility re-export at the old flat module path.

## Steps

1. Add `PrimPRSRegular/Content.lean`.
2. Add `PrimPRSRegular/Degree.lean`, importing `Content`.
3. Add `PrimPRSRegular/Assembly.lean`, importing `Content` and `Degree`.
4. Delete `Computable/PrimPRSRegular.lean`.
5. Update `Computable.lean` to import `PrimPRSRegular.Assembly`.
6. Gate the new assembly module and the full library, rebuild the wiki graph,
   and commit the split.
