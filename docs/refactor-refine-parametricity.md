# Refine parametricity module reorganization

The parametricity development was spread across flat `DeepWiki/Refine/` modules. Group the
translations, their metatheory, sequent presentations, quotation boundary, and intrinsic tutorial
under a sibling `DeepWiki/Refine/Parametricity/` area, following the existing `CCOmega/` pattern.

## Boundary

`CCOmega` is the object calculus. Parametricity consumes that calculus and therefore remains a
sibling area rather than becoming part of `CCOmega`. Preserve declaration namespaces and theorem
statements during mechanical path moves; module paths encode ownership, while declaration
namespaces continue to encode the mathematics. The intentional API retirements and semantic-helper
namespace changes made during the later ownership split are listed below.

The reusable relation algebra remains outside this area: `RelationStructure`, `TypeEquivalence`,
`FunctionalRelation`, `UnivalentRelationStructure`, `PiRelationStructure`, and
`UniverseRelationStructure` serve both parametricity and the later annotated Trocq calculus.

Paper numbers and coverage status remain only in `Sources/`. Do not introduce a `Section33` library
module.

## Target layout

```text
DeepWiki/Refine/
  Parametricity.lean
  Parametricity/
    Raw.lean
    Raw/
      Semantics.lean
      Translation.lean
      Typing.lean
      Conversion.lean
      Abstraction.lean
    Univalent.lean
    Univalent/
      Package.lean
      QuotationSpec.lean
    Sequents.lean
    Sequents/
      Raw.lean
      Renaming.lean
      RawCounterexample.lean
      Univalent.lean
    Intrinsic.lean
    Intrinsic/
      Core.lean
      Abstraction.lean
    SurfaceSyntax.lean
    Examples.lean

DeepWiki/Refine/Annotated/
  Quotation.lean
  Quotation/
    Syntax.lean
    Context.lean
    Typing.lean
```

Full univalent-parametricity work uses the semantic destinations reserved by this reorganization:

```text
Parametricity/Univalent/Realizers.lean
Parametricity/Univalent/Translation.lean
Parametricity/Univalent/Typing.lean
Parametricity/Univalent/Abstraction.lean
```

These modules now respectively contain the concrete `p□`/`pΠ` package constructors, Figure 2,
Equation (17), and full dependent Theorem 3.6; `RelationalCumulativity.lean` supplies the additional
conversion layer required by the abstraction induction.

## Mechanical move map

1. `RawParametricitySyntax` → `Parametricity/Raw/Translation`
2. `RawParametricityTyping` → `Parametricity/Raw/Typing`
3. `RawParametricityConversion` → `Parametricity/Raw/Conversion`
4. `RawParametricityAbstraction` → `Parametricity/Raw/Abstraction`
5. `ParametricitySequents` → `Parametricity/Sequents/Raw`
6. `ParametricitySequentRenaming` → `Parametricity/Sequents/Renaming`
7. `RawParametricityAbstractionCounterexample` →
   `Parametricity/Sequents/RawCounterexample`
8. `UnivalentParametricitySequents` → `Parametricity/Sequents/Univalent`
9. `CoreParametricity` → `Parametricity/Intrinsic/Core`
10. `UnivalentUniverseQuotation` → `Parametricity/Univalent/QuotationSpec`
11. `ParametricitySurfaceSyntax` → `Parametricity/SurfaceSyntax`
12. `Examples/ParametricityTranslations` → `Parametricity/Examples`
13. `StructuredUniverseQuotationSyntax` → `Annotated/Quotation/Syntax`
14. `StructuredUniverseQuotationContext` → `Annotated/Quotation/Context`
15. `StructuredUniverseQuotationTyping` → `Annotated/Quotation/Typing`

The `RawCounterexample` name is deliberate: it refutes the under-specified literal sequent claim,
not the successfully proved deterministic raw abstraction theorem.

## Semantic split

Retire the mixed `ParametricityTranslations` module by distributing its nonredundant declarations:

- raw universe semantics moves to `Parametricity/Raw/Semantics`; dependent-product semantics keeps
  using the shared `DependentRespectful` API in `Dependent`;
- the proof-relevant intrinsic kernel and intrinsic abstraction results move to
  `Parametricity/Intrinsic/Abstraction`;
- `BackwardEqualityGraph`, `UnivalentRelation`, Theorem 3.5, and the semantic universe package move
  to the dependency-leaf module `Parametricity/Univalent/Package`.

Do not retain forwarding aliases for exact duplicate APIs. Retire `RawPiRelation`,
`RawPiRelation.app`, and `RawPiRelation.lam` in favor of `DependentRespectful` and its existing
`app`/`lam` operations. Retire `CoreTerm.rawParametricity` in favor of the identical
`CoreTerm.abstraction`, and retire `CoreTerm.univalentAbstractionResult` in favor of the direct
`CoreTerm.rawAbstractionResult` specialization. Update the tutorial and source catalog to use the
canonical declarations.

This removes the current dependency inversion in which general structured-relation modules import
the intrinsic demonstration merely to obtain `UnivalentRelation`.

Keep the sequent modules syntactic. Move the semantic top-universe helpers
`universeRelationTop_fiber`, `universeRelationTopFiberEquiv`, and
`universeRelationTopFiber_characterization` from the sequent namespace to the root
`DeepWiki.Refine` namespace in `UniverseRelationStructure`. Move
`univalentDependentProductRelation` similarly to `PiRelationStructure`. These are deliberate
declaration-identity changes: their names now reflect reusable relation semantics rather than one
syntactic presentation.

## Quotation ownership

`Parametricity/Univalent/QuotationSpec` is the abstract object-calculus interface required by the
univalent translation. The `StructuredUniverseQuotation*` family is instead a concrete extension of
the annotated calculus, so it lives under `Annotated/Quotation/` and is not re-exported as though it
were the completed Section 3.3 implementation.

The quotation development currently has an early core-context `HasType` relation and a later
quotation-context typing relation. Treat the latter as the canonical direction. Consolidating the
former requires migrating its closed universe-equation consumers first and is a semantic follow-up,
not part of the path-only move.

## Phases and gates

1. Perform path-only moves, add ordered area aggregators, and update every import. Leave no
   forwarding shims.
2. Split `ParametricityTranslations` along the boundaries above and update direct consumers.
3. Move semantic helpers out of the sequent module and make quotation ownership explicit.
4. Build the leaf modules and aggregators in dependency order.
5. Run `scripts/check.sh DeepWiki.Refine.Parametricity`, then the relevant source-catalog targets,
   and finally bare `scripts/check.sh` serially.
6. Audit for stale old module paths, orphaned source imports, warnings, `sorry`, and obsolete build
   artifacts before declaring the migration complete.

## Completion

Completed on 2026-07-17. The flat modules have no forwarding module shims, all moved declarations
are reachable through the new aggregators, and both paper catalogs import the new ownership paths.
Subsequent work completed the full Figure 2 translation, object-level Equation (17), and dependent
Theorem 3.6 in those destinations and discharged their TOPLAS source-catalog markers. The original
reorganization itself remains a mechanical ownership change rather than that later formalization.

Verification passed for `DeepWiki.Refine.Parametricity`, `DeepWiki.Refine.Annotated.Quotation`,
the TOPLAS Section 3.3 catalog, the ESOP Section 2.3 and theory catalogs, `DeepWiki.Refine`, and the
full warning- and `sorry`-free `scripts/check.sh` gate. The declaration graph was rebuilt after the
move.
