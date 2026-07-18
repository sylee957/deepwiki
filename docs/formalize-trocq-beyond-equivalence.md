# Formalizing Trocq beyond equivalence and univalence

Source: Cohen, Crance, and Mahboubi, *Trocq: Proof Transfer for Free, Beyond Equivalence and
Univalence*, ACM TOPLAS 2025, DOI `10.1145/3737283`. The local reference is
`references/10.1145_3737283.pdf`, collected from HAL record `hal-05192017`.

This paper supersedes the ESOP 2024 paper as the main worklist, but it does not erase that paper's
catalog. Reuse the source-neutral theory already built under `DeepWiki/Refine/`, keep the ESOP
catalog as a historical map, and add TOPLAS aliases under `Sources/Doi_10_1145_3737283/`. Refactor
library declarations only when the revised paper exposes a genuinely more semantic API or a false
modeling assumption.

## Revised-paper map

- Section 2: four motivating transfer examples, including ground and quantified statements both
  within and beyond equivalence.
- Section 3: proof-transfer synthesis, equivalence, univalence, and raw/univalent parametricity;
  largely corresponds to old Section 2.
- Section 4: an operational account of parametricity translations and univalent parametricity
  sequents.
- Section 5: decomposition and reconstruction of type equivalence.
- Section 6: the relation hierarchy, annotated type theory, the Trocq calculus, conservativity,
  registered constants, and constraints.
- Section 7: plugin representation, synthesis, constraint solving, and constant handling.
- Section 8: the expanded application gallery for isomorphisms, sections/retractions, and
  polymorphic dependent types.

## Section 2 - intentionally decataloged

Section 2 was used as a reading exercise and its temporary Lean examples were removed afterward.
The TOPLAS source catalog intentionally claims no formalization coverage for Examples 2.1, 2.2,
2.3, and 2.4 or Proposition 2.5. Revisit them only if they become necessary tests for later Trocq
infrastructure.

## Section 3.1 - proof transfer in type theory

- [x] Reuse the intrinsically scoped `CCω` term and context grammars.
- [x] Internalize the exact context of source and target carriers, type formers, and relations.
- [x] Internalize `∀ s t, RInput s t → ROutput (V s) (W t)` and prove its formation judgment.
- [x] Reuse the semantic package synthesizing `W` together with its uniform relational witness.
- [x] Reuse the backward-arrow proof step, natural-number interfaces, and functional pullback
  boundary case.
- [x] Add revised-paper catalog pointers in `Sources/Doi_10_1145_3737283/Section31.lean`.

The catalog retains explicit markers for equality/sigma extensions of the object syntax and for
the implementation-only automation discussion; neither is silently counted as core `CCω` coverage.

## Section 3.3 - parametricity translations

- [x] Catalog the exact raw context equations (1) and (2): the empty context and one source
  declaration translated to its original, primed, and relation-witness triple.
- [x] Catalog the exact raw term equations (3) through (7): universes, variables, applications,
  lambdas, and dependent products in intrinsically scoped syntax.
- [x] Catalog Equation (8), proving that the translated universe has the displayed relation type
  one universe level higher.
- [x] Prove the formation-explicit abstraction theorem: all three displayed conclusions follow from
  the `FormationHasType` judgment.
- [x] Narrow ordinary `Cumulative` to the standard conversion, universe, dependent-product, and
  transitivity rules, retiring the unrelated lambda and structural-product closure rules.
- [x] Prove `isRelationallyCumulative_of_cumulative` for that ordinary relation and derive the
  unconditional `displayedRawAbstraction`, discharging the source-catalog marker for Theorem 3.4.
- [ ] Complete Figure 2 and unrestricted Theorem 3.6 after supplying object-language universe and
  dependent-product package realizers; retain their `[infra]` markers in the source catalog.

The formation-explicit theorem remains the proof factorization behind the unrestricted result.
Ordinary `CCω` cumulativity now preserves every substituted relation fiber, so ordinary `HasType`
embeds unconditionally into `FormationHasType` and Theorem 3.4 follows. The previous conditional
bridge and its lambda/structural-product gap were artifacts of an overly broad `Cumulative`
relation and have been retired. Figure 2 and Theorem 3.6 remain the next Section 3.3 boundary.

## Next phases

1. Audit revised Section 3.2 against the old `Section22` catalog. Prefer new TOPLAS aliases for
   unchanged declarations; record only semantic differences as library work.
2. Treat Section 4 as the first likely refactor frontier: compare its operational sequents with
   `Parametricity/Sequents/Raw`, `Parametricity/Sequents/Univalent`, and the erasure developments.
3. Audit Section 5 against `RelationStructure`, `FunctionalRelation`, `RelationEquivalence`, and
   `UnivalentRelationStructure`; retain the six-level API unless the revised symmetric presentation
   changes a theorem statement.
4. Audit Section 6 against the annotation lattice, dependency requirements, annotated calculus,
   recursive weakening, registered constants, and constraint solver. Separate mathematical
   theorems from plugin-only claims.
5. Catalog Section 7 implementation behavior with `[infra]` markers unless a claim has a stable,
   source-neutral executable Lean model.
6. Reconcile Section 8 with the old `Applications` catalog, adding revised examples and deleting a
   missing marker only when both the mathematical transfer and its exact displayed statement are
   present.
