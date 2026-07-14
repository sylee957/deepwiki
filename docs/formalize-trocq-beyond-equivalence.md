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

## Section 2 - proof transfer by example

- [x] Reuse the canonical unary/binary natural equivalence and its zero/successor laws.
- [x] Add binary multiplication and list product with unary-reading lemmas in the defining file.
- [x] Formalize Example 2.1's exact `[100, 101, 102]` ground-product comparison in both
  representations.
- [x] Implement direct binary strict comparison and prove its Boolean result agrees with `Nat`
  order; state the binary benchmark using that executable comparison.
- [x] Reuse the transferred binary eliminator and the weaker left-inverse construction for Example
  2.2.
- [x] Formalize Example 2.3's exact `23649 * 23703` computation modulo nine and the resulting
  integer divisibility theorem.
- [x] Prove the finite modular obstruction behind Example 2.4 by exhaustive computation in
  `ZMod 9`.
- [x] Transfer the obstruction back to prove Proposition 2.5 for arbitrary natural numbers.
- [x] Add a complete subtractive Section 2 catalog for DOI `10.1145/3737283`.

## Next phases

1. Audit revised Section 3 against the old `Section21`/`Section22`/`Section23` catalogs. Prefer new
   TOPLAS aliases for unchanged declarations; record only semantic differences as library work.
2. Treat Section 4 as the first likely refactor frontier: compare its operational sequents with
   `ParametricitySequents`, `UnivalentParametricitySequents`, and the erasure developments.
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
