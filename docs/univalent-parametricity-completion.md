# Section 3.3 univalent parametricity completion

Status: complete (2026-07-18)

## Objective

Complete the univalent half of Section 3.3 of *Trocq: Proof Transfer for Free,
Beyond Equivalence and Univalence* as a non-vacuous object-language
formalization.  The completed stack must expose the concrete `p□` and `pΠ`
packages, the package-to-relation projection, both translations from Figure 2,
Equation (17), and the full dependent abstraction theorem (Theorem 3.6).

The source catalog
`Sources/Doi_10_1145_3737283/Section33.lean` is the authoritative coverage
map.  A missing marker is deleted only after its corresponding declaration is
implemented and checked.

## Representation boundary

Native Lean cannot serve as the model of the paper's univalent universes:
`IsUnivalentUniverse` is inconsistent with Lean's proof-irrelevant equality.
The theorem is therefore proved syntactically for a dedicated extension
of the repository's CCω object calculus.  This keeps the result non-vacuous:
no declaration may be obtained from `False.elim`, an empty typeclass, or an
uninhabited quotation interface.

The extension treats the Section 3.3 package constructors as object-language
primitives with explicit typing, cumulative package formation, and computation
laws. This is necessary because the current core calculus has neither the sigma
types nor the equality types needed to expand the paper's package triples
internally. Separate semantic counterparts are constructed from the existing
relation algebra:

- `p□` is a primitive of the syntactic univalent calculus, while
  `univalentUniverseRelation` is its separately cataloged native counterpart;
- the semantic dependent-product package uses `StructuredRelation.pi` and its
  univalent conversion, separately from the syntactic `pΠ` constructor;
- `rel` is an explicit package projection and computes definitionally on both
  constructors.

The object calculus makes this boundary explicit. Its `relationProjection`
typing rule carries universe formation for both endpoints, and its
`Cumulative.packageType` rule states cumulative closure of package families.
These are primitive rules of the dedicated syntax, not consequences derived
inside core CCω. The abstraction theorem below is therefore a syntactic
metatheorem for that explicit extension. This development does not claim an
extended subject-reduction theorem, a denotational model proving those
primitive rules from Lean's native equality, or a theorem identifying the
syntactic constructors with their separate semantic counterparts.

The specialized Section 3.3 development must depend only on the core CCω,
relation, and raw parametricity layers.  Later annotated/Trocq machinery may be
used as a design reference, but it must not become a prerequisite for the
paper's earlier univalent theorem.

## Existing reusable infrastructure

- `Parametricity/Univalent/Package.lean`: `UnivalentRelation`, `rel`, and the
  universe package.
- `UnivalentRelationStructure.lean`: lossless conversion between univalent
  packages and top structured relations.
- `PiRelationStructure.lean`: dependent respectful relations and the
  equivalence/univalence closure used by `pΠ`.
- `Parametricity/Sequents/Univalent.lean`: the constructor-by-constructor
  Figure 2 shape, currently abstract over unrealized syntax constructors.
- `Parametricity/Raw/*`: raw syntax translation, renaming/substitution,
  formation typing, and abstraction infrastructure to reuse rather than clone.
- `Annotated/Quotation/*`: a later quotation design and projection beta laws;
  it is a reference for the specialized syntax, not its dependency root.

## Target module graph

1. `Parametricity/Univalent/Realizers.lean`
   - semantic dependent-product package;
   - concrete quoted `p□`, `pΠ`, and `rel` constructors;
   - definitional projection equations.
2. `Parametricity/Univalent/Translation.lean`
   - package-valued term translation `[t]` for every CCω constructor;
   - relation-valued type translation `rel ([A])`;
   - renaming and substitution compatibility.
3. `Parametricity/Univalent/Typing.lean`
   - typing rules for the extended primitives;
   - preservation for both Figure 2 translations;
   - Equation (17), including its judgment and definitional equality.
4. `Parametricity/Univalent/RelationalCumulativity.lean`
   - normalization of projected dependent-product relation fibers;
   - preservation of source cumulativity by applied univalent relations.
5. `Parametricity/Univalent/Abstraction.lean`
   - the full dependent fundamental lemma/abstraction theorem;
   - Theorem 3.6 as the paper-facing corollary.
6. `Parametricity/Univalent.lean`
   - ordered public aggregator for the completed stack.

If implementation reveals that renaming, substitution, or conversion forms a
cohesive independent unit, it may be split into one additional support module;
the public declarations and dependency order above remain unchanged.

## Required laws and completion evidence

### Phase 1: package realizers

- [x] Define the direct universe-polymorphic `UnivalentRelation.pi` package.
- [x] Prove that `(domain.pi fibers).rel` is definitionally the dependent
  respectful relation (`rfl`).
- [x] Define concrete object-language `p□`, `pΠ`, and `rel` terms.
- [x] Prove projection computation for `p□` and `pΠ` by definitional equality.
- [x] Check the semantic realizer module warning- and sorry-free.

### Phase 2: Figure 2

- [x] Translate sorts, variables, application, abstraction, and dependent
  products exactly as the package-valued column of Figure 2.
- [x] Define the relation-valued translation as projection from the package
  translation, not as an unrelated recursive function.
- [x] Prove renaming and substitution/naturality laws for both translations.
- [x] Provide constructor equations usable as rewrite rules.

### Phase 3: typing and Equation (17)

- [x] Extend judgments with non-vacuous typing rules for `p□`, `pΠ`, and
  projection while preserving the existing CCω rules.
- [x] Prove weakening, substitution, and conversion support required by the
  dependent proof.
- [x] Prove the translated universe package has the type stated in Equation
  (17), at the two indicated universe levels.
- [x] Prove `rel ([□ᵢ]) ≡ ⟦□ᵢ⟧ᵤ` as a definitional equality in the extended
  calculus.

### Phase 4: abstraction and cumulativity

- [x] Prove the fundamental lemma by induction on the full dependent CCω
  typing derivation, including sort, variable, application, lambda, Pi, and
  conversion and cumulativity cases.
- [x] State Theorem 3.6 using the paper's translated context, term, and type.
- [x] Ensure the theorem has no empty semantic or quotation assumptions.

### Phase 5: integration

- [x] Add the completed modules to the public aggregators.
- [x] Add anonymous signature restatements matching Figure 2, Equation (17),
  and Theorem 3.6.
- [x] Delete only discharged entries from the Section 3.3 source catalog.
- [x] Run affected-module gates, then bare `scripts/check.sh`.
- [x] Audit for warnings, `sorry`, axioms introduced only to close the result,
  and accidental dependencies on the later annotated stack.

## Guardrails

- Do not call an interface a realizer unless an inhabitant is constructed.
- Do not collapse Theorem 3.6 to the non-dependent intrinsic arrow fragment.
- Do not claim Equation (17) from a meta-level equality alone; its object-level
  typing judgment and conversion law are both required.
- Do not duplicate the raw renaming/substitution proofs when an existing lemma
  can be generalized or wrapped.
- Keep paper numbers and coverage language in `Sources/`; library declarations
  receive semantic names and concise API docstrings.
