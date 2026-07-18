# Raw parametricity organization refactor

## Goal

Separate the raw parametricity development by mathematical responsibility, retire declarations
that duplicate stronger existing APIs, and preserve the source-cataloged abstraction statements.

## Current pressure points

- `Raw/Typing.lean` combines translation naturality, relation normal forms, constructor typing,
  and abstraction-statement packaging.
- Relational cumulativity is divided between `Raw/Conversion.lean` and
  `Raw/Abstraction.lean`.
- `Raw/Abstraction.lean` combines the formation-explicit typing calculus, its structural
  metatheory, and the final abstraction theorem.
- Several local helpers duplicate either a bundled projection or a generic `CCOmega` theorem.

## Target module graph

```text
Raw.Translation
    |
    v
Raw.Naturality
    |
    v
Raw.RelationTypes
    |
    v
Raw.Typing ----------------------> Raw.FormationTyping
    |                                      |
    v                                      |
Raw.Conversion                             |
    |                                      |
    v                                      |
Raw.RelationalCumulativity ----------------+
    |
    v
Raw.Abstraction
```

`Raw.Abstraction` is the public theorem endpoint. `Raw.FormationTyping` remains a real proof
layer because lambda typing must expose codomain formation as an induction hypothesis.

## Retirement rules

Retire a declaration when one of the following holds:

- it repeats an existing bundled projection or stronger theorem exactly;
- it is an implementation-only induction helper and can become `private`;
- it is an unused theorem wrapper superseded by the final abstraction API;
- it is a generic `CCOmega` lemma currently misplaced under raw parametricity.

Do not retire beta-normal-form bridges, literal-to-normal conversion lemmas, symmetric
original/primed APIs, source-cataloged claims, or standard satellite operations merely because
the current reverse-dependency set is empty.

## Phases

### 1. Semantic cleanup in place

- Define `relationalSingleSubstitution` from `relationalSingle.relational`.
- Reuse the application codomain relation inside the product-fiber normal form.
- Remove the redundant `relationalSubtype` premise from formation-explicit cumulativity;
  derive it from `isRelationallyCumulative_of_cumulative` at the use site.
- Move generic two-sided conversion congruence into `CCOmega/Typing.lean`.
- Retire beta-only wrappers subsumed by conversion preservation.
- Make implementation-only congruence and fiber helpers private.
- Remove unused constructor-level abstraction wrappers and global proposition wrappers.
- Remove the unused witness-only claim package and its equivalence chain.

### 2. Split `Raw/Typing.lean`

- `Raw/Naturality.lean`: relational renaming, substitution, and instantiation.
- `Raw/RelationTypes.lean`: relation types, beta-normal presentations, and normalization
  bridges.
- `Raw/Typing.lean`: translated-context formation and original, primed, and witness typing for
  source constructors.
- `Raw/AbstractionClaims.lean`: displayed, full, and structural claim packages and equivalences.

Move declarations without changing theorem statements beyond the retirements from phase 1.

### 3. Split cumulativity and formation typing

- `Raw/RelationalCumulativity.lean`: relation-type conversion/cumulativity lemmas,
  `IsRelationallyCumulative`, and the induction from ordinary `Cumulative`.
- `Raw/FormationTyping.lean`: the formation-explicit judgments, renaming/substitution
  infrastructure, erasure, regularity, and embedding from ordinary typing.
- `Raw/Abstraction.lean`: the structural abstraction induction and exported final theorems.

The formation-explicit judgments are named `FormationWellFormed`, `FormationHasType`,
`FormationTypedRenaming`, and `FormationTypedSubstitution`, describing the judgments rather than
their consumer.

### 4. Imports and catalogs

- Update `Raw.lean`, downstream Refine modules, and both raw-parametricity source catalogs.
- Keep source pointers for `DisplayedRawAbstractionClaim`, conversion witness typing,
  relational cumulativity, formation-explicit typing, and the final abstraction theorem.
- Check that no source catalog or aggregator imports a removed module only for a retired helper.

### 5. Verification

- Run `scripts/check.sh` for each new or materially changed module in dependency order.
- Run `git diff --check`.
- Run bare `scripts/check.sh` as the final warning- and sorry-free gate.
- Inspect `git status --short` and keep unrelated work outside the refactor scope.
