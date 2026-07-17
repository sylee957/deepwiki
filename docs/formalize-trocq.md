# Formalizing the theory behind Trocq

> Historical ESOP 2024 worklist. The expanded TOPLAS paper now drives new work; continue from
> `docs/formalize-trocq-beyond-equivalence.md` and keep this file as the old paper's coverage record.

Source: Cohen, Crance, and Mahboubi, *Trocq: Proof Transfer for Free, With or Without
Univalence*, ESOP 2024, DOI `10.1007/978-3-031-57262-3_10`. The local reference is
`references/2310.14022v2.pdf`.

The rendered 29-page arXiv/ESOP paper ends after Section 6 and the references. Appendix 0.A-0.E
appears only in an unreachable arXiv source tail after `\end{document}`. It is supplementary audit
material here, not part of rendered-paper completion.

The supplementary constructions omitted from the PDF are in the official Trocq `0.1.5` artifact
(DOI `10.5281/zenodo.10563382`), especially `Hierarchy.v`, `Param_Type.v`, `Param_forall.v`, and
`Param_arrow.v`. Those files, rather than inference from the displayed tables alone, are the source
of truth for porting the `p□`, `pΠ`, and `p→` witness families.

The official repository is cached at `references/trocq-artifact`. The paper snapshot is tag
`ESOP2024` (`dd6ae95e39247d7df8c2f797e5d77f3d9f473943`); artifact release `0.1.5` is
`b5bd4bfcd7435b0cba121f9a7575a9fd97109af8`. Audit implementation claims against those tags, not
against current master, whose architecture and supported Rocq versions have continued to evolve.
The cached checkout currently points at `0.4.0`
(`a36529e66dfd3d255c51506943dbdac77adbee56`). In particular, its optional `(1,0)` coercion hook is
post-paper functionality and must not be attributed to the ESOP artifact.

The goal is a readable Lean development of the mathematical theory that explains Trocq, followed
by a deliberate comparison with `DeepWiki.Refine`. This is not initially a port of the Coq-Elpi
plugin. Each phase should leave named definitions, small theorems, and anonymous examples that expose
the paper statement in ordinary Lean.

## Reading map

- PDF pp. 5-6: the proof-transfer synthesis problem, induction example, and functional pullback.
- PDF pp. 6-7: type isomorphism, coherent equivalence, univalence, and equivalence transport.
- PDF pp. 7-8: raw and univalent parametricity translations.
- PDF pp. 9-11: functional relations, univalent maps, and the symmetric characterization of
  equivalence.
- PDF p. 12: the six one-direction map classes and their bidirectional product.
- PDF pp. 13-14: universe/product requirements and the motivation for annotation inference.
- PDF pp. 15-19: the annotated calculus and weakening of parametricity witnesses.
- PDF pp. 20-21: the Trocq abstraction theorem, recursive weakening, and registered constants.
- PDF pp. 22-26: plugin behavior and the six application case studies.

## Section 2.1 - proof transfer in type theory

- [x] Represent the recalled universe/variable/application/lambda/dependent-product term grammar.
- [x] Formalize proof transfer as synthesis of a target type former and a uniform relational witness.
- [x] Show how a target proof is transported back to the original source goal.
- [x] Package the carrier/zero/successor interface and transfer its induction principle across an
  interface equivalence.
- [x] Formalize the functional graph pullback `W = V ∘ φ` and prove that its transfer proof reduces
  to identity after substituting the graph equality.
- [x] Restate the structurally conjugated `W″` candidate and identify it definitionally with the
  functional pullback construction.

## Section 2.2 - type equivalence and univalence

- [x] Define pointwise equality and prove that it coincides with equality of functions.
- [x] Represent a type isomorphism by a forward map, inverse map, section, and retraction.
- [x] Represent the paper's coherence equation between section and retraction proofs.
- [x] Define `A ≃ B` in the paper's sigma form and prove it equivalent to Lean's bundled `Equiv`.
- [x] Prove that every two-sided isomorphism is coherently equivalent in Lean, where equality proofs
  are proof-irrelevant.
- [x] Prove explicitly that coherent equivalence evidence for a fixed map is proof-irrelevant.
- [x] Expose the forward and backward transport maps carried by a type equivalence.
- [x] Verify contravariant domain and covariant codomain transport for function types.
- [x] Formalize a univalent universe as an explicit coherent-equivalence hypothesis on the
  equality-to-equivalence map; do not add univalence as an axiom.
- [x] Prove that this hypothesis is uninhabited for Lean's standard proof-irrelevant universes,
  using the distinct identity and negation automorphisms of `Bool`.
- [x] Derive the paper's transfer principle `A ≃ B -> P A ≃ P B` and proof transport from that
  hypothesis.

Lean modeling caveat: the paper works in homotopy type theory, where identity types are
proof-relevant. Standard Lean equality is proof-irrelevant, so a universe-level inverse from all
equivalences back to equality would collapse the two automorphisms of `Bool`; the theorem
`isEmpty_isUnivalentUniverse` makes this incompatibility explicit. The univalent results below are
therefore conditional dependency checks, not an internal model of HoTT univalence. A semantic model
or a cubical/HoTT-flavored equality would be needed to instantiate them non-vacuously.

## Section 2.3 - parametricity translations

- [x] Formalize raw universe relations and the dependent product, application, and lambda rules.
- [x] Formalize the exact scoped context and term translations of Equations (2)–(8), including
  binder-safe Sort, variable, application, lambda, and dependent-product clauses.
- [x] Verify that the raw universe translation is itself a relation in the next universe.
- [x] Prove the exact universe, variable, application, and dependent-product witness cases of the
  scoped raw abstraction theorem, and prove the lambda case from the body witness plus the
  translated product-type witness.
- [x] Represent translated contexts by paired environments carrying proof-relevant witnesses.
- [x] Prove raw abstraction by structural induction for the intrinsic function fragment.
- [x] Package the two typed term interpretations and their translated witness as the three
  conclusions of the abstraction theorem.
- [x] Formalize the univalent universe package `Σ R, Σ e, R ≃ graph(e⁻¹)`.
- [x] Prove that this package is equivalent to type equivalence under an explicit univalence
  hypothesis.
- [x] Separate the package-valued term translation from its relation-valued type projection.
- [x] Construct the native semantic translated-universe package and verify its relation projection
  definitionally.
- [x] State the exact quoted-universe boundary as `UnivalentUniverseQuotation`, indexed by an
  explicit extension of object-language typing and definitional conversion; its fields record the
  package typing and projected-relation conversion without identifying the native semantic package
  with an object-language term.
- [x] Realize the top/top quoted-universe equation in `StructuredUniverseQuotationSyntax`: the
  primitive structured witness has its displayed type, its projected relation has the top family
  type, and projection converts definitionally to the quoted top relation family. Relate each
  native top-universe fiber to both `StructuredRelation` at `(4,4)` and `UnivalentRelation` without
  asserting the still-open full univalent abstraction induction.
- [x] Prove the univalent abstraction result for the intrinsic function fragment.
- [x] Prove all three raw abstraction conclusions for a formation-explicit dependent judgment whose
  lambda rule recursively supplies codomain formation and whose cumulativity rule records exact
  substitution-stable relation-fiber monotonicity; prove its erasure into ordinary `CCω`
  typing. Add typed renaming, weakening, substitution, instantiation, lookup regularity, and assigned
  type regularity for this judgment.
- [x] Prove relational-fiber monotonicity for every ordinary `Cumulative` constructor—conversion,
  universe lifting, products with convertible domains and cumulative codomains, and transitivity—
  and lift ordinary typing into the formation-explicit judgment. Raw abstraction for ordinary
  `CCω` typing is therefore unconditional.

## First checkpoint: what the six levels mean

Fix a proof-relevant relation `R : A -> B -> Sort w` and a candidate map `m : A -> B`. There are
two logically different comparisons between `R a b` and the graph equation `m a = b`:

```text
G2a m R := forall a b, m a = b -> R a b
G2b m R := forall a b, R a b -> m a = b
```

`G2a` says that every graph pair is related, so the graph of `m` is contained in `R`. `G2b` says
that every related pair lies on the graph, so `R` is contained in the graph. Neither implication
contains the other; this is why Trocq has two incomparable level-2 nodes.

The six one-direction classes are then:

| Level | Data carried in the direction `A -> B` |
|---|---|
| `0` | only `R` |
| `1` | a map `m : A -> B` |
| `2a` | `m` and `G2a m R` |
| `2b` | `m` and `G2b m R` |
| `3` | `m`, `G2a m R`, and `G2b m R` |
| `4` | level `3` plus witness coherence `G2a (G2b r) = r` |

Level `3` makes `R a b` logically equivalent to `m a = b`; level `4` also preserves the identity
of a proof-relevant witness during the round trip. This last distinction disappears easily for
`Prop`-valued relations because proofs are proof-irrelevant, but it matters for Trocq's
`Type`-valued relations.

An annotation is a pair `(n, k)`: level `n` for `R` in the forward direction and level `k` for
`Converse R` in the backward direction. Two level-`3` directions already provide maps `f : A -> B`
and `g : B -> A`. The graph laws prove `g (f a) = a` and `f (g b) = b`, which is why
`BiMapClass3.toEquiv` constructs a Lean `Equiv A B`.

Our existing `DenoteRel denote c a := denote c = a` is the graph relation of `denote`. Therefore it
has a canonical forward level-`4` structure: both graph comparisons are the identity function, and
the coherence proof is reflexivity. What the existing refinement kernel lacks is the independently
tracked converse level and the inference of the minimal pair `(n, k)` required by a term.

## Phase 1 - relation structures

- [x] Define converse relations.
- [x] Define the graph-to-relation and relation-to-graph directions.
- [x] Define `MapClass0`, `MapClass1`, `MapClass2a`, `MapClass2b`, `MapClass3`, and `MapClass4`.
- [x] Define the six-level index and the bidirectional level-`3` class.
- [x] Define the field-for-field structured-relation carrier `Σ R, RelationClass α R`, its
  projections, converse symmetry, and structure-preserving weakening. Lean conservatively
  generalizes the artifact's same-universe `Type` carriers to heterogeneous universes and `Sort`.
- [x] Define the primitive weakening projections between adjacent map classes.
- [x] Show that `DenoteRel denote` carries a canonical forward `MapClass4`.
- [x] Show that two `MapClass3` directions determine a Lean equivalence of carriers.

## Phase 2 - the partial order and generic weakening

- [x] Formalize `0 < 1 < 2a < 3 < 4` and `0 < 1 < 2b < 3 < 4`, with `2a` and `2b`
  incomparable.
- [x] Define the universe-polymorphic `RelationClass (m, n) R` family without collapsing
  proof-relevant relations to `Prop`.
- [x] Prove that the product order is a partial order on annotations.
- [x] Equip the level diamond and its annotation product with lawful bounded lattice operations,
  including `2a ⊔ 2b = 3` and `2a ⊓ 2b = 1`.
- [x] Define a type-correct generic weakening operation for every comparable pair.
- [x] Match Definition 9's componentwise weakening of bidirectional relation classes exactly.
- [x] Restate the paper's named dictionary entries, including `(4, 2a)`, `(4, 2b)`, `(3, 3)`,
  and `(4, 4)`.

## Phase 3 - functional relations and equivalence

- [x] Formalize `IsFun R := forall a, IsContr (Sigma fun b => R a b)` in a proof-relevant universe.
- [x] Construct a univalent map from a functional relation and conversely.
- [x] Formalize the exact function/functional-relation equivalence under an explicit univalence
  hypothesis, rather than silently adding univalence as a Lean axiom.
- [x] Formalize the exact symmetric two-direction characterizations of equivalence, both through
  `IsFun` and through level-`4` univalent-map data, under the same explicit hypothesis.
- [x] Keep the constructive carrier and inhabitedness directions available without univalence.
- [x] Isolate where proof relevance matters: for `Prop`-valued relations the `MapClass4` coherence
  field follows from proof irrelevance, while for `Type`-valued relations it carries data.

## Phase 4 - dependent respectful products

- [x] Define the dependent relational interpretation of `forall x : A, B x`.
- [x] Recover `DeepWiki.Refine.Respectful` as the nondependent specialization.
- [x] Formalize application and lambda rules for the dependent relation.
- [x] Add lifted relations for dependent pairs and `List`, including transfer of `List.map`.
- [x] Transcribe the complete, distinct `D_Π` and `D_→` requirement functions from the six
  one-sided rows and prove their bidirectional reconstruction formulas.
- [x] Prove all six product rows and all six coherence-preserving arrow rows least for their finite
  constructor-feature constraints, separating this from stronger semantic impossibility claims.
- [x] Port the six atomic non-dependent arrow map-class constructors, including proof-relevant
  level-`4` coherence.
- [x] Assemble the atomic arrow constructors into every bidirectional annotation witness.
- [x] Expose the native-Lean UIP divergence: arrow level `4` needs only domain level `3`, so the
  coherence-preserving domain-level-`4` row is not minimal for Lean `Eq`.
- [x] Port the six atomic dependent-product map-class constructors.
- [x] Assemble the dependent-product constructors into every bidirectional annotation witness.

## Phase 5 - annotated calculus

- [x] Formalize the paper's admissible universe-annotation predicate `D_□`.
- [x] Construct the axiom-free weak-target universe witnesses with definitional relation
  projections.
- [x] Construct the univalent top-source universe witnesses for the remaining admissible targets
  and combine both branches into the complete `D_□`-indexed family.
- [x] Define intrinsically scoped raw dependent terms and contexts with binder-safe renaming,
  simultaneous substitution, lookup, and their identity/composition/fusion laws.
- [x] Add well-formedness, dependent typing, conversion, and ordinary cumulativity for the scoped
  calculus. `Cumulative` has exactly conversion, universe lifting, invariant-domain dependent
  products, and transitivity; application covariance, lambda covariance, and contravariant product
  domains are not ordinary cumulative constructors.
- [x] Prove typed renaming, weakening, simultaneous substitution, instantiation, and their
  preservation of beta conversion, cumulativity, context well-formedness, and typing.
- [x] Add annotations, binder-safe erasure, and the complete displayed `CCω⁺` subtyping and typing
  judgments with `D□`, `D→`, and `DΠ` side conditions.
- [x] Define the annotation-free judgments obtained by literally erasing Figures 5 and 6, and
  prove mutually that erasure preserves context formation, typing, and every subtyping derivation.
- [x] Erase every annotated context, typing, and subtyping derivation into the literal
  annotation-free Figures 5 and 6 calculus.
- [x] Keep the literal erasure calculus separate from ordinary `CCω`: its `Subtype` judgment has
  structural application, lambda, and contravariant-product rules that ordinary `Cumulative` does
  not. Exact annotated erasure lands in `UnderlyingDependentCalculus`, not directly in ordinary
  cumulative typing.
- [x] Retire the false context-free bridge from structural `Subtype` to ordinary `Cumulative`, the
  conditional embedding built on it, and the dead application-transport scaffold.
- [x] Audit source-tail 0.B's printed `|Γ| ⊢ |t| ≡ |A|` conclusion and refute it formally with the
  annotated derivation `Sort 0 : Sort 1`; the repaired conservativity conclusion is typing.
- [x] Prove parallel-beta substitution, complete-development triangle/diamond, Church-Rosser
  joinability, distinct-sort nonconversion, and sort/product kind disjointness for the ordinary
  scoped calculus.
- [x] Prove dependent context narrowing unconditionally by a typed identity substitution, and reduce
  conversion regularity to assigned-kind/sort discrimination. Prove the product construction from
  reverse domain typehood transport, narrowing, and forward codomain transport.
- [x] Prove constructor-local principal typing and beta-convertible product injectivity. Formalize
  the source tail's false subtyping-as-beta-conversion claim and refute it with `Sort 0 ≤ Sort 1`;
  do not replace it by a context-free cumulative claim for the structurally stronger erased
  subtyping judgment. Remove the superseded conditional product-fork and assigned-type-lower-bound
  route.
- [x] Prove that erasing universe indices maps cumulative conversion to beta conversion and prove
  directly that any two types assigned to one term agree after level erasure. This closes
  assigned-kind discrimination and typed conversion regularity unconditionally.
- [x] Prove cumulative product-target shape preservation through transitive paths, derive convertible
  domains and cumulative codomains, and prove root-beta and compatible one-step subject reduction
  unconditionally.
- [ ] If the repaired source-tail conservativity result is pursued directly, interpret the literal
  erased typing and structural-subtyping derivations into ordinary typing using their typing premises
  constructor by constructor. This must be a typed, derivation-indexed theorem rather than an
  untyped structural-subtyping-to-cumulativity map; arbitrary application-spine transport and
  substitution stability remain part of the supporting metatheory.
- [x] Represent annotated universe levels and annotated types for a documented core fragment.
- [x] Represent semantic parametricity contexts for an intrinsically typed lambda calculus.
- [x] Formalize weakening of witnesses through the documented core types, including the
  contravariant domain and covariant codomain rule, and combine it with annotation weakening.
- [x] State and prove the fragment's abstraction theorem by induction on intrinsically typed terms.

## Section 4.1 - raw parametricity sequents

- [x] Formalize parametricity contexts as duplicate-free triples of original, primed, and witness
  variables.
- [x] Transcribe every rule of Figure 3 as an intrinsically scoped derivation judgment.
- [x] Formalize Definition 8 with the paper's exact lookup equalities.
- [x] State Theorem 4 with its two typing conclusions.
- [x] Audit Lemma 5 against the literal lambda rule and exhibit a closed counterexample to
  functionality caused by its unconstrained primed and witness domains.
- [x] Refute the literal Theorem 4 itself with a closed, well-typed source lambda: choose a dependent
  product as its unconstrained primed binder while the independent type sequent expects a universe
  binder, then use cumulative-level erasure and product injectivity to refute the required typing.
- [x] Define the minimally repaired domain-coherent judgment and prove its translation functional.
- [x] Remove the abandoned constructor, strengthening, and typing-reflection scaffold: it targeted a
  conditional repair of an already false theorem and no completed abstraction result consumed it.
- [ ] State a repaired sequent abstraction theorem over `CoherentRawSequent` and prove its own typing
  induction. The literal Figure 3 theorem cannot be repaired by an auxiliary premise alone because
  its lambda constructor omits the domain translation data.

## Sections 4.2-4.5 - univalent sequents and Trocq

- [x] Transcribe Figure 4 as a scoped univalent-parametricity judgment with explicit realizers for
  the object-language `p□` and `pΠ` constants, and prove functionality for fixed realizers.
- [x] State Theorem 5 with an explicit universe-univalence hypothesis and verify Remark 3
  semantically as the top relation fiber `Σ R, IsUmap R × IsUmap (Converse R)`.
- [x] Transcribe every Figure 7 Trocq rule in
  `DeepWiki/Refine/AnnotatedRelationTranslation.lean`, including `D□`, `D→`, `DΠ`, and conversion
  weakening.
- [x] Prove that parallel primed syntax is structurally the source syntax and reduce both the
  legacy and context-realized Theorem 6 schemas exactly to structured-witness typing.
- [x] Prove that source-only contexts cannot reconstruct omitted binder witnesses, then define
  `ContextRealization` with explicit primed types and witnesses and construct its three-copy
  typing context.
- [x] Isolate explicit `RelationFieldQuotation` and `QuotationBackedBridge` interfaces for the
  paper's `rel(A_R) M M'` conclusion. These currently state syntactic alignment, not typed
  quotation laws.
- [x] Add a genuine intrinsically scoped syntax extension with relation families, structured
  universe witnesses, and primitive `rel` projection; prove its typing, projection reduction,
  binary-application congruence, and quotation-aware lambda-binder laws. Prove that the new
  primitives lie outside the embedded core-syntax image.
- [x] Prove that the canonical `rel(A_R) x x'` binder itself is not core-representable, which
  formally rules out hiding the missing Theorem 6 context extension inside the old core syntax.
- [x] Extend dependent contexts over the quotation syntax and build each realized source extension
  as the faithful triple `x : A`, `x' : A'`, `x_R : rel(A_R) x x'`, with the expected newest-lookup
  equation.
- [x] Add a conservative extended-context typing fragment and prove that a typed structured witness
  makes `rel(A_R) x x'` a context-entry type, that the resulting three-binder context is well formed,
  and that `x_R` has its stored type by variable lookup. The exact bridge identifies this context
  with one `ContextRealization` extension. Relation-fiber universe levels remain erased by the
  current `relationType` syntax, so this is not yet full Figure 7 typing.
- [ ] Make quotation-valued contexts canonical once the extended typing relation covers every core
  constructor; then retire the older core-context-only `HasType` fragment instead of maintaining two
  context and typing architectures.
- [x] Isolate the universe-witness consequences of the abstraction claim in
  `DeepWiki/Refine/UniverseWitnessConsequences.lean`.
- [x] Formalize all five Figure 8 recursive weakening equations as object-language definitional
  convertibilities at the scoped syntax boundary, plus executable semantic universe and
  dependent-product weakening. Raw syntax equality is too strong: even the identity equation is
  refuted by `noSyntacticIdentityTransformer`, while the quoted identity lambda satisfies it by
  beta conversion.
- [x] Index the five equations directly by a proof-relevant mirror of actual annotated subtyping;
  prove coverage of every subtyping constructor and erasure back to the original judgment.
- [x] Separate atomic identity from equal composite conversion and distinct beta-convertible
  endpoints; exhibit a well-typed beta-redex showing that the five structural equations are not a
  total conversion rule.
- [x] Isolate paired-endpoint substitution as extra data not supplied by lambda subtyping alone, and
  package typed weakening realizers that induce the translation realizer interface after selecting
  an index.
- [ ] Quote and type application, paired-endpoint substitution, and dependent-product transformers
  on the supported typed fragment; add a normalization- or quotient-compatible conversion clause
  and extend atomic fallback to the constant-aware calculus.
- [x] Separate the paper-oriented application constructor from the artifact's partial evaluator.
  The ESOP implementation returns identity for applications headed by a variable or global, suspends
  a lambda as `wsuspend`, resumes that suspension after endpoint substitution, and recurses by
  variance through products; it does not apply an arbitrary recursively weakened family witness to
  every application. `MetaWitnessWeakeningEvaluator` implements the clause order of
  `ESOP2024/elpi/param.elpi:217-246` over constant-aware syntax, records ready and suspended states,
  gives a proof-relevant sound trace and deterministic outputs, and rejects an explicit unsupported
  composite.
- [ ] Connect every successful artifact-evaluator trace to annotated subtyping and a typed quoted
  witness transformer; this typed soundness statement is deliberately not claimed by the untyped
  operational model.
- [x] Formalize Figure 9 constant type collections, common erasure, the functional partial lookup,
  and its exact missing-entry stuck condition. Registry completeness is not asserted by the paper.
- [x] Separate source-type lawfulness from translation-output lawfulness. A successful lookup now
  types its primed output at the selected translated type and its witness at the explicitly quoted
  relation type, relative to a coherent realization carrying the omitted binder translations.
  Prove the complete Figure 9 constant branch from these non-circular laws and the translation of
  the selected source type; source-only recovery of the omitted relation witnesses is refuted.
- [ ] Prove Theorems 5 and 6 after extending the conservative projected-binder typing fragment to
  the complete universe-aware annotated calculus, supplying typing and conversion laws for every
  `SyntaxRealizers` field, lifting the existing quotation-aware lambda constructor into the actual
  Figure 7 judgment, and completing the realized witness-typing induction. Native Lean also cannot
  inhabit the paper's full universe-univalence premise.

## Appendices - erasure and maximality

- [x] Prove source-tail 0.B annotation erasure for contexts, typing, and subtyping into the literal
  annotation-free calculus.
- [ ] Complete the repaired source-tail 0.B conservativity theorem with a direct typed interpretation
  of the literal annotation-free Figures 5 and 6 judgments into ordinary `CCω` typing. Context
  narrowing, assigned-kind discrimination, typed conversion regularity, canonical-beta preservation,
  cumulative product inversion, and compatible one-step subject reduction are available, but no
  complete embedding is currently claimed.
  The paper's printed beta-conversion conclusion is false and already has a formal counterexample.
- [x] Construct the erased parameter context, recursively project relation records with `rel*`, and
  map every annotated synthesis derivation to a raw sequent under explicit `ErasureLaws` for the
  opaque witness realizers.
- [x] Construct an erasure-only structural projection and prove its recursive projection law.
  Construct `canonicalRawRealizers` by maximally annotating canonical raw witnesses and prove the
  full `ErasureLaws` interface directly.
- [x] Connect the genuine universe-witness primitive and its relation-field projection to raw
  erasure. The projected witness reads back as the canonical raw universe relation and agrees
  exactly with `canonicalRawRealizers`.
- [ ] Complete the quotation-faithful source-tail Theorem 0.C.1 by extending the realizer interface
  and connecting genuine typed arrow, product, and weakening witnesses to the erasure laws. The
  typed projected-binder context and universe fragment are available, but do not yet constitute
  the complete constructor induction.
- [x] Formalize source-tail 0.D's maximal annotation function on terms, substitutions, and contexts;
  prove naturality for renaming, substitution, instantiation, and lookup, and prove erasure is a
  left inverse.
- [x] Lift every context-formation, typing, and subtyping derivation of the literal unannotated
  calculus to the maximally annotated calculus.
- [x] Construct the canonical source-context bridge, prove that its erasure is exactly the
  canonical triple context, and prove maximal correspondence for universes, variables,
  applications, lambdas, products, conversions, and arrows under explicit realizer agreement.
- [x] Remove the unrestricted-scope counterexample scaffold and state correspondence only for the
  canonical source-generated contexts and constructors used by source-tail 0.D.
- [ ] Assemble source-tail Theorem 0.D.1 over canonical source-generated derivations after adding
  typed realizer laws.

## Section 4.5 - registered constants

- [x] Represent a global constant's family of annotated type choices.
- [x] Require all annotated choices for one constant to share the same erasure.
- [x] Register a synthesized target term and witness term for every annotated choice; outputs are
  not restricted to constant names because the paper's list witness is a lambda term.
- [x] Formalize both constant rules of Figure 9 and prove the common-erasure invariant for their
  typing derivations.
- [x] Construct recursive annotated and erased syntax parameterized by global constants, including
  renaming, substitution, contexts, beta conversion, kinds, the full typing/subtyping rules, and the
  complete sort/variable/application/lambda/arrow/product/conversion/constant synthesis judgment.
  Registered target and witness outputs are arbitrary closed terms weakened into the local scope;
  this follows Figure 9's mathematical term rule but is more general than the tagged artifact's
  global-reference database.
- [ ] Factor the constant-free and constant-aware calculi through one syntax parameter and an
  explicit embedding law package, instead of duplicating renaming, substitution, contexts,
  conversion, typing, and subtyping in `RegisteredConstantSyntax`.
- [x] Add a separate `LawfulTranslationEnvironment` package: relative to an explicit relation-type
  quotation, coherent context realization, and translation of the selected source type, each lookup
  types its primed and witness outputs and proves all three constant-abstraction conclusions.
- [x] Enrich annotation-only `D_K` rows with source constant, annotated type, target, and witness
  payloads; prove that erasing the payload gives exactly the existing constraint semantics; and
  formalize the complete family obtained by weakening one witness to every strict lower output.
- [x] Prove the exact recursive-lookup boundary: because `Environment.translation` is keyed only by
  source and annotated type, it realizes a weakened row in addition to the base row exactly when
  witness weakening is syntactically fixed, and cannot hold two distinct weakened witnesses.
- [ ] Realize payload-level witness weakening by the typed quoted transformer and connect its rows
  to `LawfulTranslationEnvironment`; model the plugin command's duplicate-row suppression separately.

## Phase 6 - connect the theory to the existing resolver

- [x] Relate `Subsumes` to lattice weakening: it changes the relation covariantly and therefore
  preserves the `2a` graph-to-relation branch, whereas annotation weakening fixes the relation and
  forgets structure. The dual relation map preserves the `2b` branch contravariantly.
- [x] Generalize the resolver with the lambda rule justified by the formalized relational calculus.
- [x] Add nondependent binder transfer using explicit local relation hypotheses; dependent binder
  transfer remains represented in the kernel but is not yet exposed through elaborator automation.
- [x] Exhibit the current resolver as the multisorted arrow fragment of the relational calculus,
  including exact polynomial operations and the mixed exact/associated `gcd` witness.
- [x] Implement annotation inference as a separate proof-producing decision procedure
  (`Annotation.canWeaken` / `RelationClass.weaken?`); elaborator automation may call it, while the
  mathematical kernel remains independent of tactic and typeclass search behavior.
- [x] Formalize the supplementary implementation appendix's finite constraint language with
  constant/variable graph nodes, exact calculus equations, and the artifact's lower-bound
  reductions for `D_→` and `D_Π`.
- [x] Prove that exact constructor constraints imply their artifact relaxations and formally show
  the converse fails already for one arrow constraint.
- [x] Implement an executable finite-domain reference solver returning every componentwise-minimal
  assignment, and prove its membership, soundness, satisfiability-completeness, and least-solution
  uniqueness specifications.
- [x] Implement the artifact's output-first dependency graph, reversed-Kahn order, and stepwise
  least-upper-bound instantiation for order, universe, arrow, product, and registered-constant
  constraints; certify every successful result against the original denotational system and prove
  that it belongs to exhaustive search.
- [x] Characterize graph success exactly as certification of its single propagated candidate and
  formally refute general completeness and leastness. Duplicate-output first-match `D_K` rows can
  reject satisfiable systems or return nonminimal solutions; unconstrained registered outputs are
  not inferred; exact arrow/product equations are unsupported until explicitly relaxed.
- [x] Enrich Lean's `D_K` rows with the source constant, annotated type, target, and witness payload
  carried by the artifact graph, prove exact projection to annotation-assignment semantics, and
  prove the conditional boundary for representing output-indexed rows in the current lookup.
- [ ] Index recursive translation lookup by the selected output annotation, or prove a typed
  quotient making every generated witness equal; then connect row selection to translation
  lawfulness rather than only annotation-assignment soundness.

## Phase 7 - motivating examples and case studies

- [x] Formalize unary and canonical binary naturals, their inverse conversions, successor square,
  and dependent induction transfer in both directions (Example 1).
- [x] Formalize finite summable nonnegative sequences, their extension into arbitrary `ENNReal`
  sequences, the operation witnesses, and transferred sum additivity (Example 2 / Equation (1)).
- [x] Formalize the Section 5.1 bitvector representation and registered `get`/`set` witnesses,
  including the displayed transfer direction from bounded naturals to vectors.
- [x] Formalize the Section 5.1 retractive natural-induction example at the selected `(2a,3)`
  structure; automatic weakest-annotation inference remains tactic engineering.
- [x] Formalize the Section 5.2 modular-arithmetic retraction example, including the exact
  three-variable implication without prime or nonzero-modulus assumptions.
- [x] Formalize the Section 5.2 nested summable-sequence refinement example and both displayed
  additivity lemmas.
- [x] Formalize the Section 5.3 polymorphic-list relation lifts and the exact top-lookup weakening
  obstruction; automatic annotation-aware selection remains tactic engineering.
- [x] Formalize the Section 5.3 dependent-vector example, including the simultaneous
  integer-to-modular container retraction and both displayed head/constant laws.

The checked case-study items cover their mathematical relations, witnesses, and conclusions.
The finite annotation-constraint problem now has an executable verified reference solver and a
sound executable graph reducer. The optimized reducer's general completeness and leastness are
formally false, not unproved; `Trocq Use` and automatic tactic rewriting remain plugin-engineering
work and are recorded separately rather than silently counted as formalized.

### Case-study statement audit against pp. 22–26

- **Bitvectors:** `BoundedNat k = Fin (2^k)` and `BitVector k = Vector Bool k`; the width,
  `get`, and `set` witnesses retain the paper's dependent width relation and ordinary natural
  indices. The displayed in-range get-after-set conclusion is present in both source and target
  representations. The bounded-natural operations are direct: reads use guarded `Nat.testBit`, and
  writes use conditional XOR with `2^index`. Their get-after-set law is proved from the natural-bit
  lemmas before the commuting witnesses transport it to Boolean vectors.
- **Retractive induction:** the generic carrier relation has exactly annotation `(2a,3)`, assumes
  the one inverse law actually needed together with zero/successor squares, and produces the full
  dependent eliminator rather than only a non-dependent induction lemma.
- **Modular arithmetic:** the theorem retains all three quantified variables and the displayed
  product equation `m = n * p`, assumes no primality or nonzero-modulus condition, and concludes
  equality after reduction to `ZMod`; the relation has the displayed `(4,2a)` retraction structure.
- **Summable sequences:** both the finite-value and sequence layers carry `(4,2b)`, truncation sends
  the extra infinite value to zero, and both displayed additivity statements are present with the
  value, pointwise-addition, and summation witnesses kept separate.
- **Polymorphic lists:** both the top lift and the weaker `(2a,4)` lift are constructed. The failed
  top-only lookup is proved as the exact lattice obstruction `¬ (4,4) ≤ (2a,4)`, rather than being
  described only as a tactic failure.
- **Dependent vectors:** iterated tuples use the paper's `unit`/product recursion and are equivalent
  to fixed-length vectors; the source vector `head (const i)` law transfers to the modular tuple
  law using only the integer-to-modular retraction on elements, with separate `head` and `const`
  witnesses.

## Full-paper completion contract

The earlier intrinsic-core checkpoint is not full-paper completion. The formalization is complete
only when the source-neutral library and DOI catalog account subtractively for every numbered
definition, lemma, theorem, equation, and rule-bearing figure in the paper. In particular it must:

- define the full `Σ R, RelationClass α R` structured-relation carrier;
- formalize `D_□`, the distinct complete `D_Π` and `D_→` dependency tables, and their minimality
  claims;
- replace the placeholder annotated types with scoped dependent `CCω`/`CCω⁺` terms, renaming,
  substitution, conversion, typing, erasure, and annotated subtyping;
- formalize the raw, univalent, and Trocq sequent judgments, formally refute any ill-scoped or false
  printed statement, and prove the strongest faithful repaired form of Lemma 5 and Theorems 1–6 by
  induction on their actual derivations;
- construct the universe, dependent-product, and arrow witnesses with the definitional relation
  projections required by Equation (12);
- implement Figure 8 witness weakening by recursion on type/subtyping derivations, not merely by
  forgetting relation metadata;
- represent registered constants and formalize the mathematical claims in both numbered examples
  and the Section 5 case studies, while classifying plugin-only engineering claims as executable
  tests rather than mathematical theorems.

Every landed frontier must pass `scripts/check.sh`; source provenance, paper numbering, and all
remaining-item status stay in the DOI catalog rather than the source-neutral library.

## Faithfulness audit findings

These are semantic discrepancies that must remain visible rather than being hidden by similarly
shaped Lean declarations.

- **Native Lean is not a model of the paper's univalent universes.** Proof-irrelevant `Eq` makes
  `IsUnivalentUniverse` empty, witnessed by the two distinct automorphisms of `Bool`. Results that
  depend on univalence are therefore conditional signature checks.
- **Figure 3 is under-specified when read literally.** `ParamLam` contains no premise translating
  its domain, so its displayed `A'` and the type of `x_R` are unconstrained. The literal inductive
  judgment has a closed counterexample to Lemma 5. More strongly, `not_rawAbstractionClaim`
  constructs all premises of the printed Theorem 4 while making its primed lambda conclusion
  untypable, so the literal theorem is false as well. `CoherentRawSequent` restores the omitted
  domain premise and satisfies functionality.
- **Raw abstraction is unconditional for ordinary `CCω` typing.** `AbstractionHasType` recursively
  exposes the type witnesses consumed by lambda and conversion and records fiberwise relational
  cumulativity. Ordinary `Cumulative` has only conversion, universe lifting, invariant-domain
  products, and transitivity; each constructor preserves every substituted relation fiber. Ordinary
  typing therefore lifts into `AbstractionHasType`, giving the complete raw abstraction conclusion
  without an extra premise. This does not identify the structurally stronger erased annotated
  subtyping judgment with ordinary cumulativity.
- **The coherence-preserving arrow level-4 dependency is not minimal for native Lean equality.**
  UIP lowers the necessary domain structure from level `4` to level `3`; the stronger requirement
  is retained as the intended proof-relevant specification, while the native reduction is proved
  separately.
- **Figure 9 and the artifact have different output representations.** The mathematical rule returns
  terms, so `RegisteredConstantSyntax` allows arbitrary closed primed and witness terms. In
  `ESOP2024` and `0.1.5`, however, `trocq.db.gref` stores global
  references for both outputs; `0.1.5` merely resolves the primed global reference to its term form
  during graph reduction. `RegisteredConstantSyntax.Environment.translationSourceValid` checks only
  the source declaration and annotated type, and `LawfulEnvironment` is deliberately only
  source-lawfulness. The separate `LawfulTranslationEnvironment` now validates the primed and
  witness outputs relative to the selected type translation, an explicit relation-type quotation,
  and a coherent context realization; from it the complete Figure 9 constant-abstraction branch is
  proved. `RegisteredConstantRows.Row` now retains the artifact graph's source/type/target/witness
  payload, projects exactly to the annotation-only `D_K` constraint, and generates the full strict
  lower-output family. The current recursive lookup still lacks an output index: it can represent
  the base and a weakened row simultaneously exactly when their witness terms coincide. A typed
  quoted weakener and its connection to `LawfulTranslationEnvironment` remain.
- **Equations (11) and (12) are not merely semantic constructions.** Their native structured
  universe packages and relation projections are implemented. `UnivalentUniverseQuotation` states
  Equation (11)'s exact extended object-language typing and conversion obligations, while
  `StructuredUniverseQuotationSyntax` realizes its top/top instance in the genuine syntax.
  `StructuredUniverseQuotationSyntax` gives Equation (12) the general syntax extension with typed
  relation families, witnesses, projections, and definitional projection reduction.
  The tagged artifact instead generates ordinary Coq constants for these families and projections,
  so the Lean primitive extension is a faithful metamodel of their laws, not yet a literal quotation
  through registered globals.
- **Figure 7 uses one fixed realizer environment.** Universe, arrow, dependent-product, and
  subtyping-weakening witnesses are selected by a single `SyntaxRealizers` parameter shared by the
  entire derivation, so rules cannot choose unrelated witnesses independently.
- **The printed Theorem 6 context is ill-scoped in its variable case.** Its definition of
  `γ(Δ)` retains only `x : A`, while the theorem asks to type `x'` and `xR` there. The artifact
  introduces all `x`, `x'`, and `xR` binders. `relationalScope_eq_sourceScope_iff` formalizes the
  scope mismatch, `not_contextWitnessRecoveryClaim` proves that the omitted witness cannot be
  recovered from the source-only context, and `ContextRealization` is the explicit scoped repair.
- **The current Figure 7 lambda rule is not yet quotation-faithful.** It directly binds
  `A_R x x'`; the paper relies on a structured record's coercion to its `rel` field. The explicit
  core syntax must instead bind `rel(A_R) x x'`. `QuotationBackedBridge` records only untyped
  syntactic alignment and must not be counted as the typed quotation theorem. The genuine syntax
  now has both this binder and quotation-valued contexts; the realized triple-context construction
  stores it and proves that it is not secretly an embedded core context. A conservative typing
  fragment proves this projected binder well formed and makes its witness variable available by
  lookup. That fragment deliberately forgets relation-fiber universe levels; lifting the complete
  Figure 7 judgment and realizer laws into a universe-aware extension remains a separate obligation.
- **Conservativity needs the ordinary target judgment, not only literal rule erasure.**
  `UnderlyingDependentCalculus` records the annotation-free Figures 5 and 6 judgments, and the
  mutual `WellFormed.erase`, `HasType.erase`, and `Subtype.erase` definitions prove exact erasure
  into that intermediate system. Its structural `Subtype` includes application covariance, lambda
  covariance, and contravariant product domains, whereas ordinary `Cumulative` contains only
  conversion, universe lifting, invariant-domain products, and transitivity. The former context-free
  map between them and its conditional application-transport embedding have been retired. The
  appendix still targets ordinary `CCω` typing, so completing it requires a direct typed
  interpretation of those structural derivations; no final embedding is currently claimed.
- **The source-tail 0.B has two genuine beta-conversion errata.** Universe cumulativity refutes the
  printed subtyping-erasure lemma with `Sort 0 ≤ Sort 1`, and the typing derivation
  `Sort 0 : Sort 1` refutes the theorem's displayed term/type conversion. The repairs target
  a typed interpretation of structural subtyping and ordinary typing, respectively, rather than an
  untyped beta- or cumulative-conversion bridge. Parallel-beta confluence proves both nonconversion
  facts; newest-entry narrowing is proved by a typed identity substitution, canonical beta redexes
  preserve typing, and cumulative product-component inversion proves compatible one-step subject
  reduction unconditionally, including transitive paths through beta-convertible intermediates. The
  direct derivation-indexed interpretation remains the source-tail metatheory, not a context-free
  application-transport interface.
- **Canonical erasure is not source-tail Theorem 0.C.1.** `Judgment.canonicalErasure` proves only
  normalization equalities for the restricted self-translation. `Judgment.eraseToRaw` now supplies
  the source tail's erased parameter context, raw parametricity sequent, and recursive `rel*`
  projection under `ErasureLaws`. `RelationFieldSyntax.erasure` is only a structural test model;
  `canonicalRawRealizers` satisfies the complete law package directly by maximally annotating raw
  witnesses, so the structural source-tail theorem is fully instantiated.
  The genuine universe-witness primitive is now wired to that model: its quoted `rel` projection
  reads back as the raw universe relation and agrees exactly with the structural universe law. The
  genuine typed arrow, product, and weakening realizers remain, while the generic collision theorem
  records the quotation constraint.
- **The maximal-annotation correspondence is currently constructor-local.**
  `MaximalCorrespondence` relates canonical source-generated contexts and derivations under
  explicit `RealizerAgreement` equations; assembling the constructors into the full derivation
  induction and proving the typed realizer laws remain.
- **Figure 8 states definitional conversion, not raw syntax equality.** Literal equality is
  inconsistent already for the identity equation: no application node can equal every witness.
  `noSyntacticIdentityTransformer` proves this obstruction, and
  `identityWitnessTransformer_beta` verifies the intended beta-convertible identity case.
- **The Figure 8 equations and artifact algorithm are distinct.** The proof-relevant
  `RecursiveWitnessWeakeningSubtypeIndexed.TypedDerivation` indexes the five equations by actual
  annotated-subtyping structure and avoids overlapping raw-term cases. Its application constructor
  still recursively applies a family
  transformer. The ESOP code is instead a partial typed meta-program with results `wfun` and
  `wsuspend`: universes create a projection placeholder, products recurse by variance,
  variable/global-headed applications are identity, lambdas suspend, and only application of a
  suspended lambda resumes recursion after substituting both endpoints.
  `MetaWitnessWeakeningEvaluator` now encodes that result type and exact first-match term-head
  dispatch over constant-aware syntax. Its proof-relevant traces are sound for the executable
  evaluator, successful outputs are deterministic, and a universe relation used as an applied
  function is rejected explicitly. What remains is typed soundness connecting each successful
  output to the originating annotated-subtyping derivation and quoted object-language transformer;
  conversion boundaries, paired-endpoint substitution closure, and quotation remain explicit
  obligations.
- **A stated proposition is not counted as a proved theorem.** The catalog distinguishes exact
  judgment/claim encodings from abstraction, conservativity, and weakening proofs that still need
  derivation induction.
- **The artifact is an implementation, not an internal proof of its meta-algorithms.** Coq checks the
  generated hierarchy, witness constants, and final proof terms, but the Elpi constraint reducer,
  first-match registry policy, and recursive weakening procedure do not themselves come with
  soundness, completeness, or minimality theorems in the tagged artifact. Lean's certified reducer
  and counterexamples are therefore additional metatheory rather than a transliteration of artifact
  proofs.
- **The verified finite solver is a reference semantics, not the artifact's optimized algorithm.**
  It represents order, universe, arrow, dependent-product, and registered-constant `D_K` table
  constraints, enumerates the finite assignment space, and returns all Pareto-minimal solutions.
  When a pointwise least solution exists, a theorem reduces this set to its singleton. The graph
  reducer separately implements output-first propagation and proves every successful result belongs
  to exhaustive search. It does not always find a least solution: formal counterexamples show both
  rejection of a satisfiable supported acyclic system and successful return of a nonminimal one.
- **Registered-constant lookup is order-sensitive in the artifact.** The denotational `D_K`
  constraint permits any matching row, while Coq-Elpi commits to the first row with the chosen
  output annotation. The Lean graph reducer models first-match behavior and remains sound by final
  certification, but duplicate output rows with different input requirements make it incomplete
  and potentially nonminimal. A separate counterexample shows that rows alone do not infer an
  otherwise unconstrained output annotation. Lean now has payload-backed rows carrying the artifact
  node's source constant, annotated type, target, and witness, with a theorem identifying their
  projection with annotation-only `D_K` satisfaction. `generatedRows` constructs the base row and
  every strict lower-output weakening. The exact remaining mismatch is output indexing: the current
  source/type-keyed recursive lookup cannot jointly realize two rows whose witnesses differ, while
  the artifact registry stores them at distinct output annotations.
- **The calculus and artifact use different constructor constraints operationally.** Figures 6 and
  7 require exact equations `D_→(γ) = (α,β)` and `D_Π(γ) = (α,β)`. The Coq-Elpi graph reducer instead
  propagates the computed pair as lower bounds. Exact satisfaction implies the relaxed artifact
  constraint, but `arrowLowerRelaxation_strict` proves the converse is false.
- **One tagged helper does not implement the product cover relation correctly.** In both
  `ESOP2024` and `0.1.5`, `param-class.weakenings-from` takes the Cartesian product of strict
  one-coordinate predecessor lists, omitting weakenings that lower only one component. The actual
  hierarchy generation weakens each component separately, and `all-weakenings-from` includes the
  one-component cases; current `0.4.0` also repairs the immediate helper. Lean therefore follows the
  mathematical componentwise order, not this tagged implementation defect.
