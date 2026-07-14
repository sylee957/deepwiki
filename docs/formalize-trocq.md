# Formalizing the theory behind Trocq

Source: Cohen, Crance, and Mahboubi, *Trocq: Proof Transfer for Free, With or Without
Univalence*, ESOP 2024, DOI `10.1007/978-3-031-57262-3_10`. The local reference is
`references/2310.14022v2.pdf`.

The supplementary constructions omitted from the PDF are in the official Trocq `0.1.5` artifact
(DOI `10.5281/zenodo.10563382`), especially `Hierarchy.v`, `Param_Type.v`, `Param_forall.v`, and
`Param_arrow.v`. Those files, rather than inference from the displayed tables alone, are the source
of truth for porting the `p□`, `pΠ`, and `p→` witness families.

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
  definitionally; the corresponding quoted `CCω` term and typing derivation remain open.
- [x] State the exact quoted-universe boundary as `UnivalentUniverseQuotation`, indexed by an
  explicit extension of object-language typing and definitional conversion; its fields record the
  package typing and projected-relation conversion without identifying the native semantic package
  with an object-language term.
- [x] Prove the univalent abstraction result for the intrinsic function fragment.
- [ ] Extend both abstraction results from the intrinsic fragment to full dependent `CCω` typing
  judgments. For raw abstraction, the conversion case is proved; cumulativity and the strengthened
  induction that recursively supplies translated type witnesses remain.

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
- [x] Define the exact structured-relation carrier `Σ R, RelationClass α R`, its projections,
  converse symmetry, and structure-preserving weakening.
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
- [x] Add well-formedness, dependent typing, conversion, and cumulativity for the scoped calculus.
- [x] Prove typed renaming, weakening, simultaneous substitution, instantiation, and their
  preservation of beta conversion, cumulativity, context well-formedness, and typing.
- [x] Add annotations, binder-safe erasure, and the complete displayed `CCω⁺` subtyping and typing
  judgments with `D□`, `D→`, and `DΠ` side conditions.
- [x] Define the annotation-free judgments obtained by literally erasing Figures 5 and 6, and
  prove mutually that erasure preserves context formation, typing, and every subtyping derivation.
- [x] Erase every annotated context, typing, and subtyping derivation into the literal
  annotation-free Figures 5 and 6 calculus.
- [x] Reduce its final embedding into ordinary `DependentCalculus` typing to the precise proposition
  `ErasedSubtypeTypehood`: a target reached by a typed erased-subtyping derivation preserves the
  existence of a universe typing. The construction covers every typing constructor, while erased
  subtyping maps to ordinary cumulative conversion unconditionally. The older `CumulativeTypehood`
  boundary is retained only as a strictly stronger sufficient assumption because it discards the
  typing evidence carried by the subtyping derivation.
- [ ] Prove `ErasedSubtypeTypehood` from conversion and regularity for the ordinary calculus; this is
  now the only assumption in the Appendix B bridge.
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
- [x] Define the minimally repaired domain-coherent judgment and prove its translation functional.
- [x] Construct the translated context extension `x : A`, `x' : A'`, `xR : Aᴿ x x'` and prove
  its well-formedness from the translated domain witness.
- [x] Prove the universe and variable cases of the repaired abstraction typing induction.
- [x] Prove context-lookup regularity and product-term inversion, peeling conversion and
  cumulativity wrappers to recover the domain and codomain universe derivations.
- [ ] Prove the repaired sequent abstraction theorem using a triple-extended dependent typing
  context; application, lambda, product, and conversion remain, and the literal Figure 3 theorem
  cannot hold without restoring the omitted domain data.

## Sections 4.2-4.5 - univalent sequents and Trocq

- [x] Transcribe Figure 4 as a scoped univalent-parametricity judgment with explicit realizers for
  the object-language `p□` and `pΠ` constants, and prove functionality for fixed realizers.
- [x] State Theorem 5 with an explicit universe-univalence hypothesis and verify Remark 3
  semantically as the top relation fiber `Σ R, IsUmap R × IsUmap (Converse R)`.
- [x] Transcribe every Figure 7 Trocq rule in
  `DeepWiki/Refine/AnnotatedRelationTranslation.lean`, including `D□`, `D→`, `DΠ`, and conversion
  weakening, and decompose the Theorem 6 conclusion through an explicit relation-quotation bridge.
  The bridge itself is still an obligation, so this is not yet an object-language proof.
- [x] Isolate the universe-witness consequences of the abstraction claim in
  `DeepWiki/Refine/UniverseWitnessConsequences.lean`.
- [x] Formalize all five Figure 8 recursive weakening equations as object-language definitional
  convertibilities at the scoped syntax boundary, plus executable semantic universe and
  dependent-product weakening. Raw syntax equality is too strong: even the identity equation is
  refuted by `noSyntacticIdentityTransformer`, while the quoted identity lambda satisfies it by
  beta conversion.
- [x] Formalize Figure 9 constant type collections, common erasure, partial translation lookup,
  functionality, stuck lookup, and completeness.
- [ ] Prove Theorems 5 and 6 after supplying a typed object-language quotation of structured
  relations; native Lean also cannot inhabit the paper's full universe-univalence premise.

## Appendices - erasure and maximality

- [x] Prove Appendix 0.B annotation erasure for contexts, typing, and subtyping into the literal
  annotation-free calculus.
- [ ] Complete Appendix 0.B conservativity by embedding the literal unannotated Figures 5/6 rule
  system into the ordinary `CCω` typing judgment; the current `ExistingCalculusEmbedding` is only
  the exact remaining interface.
- [x] Construct the erased parameter context, recursively project relation records with `rel*`, and
  map every annotated synthesis derivation to a raw sequent under explicit `ErasureLaws` for the
  opaque witness realizers.
- [ ] Complete Appendix Theorem 0.C.1 by realizing `ErasureLaws` with the still-missing quoted
  object-language relation projections and universe/product/weakening witnesses.
- [x] Formalize Appendix 0.D's maximal annotation function on terms, substitutions, and contexts;
  prove naturality for renaming, substitution, instantiation, and lookup, and prove erasure is a
  left inverse.
- [x] Lift every context-formation, typing, and subtyping derivation of the literal unannotated
  calculus to the maximally annotated calculus.
- [ ] Prove Appendix Theorem 0.D.1 by lifting every univalent-parametricity derivation to the
  maximally annotated Trocq judgment; the remaining obligation is a scope bridge from its
  already-expanded triple context to `AnnotatedRelationTranslation.Context`.

## Section 4.5 - registered constants

- [x] Represent a global constant's family of annotated type choices.
- [x] Require all annotated choices for one constant to share the same erasure.
- [x] Register a synthesized target term and witness term for every annotated choice; outputs are
  not restricted to constant names because the paper's list witness is a lambda term.
- [x] Formalize both constant rules of Figure 9 and prove the common-erasure invariant for their
  typing derivations.
- [x] State an exact scoped extension interface that embeds the constant-free calculus, represents
  genuine constant occurrences, and lifts both Figure 9 rules with arbitrary output terms.
- [ ] Construct the paper's recursive syntax, typing, and translation judgments by parameterizing
  every term former and rule over global constants; the interface records this remaining
  implementation boundary without treating names as arbitrary terms.

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
`Trocq Use`, annotation constraint solving, and automatic tactic rewriting remain plugin-engineering
work and are recorded separately in the source catalog rather than silently counted as formalized.

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
- formalize the raw, univalent, and Trocq sequent judgments and prove Lemma 5 and Theorems 1–6 by
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
  judgment has a closed counterexample to Lemma 5. `CoherentRawSequent` restores the omitted domain
  premise and satisfies functionality.
- **The coherence-preserving arrow level-4 dependency is not minimal for native Lean equality.**
  UIP lowers the necessary domain structure from level `4` to level `3`; the stronger requirement
  is retained as the intended proof-relevant specification, while the native reduction is proved
  separately.
- **Figure 9 translations return terms, not only names.** The registry therefore separates source
  constant names from the output-term type; this is necessary for witnesses such as the displayed
  polymorphic-list lambda. `RegisteredConstantCalculus` gives the exact scoped integration
  interface and lifts both rules, while construction of the paper's recursive syntax and inductive
  judgments remains an explicit gap until they are parameterized by global constants.
- **Equations (11) and (12) are not merely semantic constructions.** Their native structured
  universe packages and relation projections are implemented. `UnivalentUniverseQuotation` states
  Equation (11)'s exact extended object-language typing and conversion obligations, while
  `StructuredUniverseQuotation.Quotation` does the same for Equation (12) and derives its projected
  relation conversion. Realizing either interface still requires the corresponding quoted syntax.
- **Figure 7 uses one fixed realizer environment.** Universe, arrow, dependent-product, and
  subtyping-weakening witnesses are selected by a single `SyntaxRealizers` parameter shared by the
  entire derivation, so rules cannot choose unrelated witnesses independently.
- **Conservativity needs the ordinary target judgment, not only literal rule erasure.**
  `UnderlyingDependentCalculus` records the annotation-free Figures 5 and 6 judgments, and the
  mutual `WellFormed.erase`, `HasType.erase`, and `Subtype.erase` definitions prove exact erasure
  into that intermediate system. The appendix targets ordinary `CCω` typing. The final embedding is
  now constructed from the exact `ErasedSubtypeTypehood` boundary, while erased subtyping already
  maps unconditionally to ordinary cumulativity. Unlike unrestricted `CumulativeTypehood`, the exact
  boundary retains the original typed-subtyping derivation. Closing it requires conversion and
  regularity metatheory; it is not assumed as an inhabitant.
- **Canonical erasure is not Appendix Theorem 0.C.1.** `Judgment.canonicalErasure` proves only
  normalization equalities for the restricted self-translation. `Judgment.eraseToRaw` now supplies
  the appendix's erased parameter context, raw parametricity sequent, and recursive `rel*`
  projection under `ErasureLaws`; the remaining task is to realize those laws with quoted witness
  syntax.
- **Figure 8 states definitional conversion, not raw syntax equality.** Literal equality is
  inconsistent already for the identity equation: no application node can equal every witness.
  `noSyntacticIdentityTransformer` proves this obstruction, and
  `identityWitnessTransformer_beta` verifies the intended beta-convertible identity case.
- **A record of Figure 8 equations is a specification, not an implementation.** The native semantic
  universe and dependent-product transformations execute, but the object-language
  `ObjectWeakeningSpecification` is not yet inhabited. Its `ObjectWeakeningRealizability`
  proposition remains in the source catalog until recursive quotation from an actual subtyping
  derivation is constructed.
- **A stated proposition is not counted as a proved theorem.** The catalog distinguishes exact
  judgment/claim encodings from abstraction, conservativity, and weakening proofs that still need
  derivation induction.
