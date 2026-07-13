# Formalizing the theory behind Trocq

Source: Cohen, Crance, and Mahboubi, *Trocq: Proof Transfer for Free, With or Without
Univalence*, ESOP 2024, DOI `10.1007/978-3-031-57262-3_10`. The local reference is
`references/2310.14022v2.pdf`.

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
- PDF pp. 20-24: plugin behavior and examples.

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
- [x] Derive the paper's transfer principle `A ≃ B -> P A ≃ P B` and proof transport from that
  hypothesis.

## Section 2.3 - parametricity translations

- [x] Formalize raw universe relations and the dependent product, application, and lambda rules.
- [x] Verify that the raw universe translation is itself a relation in the next universe.
- [x] Represent translated contexts by paired environments carrying proof-relevant witnesses.
- [x] Prove raw abstraction by structural induction for the intrinsic function fragment.
- [x] Package the two typed term interpretations and their translated witness as the three
  conclusions of the abstraction theorem.
- [x] Formalize the univalent universe package `Σ R, Σ e, R ≃ graph(e⁻¹)`.
- [x] Prove that this package is equivalent to type equivalence under an explicit univalence
  hypothesis.
- [x] Separate the package-valued term translation from its relation-valued type projection.
- [x] Construct the translated universe and verify its relation projection definitionally.
- [x] Prove the univalent abstraction result for the intrinsic function fragment.
- [ ] Extend both abstraction results from the intrinsic fragment to full dependent `CCω` typing
  judgments.

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
- [x] Define the primitive weakening projections between adjacent map classes.
- [x] Show that `DenoteRel denote` carries a canonical forward `MapClass4`.
- [x] Show that two `MapClass3` directions determine a Lean equivalence of carriers.

## Phase 2 - the partial order and generic weakening

- [x] Formalize `0 < 1 < 2a < 3 < 4` and `0 < 1 < 2b < 3 < 4`, with `2a` and `2b`
  incomparable.
- [x] Define the universe-polymorphic `RelationClass (m, n) R` family without collapsing
  proof-relevant relations to `Prop`.
- [x] Prove that the product order is a partial order on annotations.
- [x] Define a type-correct generic weakening operation for every comparable pair.
- [x] Restate the paper's named dictionary entries, including `(4, 2a)`, `(4, 2b)`, `(3, 3)`,
  and `(4, 4)`.

## Phase 3 - functional relations and equivalence

- [x] Formalize `IsFun R := forall a, IsContr (Sigma fun b => R a b)` in a proof-relevant universe.
- [x] Construct a univalent map from a functional relation and conversely.
- [x] Formalize the symmetric two-direction characterization of equivalence at the carrier and
  existence levels. Identifying the original relation family with its equality graph would require
  the univalence principle that Lean intentionally does not assume.
- [x] Isolate where proof relevance matters: for `Prop`-valued relations the `MapClass4` coherence
  field follows from proof irrelevance, while for `Type`-valued relations it carries data.

## Phase 4 - dependent respectful products

- [x] Define the dependent relational interpretation of `forall x : A, B x`.
- [x] Recover `DeepWiki.Refine.Respectful` as the nondependent specialization.
- [x] Formalize application and lambda rules for the dependent relation.
- [x] Add lifted relations for dependent pairs and `List`, including transfer of `List.map`.

## Phase 5 - annotated calculus

- [x] Formalize the paper's admissible universe-annotation predicate `D_□`.
- [x] Represent annotated universe levels and annotated types for a documented core fragment.
- [x] Represent semantic parametricity contexts for an intrinsically typed lambda calculus.
- [x] Formalize weakening of witnesses through the documented core types, including the
  contravariant domain and covariant codomain rule, and combine it with annotation weakening.
- [x] State and prove the fragment's abstraction theorem by induction on intrinsically typed terms.

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

## Completion contract

The project is complete when the source-neutral library contains the six-level relation hierarchy,
generic weakening, the functional-relation/equivalence theorem, a dependent respectful product with
an abstraction theorem for a documented core calculus, and examples showing exactly how the current
first-order resolver embeds into that theory. Every phase must pass `scripts/check.sh`; source
provenance and paper numbering stay in the DOI catalog rather than the library.
