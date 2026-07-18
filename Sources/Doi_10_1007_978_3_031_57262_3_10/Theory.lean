import DeepWiki.Refine.FunctionalRelation
import DeepWiki.Refine.AnnotationLattice
import DeepWiki.Refine.DependencyRequirements
import DeepWiki.Refine.DependencyMinimality
import DeepWiki.Refine.ArrowRelationStructure
import DeepWiki.Refine.PiRelationStructure
import DeepWiki.Refine.UniverseRelationStructure
import DeepWiki.Refine.UnivalentRelationStructure
import DeepWiki.Refine.Parametricity.Sequents.Raw
import DeepWiki.Refine.Parametricity.Sequents.RawCounterexample
import DeepWiki.Refine.Parametricity.Sequents.Univalent
import DeepWiki.Refine.AnnotatedDependentCalculus
import DeepWiki.Refine.MaximalAnnotation
import DeepWiki.Refine.AnnotatedCalculusConservativity
import DeepWiki.Refine.AnnotatedRelationTranslation
import DeepWiki.Refine.AnnotatedParametricityErasure
import DeepWiki.Refine.Annotated.Quotation.Syntax
import DeepWiki.Refine.RegisteredConstantSyntax
import Sources.Doi_10_1007_978_3_031_57262_3_10.Source

/-! # Trocq theory — coverage catalog

Coverage map for the mathematical definitions and metatheorems in the rendered ESOP 2024 paper.
Entries headed Appendix 0.A-0.E come from an unrendered arXiv source tail after `\end{document}`
and are labeled separately from proceedings-paper coverage.

Lean modeling caveat: native `Eq` is proof-irrelevant, so
`IsEmpty IsUnivalentUniverse` is provable. The univalence-dependent entries below verify the paper's
signatures and dependency boundaries conditionally; they are not an internal HoTT model.

## NOT YET FORMALIZED

- Figure 2 semantic minimality, p. 14 — [research] every row is proved least for its explicit
  coherence-preserving feature constraint, but the arrow level-`4` row is not semantically minimal
  for native Lean equality: proof irrelevance lowers its sufficient domain from level `4` to level
  `3`. Full semantic minimality needs a proof-relevant HoTT identity semantics.
- Theorem 4 (raw-parametricity abstraction theorem in sequent form), p. 16 — [infra] its exact
  proposition is formalized and formally refuted: the displayed lambda rule leaves the primed and
  witness domains arbitrary, so a closed well-typed source lambda can synthesize a primed lambda
  whose binder is a dependent product while its separately translated type expects a universe
  binder. This refutes both Lemma 5 and the literal Theorem 4. The repaired domain-coherent judgment
  is functional. The former constructor-by-constructor strengthening and typing-reflection route did
  not assemble a theorem and has been removed. A repaired abstraction theorem must instead use the
  domain-coherent judgment throughout and prove its own typing induction.
- Theorem 5 (univalent abstraction theorem in sequent form), p. 17 — [research] its exact
  univalence-conditional proposition and all Figure 4 rules are formalized, but native Lean has no
  inhabitant of the required universe-univalence hypothesis and the scoped syntax does not quote
  record projections needed for the typing induction.
- Theorem 6 (Trocq abstraction theorem), p. 20 — [infra] the Figure 7 synthesis judgment is
  formalized, but the printed abstraction theorem is not. Its typing proof still needs faithful
  object-language quotation of relation projections, a coherent three-copy context, and a complete
  induction over the translation judgment.
- Remark 4 (source annotations determine translated relation structure), pp. 20–21 — [infra]
  depends on Theorem 6 and its typed relation-projection witness.
- Figure 8 (recursive weakening of translated witnesses), p. 21 — [infra] no total recursive
  weakening operation satisfying all five displayed conversion equations is formalized. Existing
  specification and proof-relevant-index experiments do not cover conversion and lambda closure.
- Remark 5 (universe witnesses inhabit their source annotation), p. 21 — [infra] depends on the
  exact typed Theorem 6 judgment and the quoted Equation (12) witness.
- Theorem 0.B.1 (conservativity over ordinary `CCω`), unrendered arXiv source tail 0.B — [infra]
  both the printed subtyping-erasure lemma and the theorem conclusion incorrectly target beta
  conversion. `Sort 0 ≤ Sort 1` refutes the former and `Sort 0 : Sort 1` refutes the latter. The
  exact erasure into the literal annotation-free Figures 5/6 rule system is proved. That system's
  structural subtyping includes application covariance, lambda covariance, and contravariant product
  domains, so it is intentionally distinct from ordinary `CCω` cumulativity. The former unconditional
  map between them and its conditional application-transport scaffold have been retired. A repaired
  final conservativity theorem requires a typed interpretation of the structural subtyping judgment
  into ordinary typing.
  The common-kind typed beta-conversion constructor is isolated as a necessary fragment: proving it
  requires typed subject reduction and application/product inversion, not merely untyped confluence.
  Cumulative product targets now expose convertible domains and cumulative codomains even through
  transitive beta-convertible intermediates. Consequently, typed root-beta contraction and every
  compatible one-step beta reduction preserve typing unconditionally. Arbitrary application-spine
  transport, substitution stability, and the direct typed interpretation remain.
- Erasure of Trocq, unrendered arXiv source tail 0.C — [infra] the recursive `rel*` projection and
  erased parameter context are formalized. `Judgment.eraseToRaw` proves the theorem only under an
  abstract `ErasureLaws` interface; genuine universe, arrow, product, and weakening laws remain.
- Maximal Trocq, unrendered arXiv source tail 0.D — [infra] the maximal term and context annotation
  equations are formalized. The biconditional, its reverse implication, the ordinary-typing
  conjunct, arbitrary target context `Δ`, and genuine realizer equations remain.
-/

namespace DeepWiki.Ccm

/-- **Definition 3, p. 10:** functionality as contractibility of every relation fiber. -/
abbrev def_3 := @DeepWiki.Refine.IsFun

/-- **Lemma 2, p. 10, native counterpart:** the equivalence follows from explicit universe univalence. -/
abbrev lemma_2 := @DeepWiki.Refine.typeEquivalenceEquivBidirectionallyFunctionalRelation

/-- **Lemma 3, p. 10:** under explicit univalence, functions equal functional-relation packages. -/
abbrev lemma_3 := @DeepWiki.Refine.functionEquivFunctionalRelationData

/-- **Definition 4, p. 10:** a relation equipped with a coherent represented map. -/
abbrev def_4 := @DeepWiki.Refine.IsUmap

/-- **Lemma 4, p. 11:** functional relations and coherent represented maps are equivalent. -/
abbrev lemma_4 := @DeepWiki.Refine.isFunEquivIsUmap

/-- **Theorem 3, p. 11, native counterpart:** explicit univalence identifies both presentations. -/
abbrev theorem_3 := @DeepWiki.Refine.typeEquivalenceEquivStructuredRelationTop

/-- **Definition 5, p. 12:** the bidirectional six-level hierarchy of structured relations. -/
abbrev def_5 := @DeepWiki.Refine.StructuredRelation

/-- **Definition 5, p. 12:** the generic relation projection `rel(r)`. -/
abbrev def_5_rel := @DeepWiki.Refine.StructuredRelation.rel

/-- **Definition 5, p. 12:** the generic forward-map projection `map(r)`. -/
abbrev def_5_map := @DeepWiki.Refine.StructuredRelation.map

/-- **Definition 5, p. 12:** the generic backward-map projection `comap(r)`. -/
abbrev def_5_comap := @DeepWiki.Refine.StructuredRelation.comap

/-- **Definition 6, p. 12:** forward/backward annotations with the componentwise partial order. -/
abbrev def_6 := DeepWiki.Refine.Annotation

/-- **Remark 1, p. 12:** the top annotation is the bidirectional level-`4` annotation. -/
abbrev remark_1_top := DeepWiki.Refine.Annotation.equivalence

/-- **Remark 1, p. 12:** the bottom annotation is the bidirectional level-`0` annotation. -/
abbrev remark_1_bottom : DeepWiki.Refine.Annotation := ⊥

/-- **Remark 2, p. 12:** `(1,0)` exposes an arbitrary forward function. -/
abbrev remark_2_function := @DeepWiki.Refine.RelationClass.toFunction

/-- **Remark 2, p. 12:** `(4,0)` exposes a coherent represented map. -/
abbrev remark_2_univalent_map := @DeepWiki.Refine.RelationClass.toUnivalentMap

/-- **Remark 2, p. 12:** `(4,2a)` exposes a retraction. -/
abbrev remark_2_retraction := @DeepWiki.Refine.RelationClass.toRightInverse

/-- **Remark 2, p. 12:** `(4,2b)` exposes a section. -/
abbrev remark_2_section := @DeepWiki.Refine.RelationClass.toLeftInverse

/-- **Remark 2, p. 12:** `(4,4)` exposes an equivalence. -/
abbrev remark_2_equivalence := @DeepWiki.Refine.RelationClass.equivalenceToEquiv

/-- **Remark 2, p. 12:** `(3,3)` exposes an isomorphism. -/
abbrev remark_2_isomorphism := @DeepWiki.Refine.RelationClass.isomorphismToEquiv

/-- **Remark 2, p. 12:** swapping relation direction swaps the two annotation coordinates. -/
abbrev remark_2_symmetry := @DeepWiki.Refine.StructuredRelation.converseEquiv

/-- **Definition 7, p. 13:** the admissible pairs of universe-translation annotations. -/
abbrev def_7 := DeepWiki.Refine.AdmissibleUniverseTranslation

/-- **Definition 9, p. 19:** comparable one-direction map classes weaken by forgetting fields. -/
abbrev def_9_map_class_weakening := @DeepWiki.Refine.MapClass.weaken

/-- **Definition 9, p. 19:** bidirectional relation classes weaken componentwise. -/
abbrev def_9_relation_class_weakening := @DeepWiki.Refine.RelationClass.weaken

/-- **Figure 3, p. 16:** the literal derivation-indexed raw parametricity judgment. -/
abbrev figure_3_raw_sequent := @DeepWiki.Refine.DependentCalculus.ParametricitySequents.RawSequent

/-- **Definition 8, p. 16:** admissibility gives coherent types to every variable triple. -/
abbrev def_8 := @DeepWiki.Refine.DependentCalculus.ParametricitySequents.Admissible

/-- **Lemma 5 audit, p. 15:** the literal displayed lambda rule makes functionality false. -/
abbrev lemma_5_literal_counterexample :=
  DeepWiki.Refine.DependentCalculus.ParametricitySequents.rawSequent_not_functional

/-- **Lemma 5 repair, p. 15:** the domain-coherent raw judgment is functional. -/
abbrev lemma_5_domain_coherent :=
  @DeepWiki.Refine.DependentCalculus.ParametricitySequents.CoherentRawSequent.functional

/-- **Theorem 4, p. 16:** the exact raw abstraction conclusion, isolated as a proposition. -/
abbrev theorem_4_claim :=
  DeepWiki.Refine.DependentCalculus.ParametricitySequents.RawAbstractionClaim

/-- **Theorem 4 audit, p. 16:** the literal displayed theorem is false. -/
abbrev theorem_4_literal_claim_false :=
  DeepWiki.Refine.DependentCalculus.ParametricitySequents.not_rawAbstractionClaim

/-- **Figure 4, p. 17:** univalent parametricity sequents with fixed syntax realizers. -/
abbrev figure_4_univalent_sequent :=
  @DeepWiki.Refine.DependentCalculus.UnivalentParametricitySequents.Sequent

/-- **Theorem 5, p. 17:** the exact abstraction proposition under explicit univalence. -/
abbrev theorem_5_claim.{u}
    (realizers : DeepWiki.Refine.DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers) :
    Prop :=
  DeepWiki.Refine.DependentCalculus.UnivalentParametricitySequents.AbstractionClaim.{u} realizers

/-- **Remark 3, p. 17:** top universe fibers are relations with univalent maps both ways. -/
abbrev remark_3_top_relation_fiber :=
  @DeepWiki.Refine.universeRelationTopFiberEquiv

/-- **Section 4.5, p. 21:** constants carry annotated type choices and partial translations. -/
abbrev figure_9_constant_environment := @DeepWiki.Refine.RegisteredConstantSyntax.Environment

/-- **Figure 9, p. 21, `Const+`:** an admitted annotated choice types its constant occurrence. -/
abbrev figure_9_constant_typing := @DeepWiki.Refine.RegisteredConstantSyntax.HasType.constant

/-- **Figure 9, p. 21, `TrocqConst`:** an exact lookup synthesizes target and witness terms. -/
abbrev figure_9_constant_translation :=
  @DeepWiki.Refine.RegisteredConstantSyntax.Judgment.constant_of_lookup

/-- **Section 4.3, p. 17:** intrinsically scoped `CCω⁺` terms annotate every universe occurrence. -/
abbrev annotated_calculus_terms := DeepWiki.Refine.AnnotatedDependentCalculus.Term

/-- **Section 4.3, p. 18:** erasure removes universe annotations without changing term structure. -/
abbrev annotated_calculus_erasure := @DeepWiki.Refine.AnnotatedDependentCalculus.Term.erase

/-- **Figure 5, p. 18:** the derivation-indexed annotated subtyping judgment. -/
abbrev figure_5_subtyping := @DeepWiki.Refine.AnnotatedDependentCalculus.Subtype

/-- **Figure 6, p. 19:** annotated dependent typing with the three dependency conditions. -/
abbrev figure_6_typing := @DeepWiki.Refine.AnnotatedDependentCalculus.HasType

/-- **Section 4.3, p. 18:** annotation-free subtyping is the literal erasure of Figure 5. -/
abbrev erased_subtyping := @DeepWiki.Refine.UnderlyingDependentCalculus.Subtype

/-- **Section 4.3, p. 19:** annotation-free typing is the literal erasure of Figure 6. -/
abbrev erased_typing := @DeepWiki.Refine.UnderlyingDependentCalculus.HasType

/-- **Section 4.3, p. 18:** subtyping erases into the literal annotation-free rule system. -/
abbrev subtyping_erases_to_strengthened :=
  @DeepWiki.Refine.AnnotatedDependentCalculus.subtyping_erases_to_strengthened

/-- **Section 4.3, p. 18:** typing erases into the literal annotation-free rule system. -/
abbrev typing_erases_to_strengthened :=
  @DeepWiki.Refine.AnnotatedDependentCalculus.typing_erases_to_strengthened

/-- **Section 4.3, intermediate:** annotated typing erases to the literal unannotated rule system. -/
abbrev annotation_erasure_conservativity :=
  @DeepWiki.Refine.AnnotatedCalculusConservativity.annotationErasureConservativity

/-- **Section 4.3, p. 18:** contexts erase into the literal annotation-free rule system. -/
abbrev context_erases_to_strengthened :=
  @DeepWiki.Refine.AnnotatedDependentCalculus.context_erases_to_strengthened

/-- **Source-tail Lemma 0.B.1 erratum:** the printed subtyping-as-beta-conversion claim. -/
abbrev appendix_subtyping_erasure_printed_claim :=
  DeepWiki.Refine.AnnotatedCalculusConservativity.SubtypingErasureAsConversionClaim

/-- **Source-tail Lemma 0.B.1 erratum:** universe cumulativity refutes the printed claim. -/
abbrev appendix_subtyping_erasure_printed_claim_false :=
  DeepWiki.Refine.AnnotatedCalculusConservativity.not_subtypingErasureAsConversionClaim

/-- **Theorem 0.B.1 erratum:** the printed typing-as-beta-conversion conclusion. -/
abbrev appendix_conservativity_printed_claim :=
  DeepWiki.Refine.AnnotatedCalculusConservativity.AnnotationErasureAsConversionClaim

/-- **Theorem 0.B.1 erratum:** `Sort 0 : Sort 1` refutes the printed conclusion. -/
abbrev appendix_conservativity_printed_claim_false :=
  DeepWiki.Refine.AnnotatedCalculusConservativity.not_annotationErasureAsConversionClaim

/-- **Source tail 0.D, maximal-annotation figure (`fig:topAnn`):** maximally annotate a term. -/
abbrev maximal_annotation := @DeepWiki.Refine.MaximalAnnotation.Term.annotate

/-- **Source tail 0.D, maximal-annotation figure (`fig:topAnn`):** maximally annotate a context. -/
abbrev maximal_context_annotation := @DeepWiki.Refine.MaximalAnnotation.Context.annotate

/-- **Source tail 0.C, Erasure of Trocq:** `rel*` recursively projects relation witnesses. -/
abbrev appendix_relation_projection_star :=
  @DeepWiki.Refine.AnnotatedParametricityErasure.relationProjectionStar

/-- **Source tail 0.C, Erasure of Trocq:** erase an annotated context to raw parameter triples. -/
abbrev appendix_erased_parametricity_context :=
  @DeepWiki.Refine.AnnotatedParametricityErasure.eraseParametricityContext

/-- **Figure 7, p. 20:** the scoped four-place Trocq synthesis judgment. -/
abbrev figure_7_trocq_translation := @DeepWiki.Refine.AnnotatedRelationTranslation.Judgment

/-- **Figure 2, p. 14:** the dependency-annotation table for dependent products. -/
abbrev dependent_product_requirements := DeepWiki.Refine.dependentProductRequirements

/-- **Figure 2, p. 14:** the dependency-annotation table for non-dependent arrows. -/
abbrev arrow_requirements := DeepWiki.Refine.arrowRequirements

/-- **Figure 2, p. 14:** every dependent-product row is least for its constructor features. -/
abbrev dependent_product_constraint_minimality :=
  DeepWiki.Refine.MapLevel.piDomainRequirement_constraintLeast

/-- **Figure 2, p. 14:** every arrow row is least for its coherence-preserving features. -/
abbrev arrow_coherent_constraint_minimality :=
  DeepWiki.Refine.MapLevel.arrowDomainRequirement_coherentConstraintLeast

/-- **Figure 2 audit, p. 14:** native Lean refutes semantic minimality of arrow row `4`. -/
abbrev arrow_four_not_native_semantically_minimal :=
  DeepWiki.Refine.arrowFour_coherentRequirement_not_nativeSemanticallyLeast

/-- **Figure 2, p. 14:** the structured dependent-product witness `pΠ`. -/
abbrev dependent_product_witness := @DeepWiki.Refine.StructuredRelation.pi

/-- **Figure 2, p. 14:** the structured non-dependent arrow witness `p→`. -/
abbrev arrow_witness := @DeepWiki.Refine.StructuredRelation.arrow

/-- **Equation (12), p. 13, semantic counterpart:** admissible assumptions construct a native witness. -/
abbrev equation_12_semantic_universe_witness := @DeepWiki.Refine.universeStructuredRelation

/-- **Equation (12), p. 13, semantic counterpart:** assumptions isolate its univalence dependency. -/
abbrev equation_12_semantic_assumptions := @DeepWiki.Refine.UniverseRelationAssumptions

/-- **Equation (12), p. 13, semantic counterpart:** weak targets need no univalence evidence. -/
abbrev equation_12_semantic_weak_target := @DeepWiki.Refine.universeStructuredRelationOfWeak

/-- **Equation (12), p. 13:** genuine syntax for relation families, witnesses, and projection. -/
abbrev equation_12_quotation_syntax :=
  DeepWiki.Refine.StructuredUniverseQuotationSyntax.Term

/-- **Equation (12), p. 13:** every admissible pair satisfies quoted typing and projection. -/
abbrev equation_12_quotation_realized :=
  @DeepWiki.Refine.StructuredUniverseQuotationSyntax.satisfiesUniverseEquation

/-- **Equation (12), p. 13:** projection computes to the source relation family. -/
abbrev equation_12_projection_beta :=
  @DeepWiki.Refine.StructuredUniverseQuotationSyntax.projectedRelation_convertible

/-- **Equation (12) modeling boundary:** a relation-family primitive is outside the core image. -/
abbrev equation_12_not_directly_core_representable :=
  @DeepWiki.Refine.StructuredUniverseQuotationSyntax.not_coreRepresentable_relationFamily

example (univalent : DeepWiki.Refine.IsUnivalentUniverse.{u}) (A B : Type u) :
    (A ≃ B) ≃
      DeepWiki.Refine.StructuredRelation.{u, u, u}
        DeepWiki.Refine.Annotation.equivalence A B :=
  DeepWiki.Refine.typeEquivalenceEquivStructuredRelationTop univalent A B

example (univalent : DeepWiki.Refine.IsUnivalentUniverse.{u}) (A B : Type u) :
    (A → B) ≃
      (Σ R : A → B → Type u, DeepWiki.Refine.IsFun R) :=
  DeepWiki.Refine.functionEquivFunctionalRelationData univalent A B

example (univalent : DeepWiki.Refine.IsUnivalentUniverse.{u}) (A B : Type u) :
    (A ≃ B) ≃
      (Σ R : A → B → Type u,
        DeepWiki.Refine.IsFun R × DeepWiki.Refine.IsFun (DeepWiki.Refine.Converse R)) :=
  DeepWiki.Refine.typeEquivalenceEquivBidirectionallyFunctionalRelation univalent A B

example (α : DeepWiki.Refine.Annotation) (A B : Type u) :
    DeepWiki.Refine.StructuredRelation.{u, u, u} α A B =
      (Σ R : A → B → Type u, DeepWiki.Refine.RelationClass α R) :=
  rfl

example (α β : DeepWiki.Refine.Annotation) :
    α ≤ β ↔ α.forward ≤ β.forward ∧ α.backward ≤ β.backward :=
  Iff.rfl

example :
    DeepWiki.Refine.Annotation.equivalence = (⊤ : DeepWiki.Refine.Annotation) :=
  rfl

example :
    (⊥ : DeepWiki.Refine.Annotation) =
      ⟨DeepWiki.Refine.MapLevel.zero, DeepWiki.Refine.MapLevel.zero⟩ :=
  rfl

example : DeepWiki.Refine.Annotation.function = ⟨.one, .zero⟩ := rfl

example : DeepWiki.Refine.Annotation.univalentMap = ⟨.four, .zero⟩ := rfl

example : DeepWiki.Refine.Annotation.retraction = ⟨.four, .twoA⟩ := rfl

example : DeepWiki.Refine.Annotation.section = ⟨.four, .twoB⟩ := rfl

example : DeepWiki.Refine.Annotation.equivalence = ⟨.four, .four⟩ := rfl

example : DeepWiki.Refine.Annotation.isomorphism = ⟨.three, .three⟩ := rfl

example :
    DeepWiki.Refine.MapLevel.twoA ⊔ DeepWiki.Refine.MapLevel.twoB =
      DeepWiki.Refine.MapLevel.three :=
  rfl

example :
    DeepWiki.Refine.MapLevel.twoA ⊓ DeepWiki.Refine.MapLevel.twoB =
      DeepWiki.Refine.MapLevel.one :=
  rfl

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    (γ : DeepWiki.Refine.Annotation)
    (domain : DeepWiki.Refine.StructuredRelation
      (DeepWiki.Refine.arrowRequirements γ).1 A B)
    (codomain : DeepWiki.Refine.StructuredRelation γ C D) :
    (DeepWiki.Refine.StructuredRelation.arrow γ domain codomain).rel =
      DeepWiki.Refine.ArrowRelation domain.rel codomain.rel :=
  rfl

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (domain : DeepWiki.Refine.MapClass3 (DeepWiki.Refine.Converse R))
    (codomain : DeepWiki.Refine.MapClass4 S) :
    DeepWiki.Refine.MapClass4 (DeepWiki.Refine.ArrowRelation R S) :=
  DeepWiki.Refine.ArrowRelation.mapClass4OfDomain3 domain codomain

example {A : Type u} {B : Type v} {C : A → Type u'} {D : B → Type v'}
    (γ : DeepWiki.Refine.Annotation)
    (domain : DeepWiki.Refine.StructuredRelation
      (DeepWiki.Refine.dependentProductRequirements γ).1 A B)
    (fibers : ∀ a b (_r : domain.rel a b),
      DeepWiki.Refine.StructuredRelation γ (C a) (D b)) :
    (DeepWiki.Refine.StructuredRelation.pi γ domain fibers).rel =
      DeepWiki.Refine.DependentRespectful domain.rel
        (fun a b r => (fibers a b r).rel) :=
  rfl

example (source target : DeepWiki.Refine.Annotation) (h : target.IsUniverseWeak) :
    (DeepWiki.Refine.universeStructuredRelationOfWeak source target h).rel =
      (fun A B : Type u =>
        DeepWiki.Refine.StructuredRelation.{u, u, u} source A B) :=
  rfl

example (source target : DeepWiki.Refine.Annotation) (h : target.IsUniverseWeak) :
    (DeepWiki.Refine.universeStructuredRelation source target (.weak h)).rel =
      (fun A B : Type u => DeepWiki.Refine.StructuredRelation.{u, u, u} source A B) :=
  rfl

example (univalent : DeepWiki.Refine.IsUnivalentUniverse.{u})
    (target : DeepWiki.Refine.Annotation) (h : ¬ target.IsUniverseWeak) :
    (DeepWiki.Refine.universeStructuredRelation DeepWiki.Refine.Annotation.equivalence target
      (.strong h univalent)).rel =
        (fun A B : Type u => DeepWiki.Refine.StructuredRelation.{u, u, u}
          DeepWiki.Refine.Annotation.equivalence A B) :=
  rfl

end DeepWiki.Ccm
