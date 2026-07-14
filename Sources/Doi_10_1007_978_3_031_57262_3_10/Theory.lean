import DeepWiki.Refine.FunctionalRelation
import DeepWiki.Refine.AnnotationLattice
import DeepWiki.Refine.DependencyRequirements
import DeepWiki.Refine.DependencyMinimality
import DeepWiki.Refine.ArrowRelationStructure
import DeepWiki.Refine.PiRelationStructure
import DeepWiki.Refine.UniverseRelationStructure
import DeepWiki.Refine.UnivalentRelationStructure
import DeepWiki.Refine.ParametricitySequents
import DeepWiki.Refine.RawParametricityTyping
import DeepWiki.Refine.UnivalentParametricitySequents
import DeepWiki.Refine.AnnotatedDependentCalculus
import DeepWiki.Refine.MaximalAnnotation
import DeepWiki.Refine.AnnotatedCalculusConservativity
import DeepWiki.Refine.AnnotatedRelationTranslation
import DeepWiki.Refine.AnnotatedTranslationErasure
import DeepWiki.Refine.AnnotatedParametricityErasure
import DeepWiki.Refine.UniverseWitnessConsequences
import DeepWiki.Refine.StructuredUniverseQuotation
import DeepWiki.Refine.RegisteredConstants
import DeepWiki.Refine.RegisteredConstantCalculus
import DeepWiki.Refine.RecursiveWitnessWeakening
import Sources.Doi_10_1007_978_3_031_57262_3_10.Source

/-! # Trocq theory — coverage catalog

Coverage map for the mathematical definitions and metatheorems in the ESOP 2024 paper. The
section-specific catalogs point to the source-neutral equivalence, relation, annotation, weakening,
and core-parametricity modules.

Lean modeling caveat: native `Eq` is proof-irrelevant, so
`IsEmpty IsUnivalentUniverse` is provable. The univalence-dependent entries below verify the paper's
signatures and dependency boundaries conditionally; they are not an internal HoTT model.

## NOT YET FORMALIZED

- Figure 2 semantic minimality, p. 14 — [research] every row is proved least for its explicit
  coherence-preserving feature constraint, but the arrow level-`4` row is not semantically minimal
  for native Lean equality: proof irrelevance lowers its sufficient domain from level `4` to level
  `3`. Full semantic minimality needs a proof-relevant HoTT identity semantics.
- Theorem 4 (raw-parametricity abstraction theorem in sequent form), p. 16 — [infra] its exact
  proposition is formalized, but the displayed lambda rule is under-specified: read literally it
  leaves the primed domain and witness domain arbitrary, refuting Lemma 5. The repaired
  domain-coherent judgment is functional. The triple-extended context construction and the
  universe and variable typing cases are proved; context-lookup regularity and product-term
  inversion are also available. Application, lambda, product, and conversion remain for the
  repaired abstraction induction.
- Theorem 5 (univalent abstraction theorem in sequent form), p. 17 — [research] its exact
  univalence-conditional proposition and all Figure 4 rules are formalized, but native Lean has no
  inhabitant of the required universe-univalence hypothesis and the scoped syntax does not quote
  record projections needed for the typing induction.
- Theorem 6 (Trocq abstraction theorem), p. 20 — [infra] the intrinsic core abstraction theorem is
  proved and a scoped decomposition of the proposition is stated. Its relational typing context
  and `rel(A_R) M M'` conclusion still pass through an explicit `WitnessTypingBridge`; constructing
  that object-language bridge and proving the derivation induction remain.
- Remark 4 (source annotations determine translated relation structure), pp. 20–21 — [infra]
  its exact conclusion is derived conditionally from Theorem 6 and lawful object-language
  quotation, but discharging those two premises still depends on the exact Trocq abstraction proof.
- Figure 8 (recursive weakening of translated witnesses), p. 21 — [infra] the five equations are
  formalized as object-language convertibilities in `ObjectWeakeningSpecification`, and raw
  syntactic equality is formally refuted by `noSyntacticIdentityTransformer`; their native
  semantic counterparts execute, but `ObjectWeakeningRealizability` is not inhabited:
  constructing quoted object-language transformers recursively from annotated subtyping
  derivations remains.
- Remark 5 (universe witnesses inhabit their source annotation), p. 21 — [infra] depends on the
  exact typed object-language judgment. Its conclusion is derived from the abstraction theorem,
  quoted Equation (12), and their alignment; constructing those three object-language premises
  remains.
- Figure 9 (registered constants), p. 21 — [infra] the two displayed registry rules, common-erasure
  invariant, functional lookup, stuckness, and completeness are formalized. An exact scoped
  extension interface lifts the rules into genuine constant terms and allows arbitrary target and
  witness terms. Constructing the paper's recursive syntax and both inductive judgments still
  requires parameterizing every term former and rule by the global constant environment.
- Equation (12), p. 13 — [infra] its admissibility-indexed native semantic family is formalized, and
  `StructuredUniverseQuotation.Quotation` now states the exact quoted typing and definitional
  projection obligations. Realizing that interface in the core annotated calculus still requires
  quoted relation-family, witness, and projection syntax.
- Theorem 0.B.1 (conservativity over ordinary `CCω`), appendix — [infra] annotation erasure into the
  literal unannotated Figures 5/6 rule system is proved, and the final embedding into ordinary
  `CCω` is derived from `ErasedSubtypeTypehood`. This precise boundary retains the typed
  erased-subtyping derivation instead of discarding it into untyped cumulative conversion. Proving
  the remaining typehood preservation proposition requires the ordinary calculus's conversion and
  regularity metatheory.
- Theorem 0.C.1 (erasure of Trocq to raw parametricity), appendix — [infra] the erased parameter
  context, recursive `rel*` projection, and derivation induction into raw parametricity are
  formalized under `AnnotatedParametricityErasure.ErasureLaws`. Instantiating those laws requires
  the still-missing object-language relation projections and witness constructors.
- Theorem 0.D.1 (maximal Trocq recovers univalent parametricity), appendix — [infra] the maximal
  annotation function, its structural naturality, and its exact erasure retraction are proved;
  every context-formation, typing, and subtyping derivation of the literal unannotated calculus
  also lifts to the top annotation. Bridging the already-expanded univalent sequent scopes to
  maximally annotated `Judgment` derivations remains.
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

/-- **Theorem 4, p. 16:** one source declaration forms a well-typed relational context triple. -/
abbrev theorem_4_context_extension :=
  @DeepWiki.Refine.DependentCalculus.RawParametricity.context_extend_wellFormed

/-- **Theorem 4, p. 16:** the universe constructor satisfies raw abstraction typing. -/
abbrev theorem_4_universe_case :=
  @DeepWiki.Refine.DependentCalculus.RawParametricity.abstractionConclusion_sort

/-- **Theorem 4, p. 16:** the variable constructor satisfies raw abstraction typing. -/
abbrev theorem_4_variable_case :=
  @DeepWiki.Refine.DependentCalculus.RawParametricity.abstractionConclusion_var

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
  @DeepWiki.Refine.DependentCalculus.UnivalentParametricitySequents.universeRelationTopFiberEquiv

/-- **Figure 9, p. 21, standalone rule:** constants carry well-typed, same-erasure choices. -/
abbrev figure_9_constant_environment := @DeepWiki.Refine.RegisteredConstants.Registry

/-- **Figure 9, p. 21, standalone rule:** any registered annotated choice types its constant. -/
abbrev figure_9_constant_typing := @DeepWiki.Refine.RegisteredConstants.PositiveTyping

/-- **Figure 9, p. 21, standalone rule:** a choice synthesizes target and witness terms. -/
abbrev figure_9_constant_translation :=
  @DeepWiki.Refine.RegisteredConstants.RegisteredConstantTranslation

/-- **Figure 9, p. 21:** exact boundary for extending the annotated calculus with constants. -/
abbrev figure_9_calculus_integration :=
  @DeepWiki.Refine.RegisteredConstants.RegisteredConstantCalculus

/-- **Figure 9, p. 21:** positive registry typing lifts to a genuine constant occurrence. -/
abbrev figure_9_integrated_constant_typing :=
  @DeepWiki.Refine.RegisteredConstants.RegisteredConstantCalculus.typing_of_positive

/-- **Figure 9, p. 21:** registry translation lifts without restricting outputs to names. -/
abbrev figure_9_integrated_constant_translation :=
  @DeepWiki.Refine.RegisteredConstants.RegisteredConstantCalculus.translation_of_lookup

/-- **Section 4.5, p. 21:** every choice in `T_c` inhabits an annotated universe. -/
abbrev constant_annotated_type_is_well_typed :=
  @DeepWiki.Refine.RegisteredConstants.PositiveTyping.typeWellTyped

/-- **Section 4.5, p. 21:** all annotated types of one constant have a common erasure. -/
abbrev constant_type_erasure_invariant :=
  @DeepWiki.Refine.RegisteredConstants.PositiveTyping.erase_eq

/-- **Figure 9, p. 21:** translation is stuck exactly when the registry lookup is absent. -/
abbrev figure_9_stuck_iff_missing :=
  @DeepWiki.Refine.RegisteredConstants.isStuck_iff_no_registeredConstantTranslation

/-- **Section 4.5, p. 21:** a complete registry translates every positively typed constant. -/
abbrev complete_registry_translates_constant :=
  @DeepWiki.Refine.RegisteredConstants.Registry.IsComplete.exists_registeredConstantTranslation

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

/-- **Section 4.3, intermediate:** typing erases to the literal unannotated rule system. -/
abbrev conservativity_ccomega_plus_over_ccomega :=
  @DeepWiki.Refine.AnnotatedCalculusConservativity.annotationErasureConservativity

/-- **Section 4.3, p. 18:** contexts erase into the literal annotation-free rule system. -/
abbrev context_erases_to_strengthened :=
  @DeepWiki.Refine.AnnotatedDependentCalculus.context_erases_to_strengthened

/-- **Section 4.3, p. 18:** erased subtyping is ordinary cumulative conversion. -/
abbrev erased_subtyping_to_cumulative :=
  @DeepWiki.Refine.AnnotatedCalculusConservativity.subtype_toCumulative

/-- **Section 4.3, p. 18:** annotated subtyping erases to ordinary cumulativity unconditionally. -/
abbrev annotated_subtyping_to_cumulative :=
  @DeepWiki.Refine.AnnotatedCalculusConservativity.annotatedSubtype_toCumulative_unconditional

/-- **Theorem 0.B.1 boundary:** a direct embedding into the ordinary cumulative calculus. -/
abbrev appendix_conservativity_embedding_boundary :=
  DeepWiki.Refine.AnnotatedCalculusConservativity.ExistingCalculusEmbedding

/-- **Theorem 0.B.1 boundary:** erased typed subtyping must preserve universe typehood. -/
abbrev appendix_conservativity_typehood_boundary :=
  DeepWiki.Refine.AnnotatedCalculusConservativity.ErasedSubtypeTypehood

/-- **Theorem 0.B.1, conditional:** erased-subtyping typehood supplies the ordinary embedding. -/
abbrev appendix_conservativity_embedding_of_typehood :=
  @DeepWiki.Refine.AnnotatedCalculusConservativity.existingCalculusEmbedding_of_erasedSubtypeTypehood

/-- **Theorem 0.B.1, conditional:** erased-subtyping typehood implies ordinary conservativity. -/
abbrev appendix_conservativity_of_typehood :=
  @DeepWiki.Refine.AnnotatedCalculusConservativity.existingTypingConservativity_of_erasedSubtypeTypehood

/-- **Theorem 0.B.1:** unrestricted cumulative typehood is a sufficient stronger boundary. -/
abbrev appendix_conservativity_of_cumulative_typehood :=
  @DeepWiki.Refine.AnnotatedCalculusConservativity.existingTypingConservativity_of_cumulativeTypehood

/-- **Appendix 0.D, Figure 3:** assign the maximal annotation to every ordinary universe. -/
abbrev maximal_annotation := @DeepWiki.Refine.MaximalAnnotation.Term.annotate

/-- **Appendix 0.D, Figure 3:** maximal annotation commutes with dependent instantiation. -/
abbrev maximal_annotation_instantiate :=
  @DeepWiki.Refine.MaximalAnnotation.Term.annotate_instantiate

/-- **Appendix 0.D, Figure 3:** erasing maximal annotation returns the original term. -/
abbrev maximal_annotation_erasure :=
  @DeepWiki.Refine.MaximalAnnotation.Term.erase_annotate

/-- **Appendix 0.D, Figure 3:** erasing a maximally annotated context is identity. -/
abbrev maximal_context_erasure :=
  @DeepWiki.Refine.MaximalAnnotation.Context.erase_annotate

/-- **Theorem 0.C.1 audit:** canonical self-translation has a stronger erasure normalization. -/
abbrev appendix_canonical_erasure_audit :=
  @DeepWiki.Refine.AnnotatedTranslationErasure.Judgment.canonicalErasure

/-- **Theorem 0.C.1 audit:** this normalization is not the general raw-sequent theorem. -/
abbrev appendix_canonical_erasure_claim :=
  @DeepWiki.Refine.AnnotatedTranslationErasure.CanonicalErasureClaim

/-- **Theorem 0.C.1:** `rel*` recursively projects applications and lambda bodies. -/
abbrev appendix_relation_projection_star :=
  @DeepWiki.Refine.AnnotatedParametricityErasure.relationProjectionStar

/-- **Theorem 0.C.1:** annotated contexts erase to raw parameter triples. -/
abbrev appendix_erased_parametricity_context :=
  @DeepWiki.Refine.AnnotatedParametricityErasure.eraseParametricityContext

/-- **Theorem 0.C.1 boundary:** quoted witness constructors obey the required erasure laws. -/
abbrev appendix_parametricity_erasure_laws :=
  @DeepWiki.Refine.AnnotatedParametricityErasure.ErasureLaws

/-- **Theorem 0.C.1, conditional:** annotated translation erases to a raw sequent. -/
abbrev appendix_trocq_erasure_to_raw :=
  @DeepWiki.Refine.AnnotatedParametricityErasure.Judgment.eraseToRaw

/-- **Theorem 0.D.1:** maximal annotation lifts unannotated context formation. -/
abbrev maximal_annotation_well_formed :=
  @DeepWiki.Refine.MaximalAnnotation.wellFormed

/-- **Theorem 0.D.1:** maximal annotation lifts unannotated typing derivations. -/
abbrev maximal_annotation_typing :=
  @DeepWiki.Refine.MaximalAnnotation.hasType

/-- **Theorem 0.D.1:** maximal annotation lifts unannotated subtyping derivations. -/
abbrev maximal_annotation_subtyping :=
  @DeepWiki.Refine.MaximalAnnotation.subtypeDerivation

/-- **Figure 7, p. 20:** the scoped four-place Trocq synthesis judgment. -/
abbrev figure_7_trocq_translation := @DeepWiki.Refine.AnnotatedRelationTranslation.Judgment

/-- **Theorem 6, p. 20:** a scoped abstraction schema exposing the missing quotation bridge. -/
abbrev theorem_6_claim := DeepWiki.Refine.AnnotatedRelationTranslation.AbstractionClaim

/-- **Remark 4, pp. 20–21:** Theorem 6 and lawful quotation imply relation-witness typing. -/
abbrev remark_4_of_abstraction :=
  @DeepWiki.Refine.UniverseWitnessConsequences.universeRelationWitnessTyping_of_abstraction

/-- **Remark 5, p. 21:** admissibility constructs the semantic universe witness branchwise. -/
abbrev remark_5_semantic_universe_witness :=
  @DeepWiki.Refine.UniverseWitnessConsequences.semanticUniverseWitnessOfAdmissible

/-- **Remark 5, p. 21:** the semantic witness relation is indexed by the source annotation. -/
abbrev remark_5_semantic_relation_projection :=
  @DeepWiki.Refine.UniverseWitnessConsequences.semanticUniverseWitnessOfAdmissible_rel

/-- **Figure 8, p. 21:** the interface specifying the five object-language weakening equations. -/
abbrev figure_8_recursive_weakening :=
  DeepWiki.Refine.RecursiveWitnessWeakening.ObjectWeakeningSpecification

/-- **Figure 8, p. 21:** raw syntax equality cannot express even identity weakening. -/
abbrev figure_8_raw_identity_not_syntactic :=
  @DeepWiki.Refine.RecursiveWitnessWeakening.noSyntacticIdentityTransformer

/-- **Figure 8, p. 21:** the quoted identity transformer satisfies weakening by beta conversion. -/
abbrev figure_8_identity_beta :=
  @DeepWiki.Refine.RecursiveWitnessWeakening.identityWitnessTransformer_beta

/-- **Figure 8, p. 21:** realizability asks for an inhabitant of the weakening specification. -/
abbrev figure_8_recursive_weakening_realizability :=
  DeepWiki.Refine.RecursiveWitnessWeakening.ObjectWeakeningRealizability

/-- **Figure 8, p. 21:** semantic dependent-product weakening is contravariant then covariant. -/
abbrev figure_8_pi_weakening := @DeepWiki.Refine.RecursiveWitnessWeakening.piWitnessWeakening

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

/-- **Equation (12), p. 13:** exact quoted typing and projection obligations. -/
abbrev equation_12_quotation_specification :=
  @DeepWiki.Refine.StructuredUniverseQuotation.Quotation

/-- **Equation (12), p. 13:** admissibility gives the quoted witness equation. -/
abbrev equation_12_quoted_universe_equation :=
  @DeepWiki.Refine.StructuredUniverseQuotation.Quotation.satisfiesUniverseEquation

/-- **Equation (12), p. 13:** quoted relation projection remains convertible after application. -/
abbrev equation_12_quoted_relation_projection :=
  @DeepWiki.Refine.StructuredUniverseQuotation.Quotation.projectedRelationApplication_convertible

/-- **Equation (12), p. 13:** core-calculus quotation realizability remains explicit. -/
abbrev equation_12_core_quotation_realizability :=
  DeepWiki.Refine.StructuredUniverseQuotation.CoreQuotationRealizability

/-- **Remark 5, p. 21:** abstraction and quotation imply the translated universe conclusion. -/
abbrev remark_5_conclusion_of_abstraction :=
  @DeepWiki.Refine.StructuredUniverseQuotation.translatedTypeWitnessConclusion_of_abstraction

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
