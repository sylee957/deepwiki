import DeepWiki.Refine.ParametricityTranslations
import DeepWiki.Refine.RawParametricityAbstraction
import DeepWiki.Refine.RawParametricitySyntax
import DeepWiki.Refine.RawParametricityTyping
import DeepWiki.Refine.UnivalentUniverseQuotation
import Sources.Doi_10_1145_3737283.Source

/-! # Section 3.3 - Parametricity translations

Catalog pointers for the raw and univalent parametricity constructions in the revised paper.

## NOT YET FORMALIZED

- Figure 2 (complete univalent term translation), PDF p. 11 — [infra] the universe package,
  relation projection, and intrinsic term fragment exist, but the complete dependent translation
  still requires realizers for its universe and dependent-product package constructors.
- Theorem 3.6 (univalent abstraction for full dependent `CCω`), PDF p. 11 — [infra] the intrinsic
  abstraction theorem exists, but the exact full-calculus typing induction does not.
-/

namespace DeepWiki.CcmToplas

noncomputable section

/-- **Equation (1), PDF p. 10:** raw translation preserves the empty context. -/
abbrev equation_1_raw_empty_context_translation :=
  DeepWiki.Refine.DependentCalculus.RawParametricity.context_empty

/-- **Equation (2), PDF p. 10:** a declaration translates to original, primed, and relation-witness declarations. -/
abbrev equation_2_raw_context_extension_translation :=
  @DeepWiki.Refine.DependentCalculus.RawParametricity.context_extend

/-- **Equation (3), PDF p. 10:** a universe translates to the heterogeneous-relation family. -/
abbrev equation_3_raw_universe_translation :=
  @DeepWiki.Refine.DependentCalculus.RawParametricity.translate_sort

/-- **Equation (4), PDF p. 10:** a variable translates to its relation-witness variable. -/
abbrev equation_4_raw_variable_translation :=
  @DeepWiki.Refine.DependentCalculus.RawParametricity.translate_var

/-- **Equation (5), PDF p. 10:** application translation supplies original, primed, and relational arguments. -/
abbrev equation_5_raw_application_translation :=
  @DeepWiki.Refine.DependentCalculus.RawParametricity.translate_app

/-- **Equation (6), PDF p. 10:** lambda translation binds original, primed, and related arguments. -/
abbrev equation_6_raw_lambda_translation :=
  @DeepWiki.Refine.DependentCalculus.RawParametricity.translate_lam

/-- **Equation (7), PDF p. 10:** product translation relates functions on related arguments. -/
abbrev equation_7_raw_product_translation :=
  @DeepWiki.Refine.DependentCalculus.RawParametricity.translate_pi

/-- **Equation (8), PDF p. 9:** the raw universe relation is well typed one level higher. -/
abbrev equation_8_raw_universe_translation_is_well_typed :=
  DeepWiki.Refine.DependentCalculus.RawParametricity.rawUniverseTranslation_hasType

/-- **Theorem 3.4, PDF p. 9:** ordinary `CCω` typing implies the three displayed raw-abstraction conclusions. -/
abbrev theorem_3_4_raw_abstraction :=
  @DeepWiki.Refine.DependentCalculus.RawParametricity.displayedRawAbstraction

/-- **Theorem 3.4 auxiliary, PDF p. 9:** formation-explicit typing yields both term copies and their relation witness. -/
abbrev theorem_3_4_formation_explicit_abstraction :=
  @DeepWiki.Refine.DependentCalculus.RawParametricity.formationExplicitRawAbstraction

/-- **Equation (9), PDF p. 10:** a univalent universe relation packages an equivalence and equality-graph coherence. -/
abbrev equation_9_univalent_universe_translation :=
  @DeepWiki.Refine.UnivalentRelation

/-- **Theorem 3.5, PDF p. 10:** under univalence, universe packages are equivalent to type equivalences. -/
abbrev theorem_3_5_univalent_relation_equiv_type_equivalence :=
  @DeepWiki.Refine.univalentRelationEquivTypeEquivalence

/-- **Figure 2, PDF p. 11:** using a translated type projects the relation from its universe package. -/
abbrev figure_2_type_relation_projection :=
  @DeepWiki.Refine.UnivalentRelation.rel

/-- **Equation (17), PDF p. 11, semantic counterpart:** univalence supplies the native universe package. -/
abbrev equation_17_semantic_universe_package :=
  @DeepWiki.Refine.univalentUniverseRelation

/-- **Equation (17), PDF p. 11:** the quoted universe package has the required translated type. -/
abbrev equation_17_quoted_universe_typing :=
  @DeepWiki.Refine.DependentCalculus.UnivalentUniverseQuotation.termTranslation_hasType

/-- **Theorem 3.6, PDF p. 11, intrinsic fragment:** abstraction restricted to a projected univalent relation. -/
abbrev theorem_3_6_intrinsic_univalent_abstraction :=
  @DeepWiki.Refine.CoreTerm.univalentParametricity

end


end DeepWiki.CcmToplas
