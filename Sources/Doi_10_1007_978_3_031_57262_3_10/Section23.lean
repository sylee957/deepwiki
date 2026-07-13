import DeepWiki.Refine.ParametricityTranslations
import Sources.Doi_10_1007_978_3_031_57262_3_10.Source

/-! # Section 2.3 - Parametricity translations

Catalog pointers for the raw and univalent parametricity constructions of Section 2.3. -/

namespace DeepWiki.Ccm

noncomputable section

/-- **Equation (4), p. 8:** a raw universe relates types by arbitrary proof-relevant relations. -/
abbrev raw_universe_translation := @DeepWiki.Refine.RawUniverseRelation

/-- **Equation (9), p. 7:** the raw universe translation is itself well-typed one level higher. -/
abbrev raw_universe_translation_is_well_typed := @DeepWiki.Refine.rawUniverseTranslation

/-- **Equations (2)-(3), p. 8:** context translation stores paired values and relation witnesses. -/
abbrev raw_context_translation := @DeepWiki.Refine.CoreEnv.ProofRelevantRel

/-- **Equation (5), p. 8:** a translated variable denotes its relation witness from the context. -/
abbrev raw_variable_translation := @DeepWiki.Refine.CoreEnv.ProofRelevantRel.get

/-- **Equation (6), p. 8:** raw application composes function and argument witnesses. -/
abbrev raw_application_translation := @DeepWiki.Refine.RawPiRelation.app

/-- **Equation (7), p. 8:** raw lambda translation abstracts over paired related arguments. -/
abbrev raw_lambda_translation := @DeepWiki.Refine.RawPiRelation.lam

/-- **Equation (8), p. 8:** the relational interpretation of a dependent product. -/
abbrev raw_product_translation := @DeepWiki.Refine.RawPiRelation

/-- **Theorem 1, p. 7, intrinsic fragment:** abstraction produces both terms and their witness. -/
abbrev raw_abstraction_core := @DeepWiki.Refine.CoreTerm.rawAbstractionResult

/-- **Equation (10), p. 8:** a univalent relation packages `R`, `A ≃ B`, and graph coherence. -/
abbrev univalent_universe_translation := @DeepWiki.Refine.UnivalentRelation

/-- **Section 2.3, p. 8:** univalence identifies universe packages with type equivalences. -/
abbrev univalent_relation_equiv_type_equivalence :=
  @DeepWiki.Refine.univalentRelationEquivTypeEquivalence

/-- **Section 2.3, p. 8:** a type translation is the relation projection of its term package. -/
abbrev univalent_relation_projection := @DeepWiki.Refine.UnivalentRelation.rel

/-- **Theorem 2, p. 9, intrinsic fragment:** univalent abstraction produces the theorem triple. -/
abbrev univalent_abstraction_core := @DeepWiki.Refine.CoreTerm.univalentAbstractionResult

/-- **Equation (11), p. 9:** under univalence, the translated universe is a valid package. -/
abbrev translated_universe_is_well_typed := @DeepWiki.Refine.univalentUniverseRelation

/-- **Equation (11), p. 9:** the relation projection of the universe term is its type translation. -/
abbrev translated_universe_relation_projection :=
  @DeepWiki.Refine.univalentUniverseRelation_rel

example {A B : Type u} (equivalence : A ≃ B) :
    DeepWiki.Refine.UnivalentRelation A B :=
  DeepWiki.Refine.UnivalentRelation.ofEquiv equivalence

example (univalent : DeepWiki.Refine.IsUnivalentUniverse.{u}) (A B : Type u) :
    DeepWiki.Refine.UnivalentRelation A B ≃ (A ≃ B) :=
  DeepWiki.Refine.univalentRelationEquivTypeEquivalence univalent A B

example (A B : Type u) :
    DeepWiki.Refine.rawUniverseTranslation A B = (A → B → Type u) :=
  DeepWiki.Refine.rawUniverseTranslation_apply A B

example (univalent : DeepWiki.Refine.IsUnivalentUniverse.{u}) :
    (DeepWiki.Refine.univalentUniverseRelation univalent).rel =
      DeepWiki.Refine.UnivalentRelation :=
  DeepWiki.Refine.univalentUniverseRelation_rel univalent

example {A B : Type u} (package : DeepWiki.Refine.UnivalentRelation A B)
    (term : DeepWiki.Refine.CoreTerm context type)
    {leftEnv : DeepWiki.Refine.CoreEnv A context}
    {rightEnv : DeepWiki.Refine.CoreEnv B context}
    (contextWitness : DeepWiki.Refine.CoreEnv.ProofRelevantRel package.rel leftEnv rightEnv) :
    DeepWiki.Refine.CoreType.proofRelevantRel package.rel type
      (term.evaluate leftEnv) (term.evaluate rightEnv) :=
  term.univalentParametricity package contextWitness

example {A B : Type u} {R : A → B → Type u}
    (term : DeepWiki.Refine.CoreTerm context type)
    (leftEnv : DeepWiki.Refine.CoreEnv A context)
    (rightEnv : DeepWiki.Refine.CoreEnv B context)
    (contextWitness : DeepWiki.Refine.CoreEnv.ProofRelevantRel R leftEnv rightEnv) :
    DeepWiki.Refine.CoreTerm.RawAbstractionResult R type :=
  term.rawAbstractionResult leftEnv rightEnv contextWitness

end

end DeepWiki.Ccm
