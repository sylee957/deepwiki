import DeepWiki.Refine.TypeEquivalence
import Sources.Doi_10_1007_978_3_031_57262_3_10.Source

/-! # Section 2.2 - Type equivalences and univalence

Catalog pointers for the equivalence and univalence constructions of Section 2.2. -/

namespace DeepWiki.Ccm

/-- **Section 2.2, p. 6:** pointwise equality agrees with equality of functions. -/
abbrev pointwise_function_equality := @DeepWiki.Refine.pointwiseEq_iff_eq

/-- **Definition 1, p. 6:** a function is an isomorphism when it has a two-sided inverse. -/
abbrev type_isomorphism := @DeepWiki.Refine.IsomorphismData

/-- **Definition 1, p. 6:** coherent equivalence data relates the section and retraction proofs. -/
abbrev coherent_type_equivalence := @DeepWiki.Refine.CoherentEquivalenceData

/-- **Definition 1, p. 6:** type equivalence is the sigma of a map and equivalence evidence. -/
abbrev type_equivalence := @DeepWiki.Refine.TypeEquivalenceData

/-- **Definition 1, p. 6:** the paper's sigma presentation agrees with Lean's `Equiv`. -/
abbrev type_equivalence_equiv_lean := @DeepWiki.Refine.typeEquivalenceDataEquivEquiv

/-- **Lemma 1, p. 6:** every two-sided isomorphism yields a coherent equivalence in Lean. -/
abbrev isomorphism_is_equivalence := @DeepWiki.Refine.IsomorphismData.toCoherentEquivalence

/-- **Definition 1, p. 6:** coherent equivalence evidence is proof-irrelevant. -/
abbrev equivalence_evidence_is_proof_irrelevant :=
  @DeepWiki.Refine.coherentEquivalenceData_subsingleton

/-- **Section 2.2, pp. 6-7:** an equivalence supplies forward and backward transport maps. -/
abbrev equivalence_transport := @DeepWiki.Refine.TypeEquivalence

/-- **Section 2.2, p. 7:** arrow transfer is contravariant in its domain and covariant in its codomain. -/
abbrev equivalence_arrow_transport := @DeepWiki.Refine.TypeEquivalence.arrow

/-- **Definition 2, p. 7:** univalence makes equality-to-equivalence itself an isomorphism. -/
abbrev univalent_universe := DeepWiki.Refine.IsUnivalentUniverse

/-- **Definition 2, p. 7:** univalence evidence is proof-irrelevant. -/
abbrev univalence_is_proof_irrelevant := DeepWiki.Refine.isUnivalentUniverse_subsingleton

/-- **Lean modeling boundary:** standard proof-irrelevant universes have no such univalence data. -/
abbrev lean_univalent_universe_is_empty := @DeepWiki.Refine.isEmpty_isUnivalentUniverse

/-- **Section 2.2, p. 7:** univalence maps equivalent inputs to equivalent type-former outputs. -/
abbrev univalent_type_former_transport := @DeepWiki.Refine.IsUnivalentUniverse.mapTypeFormer

/-- **Section 2.2, p. 7:** univalence transports a proof along an input-type equivalence. -/
abbrev univalent_proof_transport := @DeepWiki.Refine.IsUnivalentUniverse.transportProof

end DeepWiki.Ccm
