import DeepWiki.Refine.Examples.BinaryNaturals
import DeepWiki.Refine.RetractiveNaturalInduction
import DeepWiki.Refine.ExtendedNonnegativeSums
import DeepWiki.Refine.BitVectorRepresentation
import DeepWiki.Refine.IntegerModularRetraction
import DeepWiki.Refine.SummableSequenceTransfer
import DeepWiki.Refine.PolymorphicListRelations
import DeepWiki.Refine.TupleVectorTransfer
import Sources.Doi_10_1007_978_3_031_57262_3_10.Source

/-! # Trocq applications - coverage catalog

Coverage map for the motivating examples and concrete applications demonstrated by the Trocq
plugin.

## NOT YET FORMALIZED

- Section 5.1 bitvector tactic execution, pp. 22–23 — [infra] the representations, equivalence,
  dependent `get`/`set` witnesses, source theorem, and transferred target theorem are formalized;
  plugin registration, constraint solving, and automatic goal rewriting remain.
- Section 5.1 natural-induction tactic execution, p. 23 — [infra] the generic retractive carrier,
  exact `(2a,3)` relation, zero/successor witnesses, and inherited dependent eliminator are
  formalized; automatic weakest-annotation inference and goal rewriting remain.
- Section 5.2 modular-arithmetic tactic execution, pp. 23–24 — [infra] the retraction, zero,
  multiplication, equality witnesses, and exact quantified implication are formalized; plugin
  registration and automatic goal synthesis remain.
- Section 5.2 summable-sequence tactic execution, pp. 24–25 — [infra] both nested refinements, all
  three operation witnesses, and both displayed additivity lemmas are formalized; plugin
  registration and automatic goal rewriting remain.
- Section 5.3 polymorphic-list tactic execution, p. 25 — [infra] the top and `(2a,4)` list lifts and
  the exact weakening obstruction are formalized; plugin lookup, stuck-state reporting, and
  annotation-aware selection of the weaker lift remain.
- Section 5.3 dependent-vector tactic execution, pp. 25–26 — [infra] iterated tuples, their vector
  equivalence, `head`/`const` witnesses, the integer-to-modular container retraction, and both
  displayed laws are formalized; plugin registration and automatic simultaneous transfer remain.
-/

namespace DeepWiki.Ccm

noncomputable section

/-- **Example 1, pp. 1–2:** the computation-oriented canonical binary natural numbers. -/
abbrev example_1_binary_natural := DeepWiki.Refine.BinaryNat

/-- **Example 1, p. 2:** successor on canonical binary natural numbers. -/
abbrev example_1_binary_successor := DeepWiki.Refine.BinaryNat.succ

/-- **Example 1, p. 2:** conversion from unary to binary natural numbers. -/
abbrev example_1_encode := DeepWiki.Refine.BinaryNat.ofNat

/-- **Example 1, p. 2:** conversion from binary to unary natural numbers. -/
abbrev example_1_decode := DeepWiki.Refine.BinaryNat.toNat

/-- **Example 1, p. 2:** decoding and encoding are inverse conversions. -/
abbrev example_1_decode_encode := DeepWiki.Refine.BinaryNat.toNat_ofNat

/-- **Example 1, p. 2:** encoding and decoding are inverse conversions. -/
abbrev example_1_encode_decode := DeepWiki.Refine.BinaryNat.ofNat_toNat

/-- **Example 1, p. 2:** decoding binary zero gives unary zero. -/
abbrev example_1_decode_zero := DeepWiki.Refine.BinaryNat.toNat_zero

/-- **Example 1, p. 2:** decoding commutes with successor. -/
abbrev example_1_decode_successor := DeepWiki.Refine.BinaryNat.toNat_succ

/-- **Example 1, p. 2:** unary dependent elimination transferred to binary natural numbers. -/
abbrev example_1_binary_induction := @DeepWiki.Refine.binaryNatEliminator

/-- **Example 1, p. 2:** binary elimination recovers unary elimination from decoding compatibility. -/
abbrev example_1_reverse_induction := @DeepWiki.Refine.unaryNatEliminatorOfBinary

/-- **Example 2, pp. 2–3:** the subtype of summable nonnegative-real sequences. -/
abbrev example_2_summable_sequence := DeepWiki.Refine.SummableNNSequence

/-- **Example 2, pp. 2–3:** the refinement relation from finite to extended nonnegative values. -/
abbrev example_2_finite_value_relation := DeepWiki.Refine.FiniteENNRealRel

/-- **Example 2, pp. 2–3:** pointwise extension relates summable and extended sequences. -/
abbrev example_2_sequence_relation := DeepWiki.Refine.SummableNNSequenceRel

/-- **Example 2, p. 3:** unconditional additivity of infinite sums in the extended domain. -/
abbrev example_2_extended_sum_add := @DeepWiki.Refine.extendedNNSum_add

/-- **Equation (1), pp. 2–3:** additivity transferred back to summable nonnegative sequences. -/
abbrev example_2_eq_1 := @DeepWiki.Refine.summableNNSequence_sum_add

/-- **Section 5.1, p. 22:** bounded naturals encode fixed-width bitvectors. -/
abbrev bitvector_bounded_natural := DeepWiki.Refine.BoundedNat

/-- **Section 5.1, p. 22:** fixed-width Boolean list vectors encode bitvectors. -/
abbrev bitvector_vector := DeepWiki.Refine.BitVector

/-- **Section 5.1, p. 22:** bounded naturals and Boolean vectors are equivalent. -/
abbrev bitvector_equivalence := DeepWiki.Refine.boundedNatBitVectorEquiv

/-- **Section 5.1, p. 22:** the representation equivalence carries annotation `(4,4)`. -/
abbrev bitvector_relation := @DeepWiki.Refine.boundedNatBitVectorStructuredRelation

/-- **Section 5.1, pp. 22–23:** vector reads respect the dependent representation relation. -/
abbrev bitvector_get_witness := @DeepWiki.Refine.boundedNatBitVector_get_rel

/-- **Section 5.1, pp. 22–23:** vector writes respect the dependent representation relation. -/
abbrev bitvector_set_witness := @DeepWiki.Refine.boundedNatBitVector_set_rel

/-- **Section 5.1, p. 22:** get-after-set for the direct bounded-natural bit operations. -/
abbrev bitvector_source_get_set := @DeepWiki.Refine.boundedNat_get_set_same

/-- **Section 5.1, p. 23:** the round-trip transfer recovers vector get-after-set. -/
abbrev bitvector_transferred_get_set := @DeepWiki.Refine.bitVector_get_set_same_of_boundedNat

/-- **Section 5.1, p. 23:** a natural retraction carries exactly the selected `(2a,3)` structure. -/
abbrev induction_retractive_relation := @DeepWiki.Refine.retractiveNatStructuredRelation

/-- **Section 5.1, p. 23:** compatible zero values are related. -/
abbrev induction_zero_witness := @DeepWiki.Refine.retractiveNatZeroRelated

/-- **Section 5.1, p. 23:** compatible successor operations preserve the relation. -/
abbrev induction_successor_witness := @DeepWiki.Refine.retractiveNatSuccRelated

/-- **Section 5.1, p. 23:** a retractive representation inherits dependent natural induction. -/
abbrev induction_from_retraction := @DeepWiki.Refine.retractiveNatEliminator

/-- **Section 5.2, p. 24:** integer reduction to `ZMod` carries annotation `(4,2a)`. -/
abbrev modular_retraction := DeepWiki.Refine.intZModRetraction

/-- **Section 5.2, p. 24:** integer and modular zero are related. -/
abbrev modular_zero_witness := DeepWiki.Refine.intZModZero_related

/-- **Section 5.2, p. 24:** integer and modular multiplication are related. -/
abbrev modular_multiplication_witness := DeepWiki.Refine.intZModMul_related

/-- **Section 5.2, p. 24:** modular equality implies equality modulo the integer modulus. -/
abbrev modular_equality_witness := DeepWiki.Refine.intZModEq_related

/-- **Section 5.2, pp. 23–24:** the displayed modular implication transfers to integers. -/
abbrev modular_integer_reduction := DeepWiki.Refine.intReductionModZMod

/-- **Section 5.2, p. 24:** finite-value extension carries annotation `(4,2b)`. -/
abbrev summable_finite_value_relation := DeepWiki.Refine.finiteENNRealStructuredRelation

/-- **Section 5.2, pp. 24–25:** finite-sum sequence extension carries annotation `(4,2b)`. -/
abbrev summable_sequence_relation := DeepWiki.Refine.finiteSumNNSequenceStructuredRelation

/-- **Section 5.2, p. 25:** value addition preserves the finite-to-extended relation. -/
abbrev summable_value_addition_witness := DeepWiki.Refine.finiteENNRealGraph_add

/-- **Section 5.2, p. 25:** pointwise addition preserves the sequence relation. -/
abbrev summable_sequence_addition_witness := DeepWiki.Refine.finiteSumNNSequenceGraph_add

/-- **Section 5.2, p. 25:** summation preserves the nested refinement relations. -/
abbrev summable_sum_witness := DeepWiki.Refine.finiteSumNNSequenceGraph_sum

/-- **Section 5.2, p. 25:** extended sums distribute over pointwise addition. -/
abbrev summable_extended_additivity := DeepWiki.Refine.extendedNNSequenceSum_add

/-- **Section 5.2, p. 25:** finite sums inherit additivity through the registered witnesses. -/
abbrev summable_finite_additivity := DeepWiki.Refine.FiniteSumNNSequence.sum_add

/-- **Section 5.3, p. 25:** top-structured element relations lift pointwise to lists. -/
abbrev polymorphic_list_equivalence_lift := @DeepWiki.Refine.StructuredRelation.listTop

/-- **Section 5.3, p. 25:** `(2a,4)` element relations lift pointwise to lists. -/
abbrev polymorphic_list_weaker_lift := @DeepWiki.Refine.StructuredRelation.listTwoAFour

/-- **Section 5.3, p. 25:** top-only lookup cannot consume a `(2a,4)` element relation. -/
abbrev polymorphic_list_top_lookup_obstruction :=
  DeepWiki.Refine.not_equivalence_le_twoAFour

/-- **Section 5.3, pp. 25–26:** iterated tuples are equivalent to fixed-length vectors. -/
abbrev dependent_vector_equivalence := DeepWiki.Refine.iteratedTupleVectorEquiv

/-- **Section 5.3, p. 26:** related elements generate related constant tuples and vectors. -/
abbrev dependent_vector_const_witness := @DeepWiki.Refine.tupleVectorConst_related

/-- **Section 5.3, p. 26:** heads of related nonempty tuples and vectors are related. -/
abbrev dependent_vector_head_witness := @DeepWiki.Refine.tupleVectorHead_related

/-- **Section 5.3, p. 26:** integer vectors refine to modular iterated tuples by a retraction. -/
abbrev dependent_vector_modular_retraction :=
  DeepWiki.Refine.integerVectorModularTupleRetraction

/-- **Section 5.3, p. 26:** the displayed source law holds for constant integer vectors. -/
abbrev dependent_vector_source_head_const := @DeepWiki.Refine.vectorHead_replicate

/-- **Section 5.3, p. 26:** the displayed modular tuple law follows through integer refinement. -/
abbrev dependent_vector_transferred_head_const :=
  DeepWiki.Refine.modularTuple_head_const_viaInteger

end

end DeepWiki.Ccm
