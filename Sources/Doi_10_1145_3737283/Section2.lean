import DeepWiki.Refine.Examples.ProofTransferArithmetic
import Sources.Doi_10_1145_3737283.Source

/-! # Trocq Section 2 - coverage catalog

Coverage map for the four proof-transfer examples and their arithmetic proposition.

## NOT YET FORMALIZED
-/

namespace DeepWiki.CcmToplas

/-- **Example 2.1, p. 4:** the ground-product comparison transported to binary naturals. -/
abbrev example_2_1 :=
  DeepWiki.Refine.binaryMultiplicationBenchmark_ltb_eq_true

/-- **Example 2.2, p. 4:** dependent induction transferred to canonical binary naturals. -/
abbrev example_2_2 := @DeepWiki.Refine.binaryNatEliminator

/-- **Example 2.3, p. 5:** the modular computation proves divisibility by nine. -/
abbrev example_2_3 := DeepWiki.Refine.nine_dvd_groundProduct

/-- **Example 2.4, p. 5:** units modulo nine obstruct the cubic equation. -/
abbrev example_2_4 :=
  DeepWiki.Refine.zmodNine_cubic_ne_of_mul_isUnit

/-- **Proposition 2.5, p. 5:** a nonzero product modulo three obstructs the cubic equation. -/
abbrev prop_2_5 := DeepWiki.Refine.nat_cubic_ne_of_three_not_dvd_mul

end DeepWiki.CcmToplas
