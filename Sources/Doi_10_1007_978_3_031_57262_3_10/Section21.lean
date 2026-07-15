import DeepWiki.Refine.ProofTransfer
import DeepWiki.Refine.CCOmega.Syntax
import Sources.Doi_10_1007_978_3_031_57262_3_10.Source

/-! # Section 2.1 — Proof transfer in type theory

Catalog pointers for the proof-transfer problem and motivating constructions of Section 2.1. -/

namespace DeepWiki.Ccm

/-- **Section 2.1, p. 5:** the syntax recalled for the dependent calculus. -/
abbrev proof_transfer_syntax := DeepWiki.Refine.DependentCalculus.Term

/-- **Section 2.1, p. 5:** a solution synthesizes `W` and the uniform witness relating `V` to `W`. -/
abbrev proof_transfer_solution := @DeepWiki.Refine.TypeFormerTransferSolution

/-- **Section 2.1, p. 5:** the common carrier/zero/successor interface for induction transfer. -/
abbrev natural_number_interface := DeepWiki.Refine.NatSignature

/-- **Section 2.1 boundary:** identity successor is a formal counterexample to arbitrary induction. -/
abbrev identity_successor_has_no_induction :=
  DeepWiki.Refine.not_identitySuccessorNatSignature_induction

/-- **Section 2.1, pp. 5–6:** interface equivalence transfers the induction principle. -/
abbrev induction_transfer := @DeepWiki.Refine.NatSignatureEquiv.induction_iff

/-- **Section 2.1, p. 6:** the displayed `W″` inserts a down-up round trip at successor. -/
abbrev reencoded_induction := @DeepWiki.Refine.NatSignature.reencode_induction

/-- **Section 2.1, p. 6:** a functional relation yields the pullback `W = V ∘ φ`. -/
abbrev functional_pullback := @DeepWiki.Refine.functionalPullbackSolution

/-- **Section 2.1, p. 6:** structural conjugation produces the weak `W″` induction candidate. -/
abbrev structural_induction_candidate :=
  @DeepWiki.Refine.NatOperationPair.functionalPullback_target

end DeepWiki.Ccm
