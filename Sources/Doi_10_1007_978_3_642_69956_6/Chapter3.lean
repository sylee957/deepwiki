import DeepWiki.RelationalDatabases.FunctionalDependencies
import DeepWiki.RelationalDatabases.MultivaluedDependencies
import Sources.Doi_10_1007_978_3_642_69956_6.Source

/-! # Relational Database Model catalog — Chapter 3: Constraints
Chapter 3 studies the main types of relation constraints: functional dependencies (§3.2),
multivalued dependencies (§3.3), join dependencies (§3.4), inclusion dependencies (§3.5) and
the tuple/equality-generating dependencies (§3.6), with their implication problems and
axiomatizations. The `DeepWiki.RelationalDatabases` library formalizes the functional-dependency
core: satisfaction, Armstrong's axioms (sound), the syntactic derivation, and the attribute
closure characterization of implication.

## NOT YET FORMALIZED (audit 2026-06-23; subtractive — delete each item once it is formalized)
Axiom systems / algorithms are to be functional `def`s + correctness lemmas, not operational
semantics.
§3.1: Def 3.2 (a type of constraint), Def 3.3 (the implication problem), Def 3.4 (sound /
  complete / non-redundant axiom systems), Example 3.4 key-dependency axioms K1/K2 [infra: an
  abstract axiom-system framework over arbitrary constraint types].
§3.2: the non-redundancy of Armstrong's axioms (Theorem 3.2 — soundness and completeness are
  done); Theorem 3.1 derived rules F5 (intersection), F6 (reduction), F7 (generalized
  augmentation), F9 (generalized transitivity) [deferred]; Algorithm 3.1 / 3.2 (attribute-closure
  computation) with Theorem 3.3 / 3.5 correctness and Theorem 3.4 / 3.6 complexity [infra:
  functional fixpoint algorithm]; Def 3.6 non-redundant cover; Def 3.7 canonical cover and
  Example 3.10 [infra].
§3.3: Theorem 3.7 / 3.8 (an fd gives a lossless two-way decomposition, and its partial
  converse), Theorem 3.9 (an mvd holds iff the relation decomposes losslessly), the remaining
  axioms of system `𝓜` — M2 (mvd-augmentation), M3 (mvd-pseudotransitivity), FM2 (mixed
  pseudotransitivity); M1 and FM1 are done — Lemma 3.1 rules M4/M5/M6, Theorem 3.11 (dependency
  basis), Algorithm 3.3 with Theorem 3.12 / 3.13 (sound/complete/non-redundant) and Corollary 3.2
  (polynomial-time decidability) [infra].
§3.4: join dependencies — definition, the chase, acyclicity [infra/research].
§3.5: inclusion dependencies — definition, axioms, the (undecidable in general) implication
  problem [research].
§3.6: tuple- and equality-generating dependencies — definition and the chase [infra/research].
§3.7: Exercises [deferred: not yet transcribed]. -/

open DeepWiki

namespace DeepWiki.Rdb

/-! ## §3.1 / §3.2 Functional Dependencies -/

/-- **Definition 3.5** (§3.2, p.65): a row set satisfies the *functional dependency* `X → Y`
when any two rows agreeing on `X` agree on `Y`. -/
abbrev def_3_5 := @DeepWiki.SatisfiesFd

/-- **Agreement `t[X] = t'[X]`** (§3.2): two rows share every value on the attributes of `X`. -/
abbrev fd_agree := @DeepWiki.Agree

/-- **Definition 3.1** (§3.1, p.62), for fds: `SC` *implies* `X → Y` when every row set
satisfying all of `SC` satisfies `X → Y`. -/
abbrev def_3_1_implies := @DeepWiki.Implies

/-- **Armstrong's axiom F1** (§3.2, p.66, triviality): `X → Y` holds when `Y ⊆ X`. -/
abbrev fd_axiom_f1_trivial := @DeepWiki.satisfiesFd_trivial

/-- **Armstrong's axiom F2** (§3.2, p.66, augmentation): `X → Y` gives `X → X ∪ Y`. -/
abbrev fd_axiom_f2_augment := @DeepWiki.satisfiesFd_augment

/-- **Armstrong's axiom F3** (§3.2, p.66, transitivity): `X → Y` and `Y → Z` give `X → Z`. -/
abbrev fd_axiom_f3_trans := @DeepWiki.satisfiesFd_trans

/-- **Theorem 3.1, rule F4** (§3.2, p.66, union): `X → Y` and `X → Z` give `X → Y ∪ Z`. -/
abbrev thm_3_1_f4_union := @DeepWiki.satisfiesFd_unionRule

/-- **Theorem 3.1, rule F8** (§3.2, p.66, decomposition/fragmentation): `X → Y ∪ Z` gives
`X → Y`. -/
abbrev thm_3_1_f8_decompose := @DeepWiki.satisfiesFd_decompose

/-- **Theorem 3.1, rule F4 (syntactic)** (§3.2, p.66): `X → Y` and `X → Z` *derive* `X → Y ∪ Z`
using only Armstrong's axioms. -/
abbrev thm_3_1_f4_union_derived := @DeepWiki.derives_union

/-- **Armstrong's axiom system `𝓕`** (§3.2, Theorem 3.2, p.66): the syntactic derivation of
functional dependencies from `SC` by triviality, augmentation and transitivity. -/
abbrev fd_axiom_system := @DeepWiki.Derives

/-- **Theorem 3.2, soundness** (§3.2, p.67): every dependency derivable by Armstrong's axioms is
semantically implied. -/
abbrev thm_3_2_sound := @DeepWiki.derives_sound

/-- **Theorem 3.2, completeness** (§3.2, p.67): over a value type with ≥2 elements, every fd over
`Ω` semantically implied by `SC` is derivable by Armstrong's axioms — proved via the two-tuple
counterexample relation. With soundness this gives `SC⁺ = SC*` for functional dependencies. -/
abbrev thm_3_2_complete := @DeepWiki.derives_complete

/-- **fd-closure `X̄`** (§3.2, p.68): the attributes `A` with `SC ⊨ X → A`. -/
abbrev fd_closure := @DeepWiki.fdClosure

/-- **fd-closure characterization** (§3.2, p.68): `SC ⊨ X → Y` iff every attribute of `Y` lies
in the fd-closure `X̄` — the basis of the closure decision procedure. -/
abbrev fd_closure_characterization := @DeepWiki.implies_iff_subset_fdClosure

/-! ## §3.3 Multivalued Dependencies -/

/-- **Definition 3.8** (§3.3, p.78): a row set satisfies the *multivalued dependency* `X ↠ Y`
when, for any two rows agreeing on `X`, the `Y`-versus-`(Ω − Y)` tuple swap stays in the
relation. -/
abbrev def_3_8 := @DeepWiki.SatisfiesMvd

/-- **Corollary 3.1, rule FM1** (§3.3, p.79): every functional dependency is a multivalued
dependency — `X → Y` gives `X ↠ Y`. -/
abbrev cor_3_1_fd_to_mvd := @DeepWiki.satisfiesMvd_of_satisfiesFd

/-- **Corollary 3.1, rule M1** (§3.3, p.79, complementation): `X ↠ Y` gives `X ↠ Ω − Y`. -/
abbrev cor_3_1_complement := @DeepWiki.satisfiesMvd_complement

end DeepWiki.Rdb
