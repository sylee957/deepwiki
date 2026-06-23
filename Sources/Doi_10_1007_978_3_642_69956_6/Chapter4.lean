import DeepWiki.RelationalDatabases.NormalForms
import DeepWiki.RelationalDatabases.DependencyImplication
import Sources.Doi_10_1007_978_3_642_69956_6.Source

/-! # Relational Database Model catalog — Chapter 4: Vertical Decompositions
Chapter 4 develops the normal forms that govern how a relation scheme should be decomposed: first
normal form (§4.1), second and third (§4.2), Boyce–Codd (§4.3), constraint-preserving
normalization (§4.4) and fourth/fifth normal form (§4.5). The `DeepWiki.RelationalDatabases`
library formalizes keys and the functional-dependency normal forms with the hierarchy
`BCNF ⟹ 3NF ⟹ 2NF`.

## NOT YET FORMALIZED (audit 2026-06-23; subtractive — delete each item once it is formalized)
Decomposition algorithms are to be functional `def`s + correctness lemmas, not operational
semantics.
§4.1: first normal form (informal — "all domain values are atomic"; deliberately not a formal
  definition in the book) [external].
§4.2: Def 4.4 (a projection of a set of fds onto an attribute set), Algorithm 4.1 (decomposition
  into 3NF) with Theorem 4.1 (correctness), Theorem 4.2 (deciding primality is NP-complete)
  [infra/research].
§4.3: Algorithm 4.2 (decomposition into BCNF) with Theorem 4.4 (correctness), Theorem 4.5
  (deciding BCNF is NP-complete) [infra/research].
§4.4: Def 4.6 (constraint-preserving representation / decomposition), Algorithm 4.3 (the
  synthesis algorithm) with Theorem 4.6 and Corollary 4.1 (every scheme has a constraint-preserving
  3NF decomposition), Example 4.10 (redundant schemes survive) [infra]. (Def 4.3 lossless-join
  decomposition is done.)
§4.5: Def 4.8 (fifth normal form / project-join normal form) with Theorem 4.8 (5NF ⟹ 4NF)
  [infra: needs join-dependency implication; the mvd-implication relation, Def 4.7 fourth normal
  form and Theorem 4.7 (4NF ⟹ BCNF) are done].
§4.6: vertical decomposition and consistency checking [infra].
§4.7: Exercises [deferred: not yet transcribed]. -/

open DeepWiki

namespace DeepWiki.Rdb

/-! ## §4.2 Keys and Normal Forms -/

/-- **Definition 4.1** (§4.2, p.114): `X` is a *superkey* of `RS` when `SC ⊨ X → Ω`. -/
abbrev def_4_1_superkey := @DeepWiki.IsSuperkey

/-- **Definition 4.1** (§4.2, p.114): `X` is a *key* — a superkey with no proper subset a
superkey. -/
abbrev def_4_1_key := @DeepWiki.IsKey

/-- **Definition 4.1** (§4.2, p.114): `A` is a *prime attribute* — it belongs to some key. -/
abbrev def_4_1_prime := @DeepWiki.IsPrime

/-- **Definition 4.2** (§4.2, p.115): `RS` is in *third normal form* — every implied `Y → A` has
`A ∈ Y`, or `A` prime, or `Y` a superkey. -/
abbrev def_4_2_3nf := @DeepWiki.Is3NF

/-- **Definition 4.2** (§4.2, p.115): `RS` is in *second normal form* — no non-prime attribute
depends on a proper subset of a key. -/
abbrev def_4_2_2nf := @DeepWiki.Is2NF

/-! ## §4.3 Boyce–Codd Normal Form -/

/-- **Definition 4.5** (§4.3, p.119): `RS` is in *Boyce–Codd normal form* — every implied
`Y → A` has `A ∈ Y` or `Y` a superkey. -/
abbrev def_4_5_bcnf := @DeepWiki.IsBCNF

/-- **Theorem 4.3** (§4.3, p.119): every Boyce–Codd normal form relation scheme is in third
normal form. -/
abbrev thm_4_3 := @DeepWiki.is3NF_of_isBCNF

/-- **Third implies second normal form** (§4.2, p.115): every 3NF relation scheme is in 2NF. -/
abbrev nf_2nf_of_3nf := @DeepWiki.is2NF_of_is3NF

/-! ## §4.4 Constraint Preserving Normalization -/

/-- **Definition 4.3** (§4.2, p.116): a *lossless-join decomposition* — components covering `Ω`
such that every instance satisfying `SC` equals the join of its projections. -/
abbrev def_4_3_lossless_join := @DeepWiki.IsLosslessJoinDecomp

/-- **Trivial lossless decomposition** (§4.4): the single-component decomposition `{Ω}` is
lossless. -/
abbrev lossless_join_single := @DeepWiki.isLosslessJoinDecomp_single

/-! ## §4.5 Fourth Normal Form -/

/-- **Mixed dependency** (§4.5): a functional or multivalued dependency over a scheme, the alphabet
of the mixed implication relation. -/
abbrev dep := @DeepWiki.Dep

/-- **Mixed dependency implication** (§4.5): `D ⊨ d` — every relation satisfying the dependency
set `D` satisfies `d`. -/
abbrev dep_implies := @DeepWiki.DepImplies

/-- **Superkey via implication** (§4.5, cf. Def 4.1): `D ⊨ X → Ω`. -/
abbrev superkey_dep := @DeepWiki.IsSuperkeyDep

/-- **Definition 4.7** (§4.5, p.135): a scheme is in *fourth normal form* when every nontrivial
implied multivalued dependency has a superkey left-hand side. -/
abbrev def_4_7_4nf := @DeepWiki.Is4NF

/-- **Definition 4.5 (implication form)** (§4.5): Boyce–Codd normal form stated over the mixed
implication relation. -/
abbrev def_4_5_bcnf_dep := @DeepWiki.IsBCNFDep

/-- **Theorem 4.7** (§4.5, p.135): a relation scheme in fourth normal form is in Boyce–Codd
normal form. -/
abbrev thm_4_7 := @DeepWiki.isBCNFDep_of_is4NF

end DeepWiki.Rdb
