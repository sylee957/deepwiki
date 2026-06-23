import DeepWiki.RelationalDatabases.UpdatesTransactions
import Sources.Doi_10_1007_978_3_642_69956_6.Source

/-! # Relational Database Model catalog — Chapter 8: Updates
Chapter 8 studies updates: the insertion/deletion/modification operators and transactions (§8.1),
equivalence of transactions and its decision algorithm (§8.2), dynamic relation constraints
specified by parameterized transactions (§8.3) and an axiomatization of transaction equivalence
(§8.4). The `DeepWiki.RelationalDatabases` library formalizes the deletion and insertion
operators, their distribution over union, and several equivalence rules.

## NOT YET FORMALIZED (audit 2026-06-23; subtractive — delete each item once it is formalized)
§8.1: the structured-`C'` modification `Mod(C, C', r)` where `C'` overrides the named attributes
  (the general function-model `Mod(C, m, r)` is done), and the structured elementary conditions
  `A = a` / `A ≠ a` (Def 8.1; here conditions are modelled as predicates) [infra].
§8.2: Def 8.5 (a transaction as a sequence of actions), Def 8.6 (equivalent transactions),
  Def 8.7 (domain-tuples / domain-sets), Lemma 8.2, Algorithm 8.1 (polynomial equivalence
  decision) and Theorem 8.1 (its correctness) [infra: needs the transaction/action syntax].
§8.3: Def 8.8 (parameterized transactions), Def 8.9 (a constraint set specified by parameterized
  transactions), Theorem 8.2 (every set of fds is so specified) and Theorem 8.3 (a non-trivial
  set of mvds is not) [infra/research].
§8.4: the transaction-equivalence rules involving `Mod` — E1, E4–E7, E10, E12–E18 (E2, E3, E8,
  a deletion case of E9, E11 and Def 8.10 independence are done) [infra: needs the `Mod`
  operator].
§8.5: Exercises [deferred: not yet transcribed]. -/

open DeepWiki

namespace DeepWiki.Rdb

/-! ## §8.1 Transactions (deletion and insertion) -/

/-- **Condition** (§8.1, Def 8.1/8.2, p.202): the tuples an update applies to, modelled as a
predicate. -/
abbrev def_8_1_condition := @DeepWiki.Condition

/-- **Definition 8.4** (§8.1, p.204), deletion: `Del(C, r)` removes the tuples satisfying `C`. -/
abbrev def_8_4_deletion := @DeepWiki.Del

/-- **Definition 8.4** (§8.1, p.204), insertion: `Ins(C, r)` adds the tuples satisfying `C`. -/
abbrev def_8_4_insertion := @DeepWiki.Ins

/-- **Definition 8.4** (§8.1, p.204), modification (function model): `Mod(C, m, r)` replaces each
`C`-tuple by its image under `m`. -/
abbrev def_8_4_modification := @DeepWiki.Mod

/-- **Rule E1** (§8.4, p.211, function-model form): `Mod(C, id, r) = r` — modifying by the
identity is a no-op. -/
abbrev e1_mod_id := @DeepWiki.Mod_id

/-! ## §8.2 Equivalent Transactions -/

/-- **Lemma 8.1** (§8.2, p.207), deletion case: `Del(C, r₁ ∪ r₂) = Del(C, r₁) ∪ Del(C, r₂)`. -/
abbrev lemma_8_1_del := @DeepWiki.Del_union

/-- **Lemma 8.1** (§8.2, p.207), insertion case: `Ins(C, r₁ ∪ r₂) = Ins(C, r₁) ∪ Ins(C, r₂)`. -/
abbrev lemma_8_1_ins := @DeepWiki.Ins_union

/-! ## §8.4 Axiomatization of Equivalence -/

/-- **Rule E2** (§8.4, p.212): an insertion followed by deleting the same condition equals the
deletion. -/
abbrev e2_ins_then_del := @DeepWiki.Del_Ins

/-- **Rule E3** (§8.4, p.212): a deletion followed by inserting the same condition equals the
insertion. -/
abbrev e3_del_then_ins := @DeepWiki.Ins_Del

/-- **Rule E9** (§8.4, p.213, deletion case): two deletions commute. -/
abbrev e9_del_comm := @DeepWiki.Del_Del_comm

/-- **Rule E8** (§8.4, p.212): two insertions commute. -/
abbrev e8_ins_comm := @DeepWiki.Ins_Ins_comm

/-- **Definition 8.10** (§8.4, p.212): two condition sets are *independent* when no tuple
satisfies both. -/
abbrev def_8_10_independent := @DeepWiki.Independent

/-- **Rule E11** (§8.4, p.212): an insertion and a deletion of independent conditions commute. -/
abbrev e11_ins_del_swap := @DeepWiki.Ins_Del_comm_of_independent

end DeepWiki.Rdb
