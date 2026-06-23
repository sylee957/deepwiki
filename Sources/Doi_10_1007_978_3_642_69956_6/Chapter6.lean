import DeepWiki.RelationalDatabases.IncompleteInformation
import DeepWiki.RelationalDatabases.NullValues
import Sources.Doi_10_1007_978_3_642_69956_6.Source

/-! # Relational Database Model catalog — Chapter 6: Incomplete Information
Chapter 6 generalizes the model to null values: representation systems for existing-but-unknown
nulls (§6.1), updating such relations (§6.2), constraints in incomplete databases (§6.3),
no-information nulls (§6.4) and the weak instance model (§6.5). The `DeepWiki.RelationalDatabases`
library formalizes the §6.2 updates on sets of possible instances, which are null-free.

## NOT YET FORMALIZED (audit 2026-06-23; subtractive — delete each item once it is formalized)
The null-extended carrier is now present (`NullTuple`/`NullTable` over `Option Val`, with the
information order `MoreInfo`); the representation systems and theorems on top of it remain.
§6.1: Codd tables, V-tables and C-tables; Def 6.1 (a representation system), Def 6.2
  (β-equivalence and β-representation); Theorems 6.1–6.7 on which classes of relational
  expressions (`P`, `S`, `S⁺`, `J`, `U`, `D`, `R`) each representation system can correctly
  evaluate (e.g. Thm 6.3 Codd tables support `PS`, Thm 6.5 V-tables support `PS⁺UJ`, Thm 6.7
  C-tables support `PSUJ`) [infra/research].
§6.2: Def 6.3 (elementary conditions and conditions), the per-table insertion/deletion/
  modification, and Theorem 6.8 (which update operations are feasible for Codd / V / C-tables)
  [infra: needs the null-table representations].
§6.3: Def 6.5 (a permissible table under fds), Def 6.6 (hard vs soft violations of an fd), the
  fill-in (chase-like) rules, Theorem 6.9 (permissible completion exists iff exhaustive fill-in
  has no hard violation), Def 6.7 (existence constraints `X ↘ Y`, with fd-like inference rules)
  [infra/research].
§6.4: relations with no-information nulls (Zaniolo) [research].
§6.5: the weak instance model [research].
§6.6: Exercises [deferred: not yet transcribed]. -/

open DeepWiki

namespace DeepWiki.Rdb

/-! ## §6.2 Updating Relations (updates on sets of instances) -/

/-- **Definition 6.4** (§6.2, p.164), general insertion: the pairwise union of two sets of
possible instances. -/
abbrev def_6_4_general_insertion := @DeepWiki.generalInsertion

/-- **Definition 6.4** (§6.2, p.164), general deletion: the pairwise difference. -/
abbrev def_6_4_general_deletion := @DeepWiki.generalDeletion

/-- **Definition 6.4** (§6.2, p.164), integration: the pairwise intersection (combine the
knowledge of two databases). -/
abbrev def_6_4_integration := @DeepWiki.integration

/-- **Definition 6.4** (§6.2, p.164), subjection: keep the possibilities of `X` also in `Y`
(plain intersection). -/
abbrev def_6_4_subjection := @DeepWiki.subjection

/-- **Definition 6.4** (§6.2, p.164), negative subjection: drop the possibilities of `X` in `Y`
(plain difference). -/
abbrev def_6_4_negative_subjection := @DeepWiki.negativeSubjection

/-- **Definition 6.4** (§6.2, p.164), augmentation: all possibilities of `X` or `Y` (plain
union). -/
abbrev def_6_4_augmentation := @DeepWiki.augmentation

/-- **Subjection restricts** (§6.2): a subjection update can only shrink the set of
possibilities. -/
abbrev subjection_subset := @DeepWiki.subjection_subset

/-- **Augmentation enlarges** (§6.2): an augmentation update can only grow the set of
possibilities. -/
abbrev augmentation_superset := @DeepWiki.subset_augmentation

/-! ## §6.1 Null-extended carrier (Codd / V-tables) -/

/-- **§6.1 carrier**: a null-extended tuple (Codd / V-table row) — each attribute carries a value
or a null (`Option Val`). -/
abbrev null_tuple := @DeepWiki.NullTuple

/-- **§6.1 carrier**: a null-extended table. -/
abbrev null_table := @DeepWiki.NullTable

/-- **§6.1 information order**: `nt'` is at least as informative as `nt` (definite, equal wherever
`nt` is definite) — a partial order (reflexive, transitive, antisymmetric). -/
abbrev info_order := @DeepWiki.MoreInfo

/-- **§6.1**: a definite tuple's total row is maximal in the information order. -/
abbrev info_order_definite_maximal := @DeepWiki.moreInfo_toNull_iff

/-- **Definition 6.1** (§6.1, representation), the possible-worlds semantics: the set of definite
tables a null-table denotes — its rows completed (nulls filled) in every way. -/
abbrev rep_possible_worlds := @DeepWiki.rep

/-- **§6.1**: a *possible answer* — a tuple in some possible world. -/
abbrev possible_answer := @DeepWiki.PossibleAnswer

/-- **§6.1**: a *certain answer* — a tuple in every possible world. -/
abbrev certain_answer := @DeepWiki.CertainAnswer

/-- **§6.1**: every certain answer is a possible answer (the representation is nonempty). -/
abbrev certain_imp_possible := @DeepWiki.certainAnswer_imp_possibleAnswer
