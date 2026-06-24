import DeepWiki.RelationalDatabases.IncompleteInformation
import DeepWiki.RelationalDatabases.NullValues
import DeepWiki.RelationalDatabases.ConditionalTables
import DeepWiki.RelationalDatabases.IncompleteConstraints
import Sources.Doi_10_1007_978_3_642_69956_6.Source

/-! # Relational Database Model catalog — Chapter 6: Incomplete Information
Chapter 6 generalizes the model to null values: representation systems for existing-but-unknown
nulls (§6.1), updating such relations (§6.2), constraints in incomplete databases (§6.3),
no-information nulls (§6.4) and the weak instance model (§6.5). The `DeepWiki.RelationalDatabases`
library formalizes the §6.2 updates on sets of possible instances, which are null-free.

## NOT YET FORMALIZED (audit 2026-06-23; subtractive — delete each item once it is formalized)
The null-extended carrier and Codd-table representation are present (`NullTuple`/`NullTable`,
the information order `MoreInfo`, `rep`/`coddRep`, certain/possible answers, and the Thm 6.3
projection/`selectCertain` rules); the equivalence machinery and the remaining systems remain.
§6.1: Def 6.1's full "representation system" triple `⟨I, Rep, β⟩` with its correctness condition;
  Def 6.2's f-information `X^f = ⋂ f(X)` and β-equivalence `≡_β` / β-representation; Theorem 6.1's
  `≡_P` claim (Codd tables P-represent any X) and Thm 6.2 (`≡_S`); the "correctly evaluates"
  statement of Theorem 6.3 (`Rep(f(T)) ≡_PS f(Rep(T))`); Theorem 6.4 (Codd tables fail `PSU` and
  `PJ`); Theorem 6.5 (V-tables: `PS⁺UJ`) / Theorem 6.6 (V-tables fail `PS`); Theorem 6.7 (C-tables:
  `PSUJ`) — the V-table and C-table *objects* and their representations are now formalized
  (`VTable`/`CTable`, `CTable.rep`), but these *capability* theorems remain [infra/research].
§6.2: the per-table insertion/deletion/modification and Theorem 6.8 (which update operations are
  feasible for Codd / V / C-tables) [infra: needs the null-table representations].
§6.3: the fill-in (chase-like) rules, the converse of Theorem 6.9 (no hard violation after
  exhaustive fill-in ⟹ a permissible completion exists — needs the fill-in as a terminating
  function), and Def 6.7 (existence constraints `X ↘ Y`, with fd-like inference rules)
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

/-- **§6.1** (faithfulness): a definite (null-free) table represents exactly itself — its only
possible world is itself. A representation system must contain the definite relations faithfully. -/
abbrev rep_definite_faithful := @DeepWiki.rep_toNullTable

/-- **Theorem 6.1** (§6.1, p.160), the Codd-table representation `Rep(T)`: the open-world instances
in which every null row of `T` has a definite refinement. -/
abbrev thm_6_1_coddRep := @DeepWiki.coddRep

/-- **§6.1**: every closed possible world is a Codd-table (open-world) world. -/
abbrev rep_subset_coddRep := @DeepWiki.rep_subset_coddRep

/-- **Theorem 6.3** (§6.1, p.161), the selection rule `σ(T;E)`: keep a null row only when the
condition is certainly true — true on every way of filling its nulls. The projection rule
`Π(T;Y) = {t[Y] : t ∈ T}` is the row-level `DeepWiki.project`. -/
abbrev thm_6_3_selectCertain := @DeepWiki.selectCertain

/-- **Theorem 6.3**: certain-selection only removes rows. -/
abbrev thm_6_3_selectCertain_subset := @DeepWiki.selectCertain_subset

/-- **Definition 6.2** (§6.1, p.160), the f-information `X^f = ⋂_{r ∈ X} f r`: the answers `f`
certainly produces over a set of possible instances. -/
abbrev def_6_2_infoF := @DeepWiki.infoF

/-- **§6.1**: the certain answers of a null-table are its identity f-information. -/
abbrev certainAnswer_eq_infoF := @DeepWiki.certainAnswer_iff_mem_infoF_id

/-- **Definition 6.2** (§6.1, p.160), β-equivalence `≡_β`: same f-information for every operator in
the family — an equivalence relation. -/
abbrev def_6_2_betaEquiv := @DeepWiki.BetaEquiv

/-- **Definition 6.2** (§6.1, p.160), β-representation: a null-table β-represents `X` when its
Codd-table worlds are β-equivalent to `X`. -/
abbrev def_6_2_betaRepresents := @DeepWiki.BetaRepresents

/-- **§6.1**: every definite (null-free) row of a Codd table is a certain answer. -/
abbrev definite_row_is_certain := @DeepWiki.mem_infoF_id_coddRep_of_toNull_mem

/-- **§6.1**: a definite table's certain answers are exactly itself. -/
abbrev certain_answers_definite := @DeepWiki.infoF_id_rep_toNullTable

/-! ## §6.1 V-tables and conditional tables (C-tables) -/

/-- **§6.1 V-table entry** (p.158): a constant value or a marked null (variable). -/
abbrev v_entry := @DeepWiki.VEntry

/-- **§6.1 V-tuple**: each attribute holds a constant or a variable. -/
abbrev v_tuple := @DeepWiki.VTuple

/-- **§6.1 naive evaluation** (p.158): apply a valuation to a V-tuple, treating variables as values.-/
abbrev v_apply := @DeepWiki.applyV

/-- **§6.1 V-table** (Fig 6.2, p.158): a set of V-tuples, evaluated naively. -/
abbrev v_table := @DeepWiki.VTable

/-- **§6.1**: the relations a V-table represents (naive images under all valuations). -/
abbrev v_table_rep := @DeepWiki.VTable.rep

/-- **§6.1 C-table** (p.158, Fig 6.3): a V-table with a per-row condition column and a global
condition — the conditional table. -/
abbrev c_table := @DeepWiki.CTable

/-- **§6.1**: the relations a C-table represents — its instances under all valuations satisfying the
global condition, keeping rows whose condition holds. -/
abbrev c_table_rep := @DeepWiki.CTable.rep

/-- **§6.1**: a C-table's instance under a single valuation. -/
abbrev c_table_instAt := @DeepWiki.CTable.instAt

/-- **§6.1**: C-tables subsume V-tables — a V-table is the conditionless C-table, with matching
representation. -/
abbrev c_table_subsumes_v_table := @DeepWiki.VTable.rep_toCTable

/-- **§6.1** (faithfulness): a constant V-table represents exactly the original relation. -/
abbrev v_table_definite_faithful := @DeepWiki.Table.rep_toVTable

/-! ## §6.2 Conditions on updates (Def 6.3) -/

/-- **Definition 6.3** (§6.2, p.163), elementary condition: an equality or inequality between two
entries (variables or constants); also the condition language of a C-table's `con` column. -/
abbrev def_6_3_elementary_condition := @DeepWiki.ECond

/-- **Definition 6.3** (§6.2, p.163), condition: a conjunction of elementary conditions. -/
abbrev def_6_3_condition := @DeepWiki.CCond

/-- **Definition 6.3** (§6.2): when a condition holds under a valuation. -/
abbrev def_6_3_holds := @DeepWiki.CCond.Holds

/-! ## §6.3 Constraints in Incomplete Databases -/

/-- **§6.3**: two V-tuples agree on `X` (identical entries on every attribute of `X`). -/
abbrev v_agree := @DeepWiki.VAgree

/-- **Definition 6.5** (§6.3, p.168): a V-table is *permissible* under a set of fds when some
completion (a valuation's image) satisfies them. -/
abbrev def_6_5_permissible := @DeepWiki.IsPermissible

/-- **Definition 6.6** (§6.3, p.168), hard violation: `X`-agreeing rows carry distinct constants on
`A` — unrepairable by any valuation. -/
abbrev def_6_6_hard_violation := @DeepWiki.HardViolation

/-- **Definition 6.6** (§6.3, p.168), soft violation: `X`-agreeing rows differ on `A` but a variable
is involved — repairable by filling in. -/
abbrev def_6_6_soft_violation := @DeepWiki.SoftViolation

/-- **Theorem 6.9** (§6.3, p.168, forward direction): a hard violation of a required fd blocks
permissibility — no completion can satisfy it. -/
abbrev thm_6_9_hard_violation_blocks := @DeepWiki.not_isPermissible_of_hardViolation
