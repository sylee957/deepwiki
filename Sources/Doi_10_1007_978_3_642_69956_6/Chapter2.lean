import DeepWiki.RelationalDatabases.RelationalAlgebra
import DeepWiki.RelationalDatabases.RelationalAlgebraExpr
import DeepWiki.RelationalDatabases.TupleCalculus
import DeepWiki.RelationalDatabases.Sql
import DeepWiki.RelationalDatabases.QueryEquivalence
import DeepWiki.RelationalDatabases.QueryEquivalenceFO
import DeepWiki.RelationalDatabases.QueryEquivalenceCodd
import Sources.Doi_10_1007_978_3_642_69956_6.Source

/-! # Relational Database Model catalog — Chapter 2: Query Systems
Chapter 2 introduces three query systems — the relational algebra (§2.1), the tuple calculus
(§2.2) and SQL (§2.3) — and proves them equivalent in expressive power by mutual reduction
(§2.4–2.6, a generalization of Codd's theorem). The `DeepWiki.RelationalDatabases` library
formalizes the relational-algebra operators at the row level and the first generating-part
reduction (intersection from difference).

## NOT YET FORMALIZED (audit 2026-06-23; subtractive — delete each item once it is formalized)
The query-language reductions are to be built as functional translation `def`s + correctness
lemmas (not operational semantics); they need syntax/semantics layers not yet present.
§2.1: the division operator `÷` of Example 2.6 and its generating-part expansion
  `r ÷ s = Π(r;…) − Π((Π(r;…) ⋈ s) − r;…)` [infra].
§2.1.5: generating-part completeness for the selection-as-join expansions
  `σ(r; A θ B) = r ⋈ [A θ B]`, `σ(r; A θ a) = r ⋈ [A θ a]`, `σ(r; f(A₁,…,Aₙ)) = r ⋈ {…|f}`,
  and division `r ÷ s = Π(r;…) − Π((Π(r;…) ⋈ s) − r;…)` [infra: needs the `Ω ∪ Ω = Ω` transport;
  intersection is already `evalAlg_inter`].
§2.1.4: the scheme-level operators (view schemes `Π(V;Ω₁)`, `ρ(V;f)`, `V ⋈ V'`, `V ∪ V'`,
  `V − V'`) with domain/`SC` bookkeeping (the view *instance* `evalAlg` is done) [infra].
§2.2: the concrete tuple-calculus atoms `r(t)`, `f(t₁(A₁),…)`, `t(A) θ t'(B)` (the generic
  `Cond.atom` skeleton, semantics, the generating part 2.2.3/2.2.5 and views 2.2.4 are done)
  and the `DOM(Aᵢ)`-ranging existential of the book's view-instance definition [infra: concrete
  atoms + per-attribute domains].
§2.3: the elementary query's SPJ core (`ElemQuery` = project∘select over the `From` relation, with
  `evalElem`/`mem_evalElem` reducing it to the algebra) and the query set-operation level
  (`INTERSECTION = α MINUS (α MINUS β)`, UNION/INTER laws) are done. Remaining: the full `Where`
  condition language (elementary conditions `f(…)`, comparisons, set-comparisons `sθ`, `IN`,
  emptiness `(…)=∅`), multi-relation `From` lists, and the `IN`/`UNION`/`MINUS` generating-part
  reductions (2.3.3/2.3.5) [infra].
§2.4: the *constructive* converse — a recursive `calcToAlg` translating each *safe* first-order
  condition to an algebra expression [research: needs the renaming operator `ρ` (itself §2.1
  `[infra]`) to compile the de Bruijn context into a product scheme without attribute clashes].
  (Done: the database-relation calculus foundation `QCond`/`evalQCond`, the quantifier-free
  fragment ↔ algebra both directions, the first-order calculus `FOCond`/`evalFO` with de Bruijn
  variables and per-relation schemes, the per-operator reductions, the **full recursive algebra →
  calculus translation** — weakening `FOCond.wk`/`evalFO_wk` via order-preserving embeddings
  `Thin`, the database-indexed algebra `DbAlgExpr`/`evalDbAlg`, and `algToFO` with correctness
  `evalFOExpr_algToFO` (algebra ⊆ calculus) — and the **safety-necessity** result
  `neg_relA_not_isAlgExpressible`: the complement `¬ R(t)` is not algebra-expressible, so the
  converse must restrict to safe formulas.)
§2.5: DONE in both directions — `algToSql`/`evalSql_algToSql` (algebra → SQL) and `sqlToAlg`/
  `evalAlg_sqlToAlg` (SQL → algebra), establishing that the relational algebra and SQL have the same
  expressive power (the set-operation/SPJ level; the elementary `Where` internals are abstracted).
§2.6: the reduction of SQL to the tuple calculus [infra: needs SQL's elementary `Where`-condition
  language translated to first-order conditions].
Expressive equivalence of the three systems (Codd's theorem, the chapter's main result) [research].
§2.7: Exercises [deferred: not yet transcribed]. -/

open DeepWiki

namespace DeepWiki.Rdb

/-! ## §2.1 The Relational Algebra -/

/-- **Row restriction `t[Ω₁]`** (§2.1.4, p.28): a row over `Ω` restricted to a subset `Ω₁ ⊆ Ω`. -/
abbrev algebra_restrict := @DeepWiki.Tuple.restrict

/-- **Projection `Π(v; Ω₁)`** (§2.1, Example 2.1, p.20): the rows of `v` restricted to `Ω₁`. -/
abbrev algebra_projection := @DeepWiki.project

/-- **Selection `σ(v; condition)`** (§2.1, Example 2.2, p.21): the rows of `v` satisfying the
condition. -/
abbrev algebra_selection := @DeepWiki.select

/-- **Join `v ⋈ v'`** (§2.1, Example 2.3, p.21): rows over `Ω ∪ Ω'` agreeing on the common
attributes; the cartesian product `v × v'` when `Ω`, `Ω'` are disjoint (Example 2.3). -/
abbrev algebra_join := @DeepWiki.join

/-- **Union `v ∪ v'`** (§2.1, Example 2.5, p.23): set union of tables over equal attributes. -/
abbrev algebra_union := @DeepWiki.union

/-- **Difference `v − v'`** (§2.1, Example 2.5, p.23): set difference of tables over equal
attributes. -/
abbrev algebra_difference := @DeepWiki.diff

/-- **Intersection `v ∩ v'`** (§2.1, Example 2.5, p.23): set intersection of tables over equal
attributes. -/
abbrev algebra_intersection := @DeepWiki.inter

/-- **Renaming `ρ(v; e)`** (§2.1, Example 2.4, p.22): rename the attributes of a table along a
bijection of the attribute carriers; invertible by renaming back along `e.symm`. -/
abbrev algebra_rename := @DeepWiki.renameTable

/-- **Intersection from difference** (§2.1.3, p.28; §2.1.5): `r ∩ s = r − (r − s)` — the first
step in showing the generating part (instances, `Π`, `ρ`, `⋈`, `∪`, `−`, computable instances)
expresses the whole algebra. -/
abbrev algebra_inter_from_diff := @DeepWiki.inter_eq_diff_diff

/-! ## §2.1.2 / §2.1.4 Algebraic expressions and their view instances -/

/-- **Algebraic expression** (§2.1.2, Fig 2.9, p.27): the abstract syntax of the relational
algebra — base relation instances, computable instances, projection, selection, join, union and
difference — denoting a table over its output attributes. -/
abbrev algebra_expr := @DeepWiki.AlgExpr

/-- **View instance represented by an algebraic expression** (§2.1.4, p.28): the denotational
semantics `evalAlg` mapping an algebraic expression to the table it represents. -/
abbrev algebra_view_instance := @DeepWiki.evalAlg

/-- **Generating part expresses intersection** (§2.1.5, p.28), expression level: `e − (e − e')`
denotes `e ∩ e'`. -/
abbrev algebra_expr_inter := @DeepWiki.evalAlg_inter

/-! ## §2.2 The Tuple Calculus -/

/-- **Calculus condition** (§2.2.2, Fig 2.10, p.33): the abstract syntax of tuple-calculus
conditions over a context of tuple variables — atoms, `¬`, `∨`, and the existential tuple
quantifier (conjunction, implication and `∀` are derived). -/
abbrev tupleCalc_cond := @DeepWiki.Cond

/-- **Semantics of a condition** (§2.2.4, p.34): the proposition `C(t/t₀)` a condition asserts
of an environment. -/
abbrev tupleCalc_eval := @DeepWiki.evalCond

/-- **View instance represented by a calculus expression** (§2.2.4, p.34): `{t(Ω) | C}` denotes
the rows over `Ω` satisfying the single-free-variable condition `C`. -/
abbrev tupleCalc_expr := @DeepWiki.evalCalcExpr

/-- **Generating part — universal quantifier** (§2.2.5, p.35): `∀t(…)C = ¬∃t(…)(¬C)`. -/
abbrev tupleCalc_all_from_ex := @DeepWiki.evalCond_all

/-- **Generating part — conjunction** (§2.2.5, p.35): `C₁ ∧ C₂ = ¬((¬C₁) ∨ (¬C₂))`. -/
abbrev tupleCalc_conj_from_disj := @DeepWiki.evalCond_conj

/-- **Generating part — implication** (§2.2.5, p.35): `C₁ ⇒ C₂ = (¬C₁) ∨ C₂`. -/
abbrev tupleCalc_imp_from_disj := @DeepWiki.evalCond_imp

/-! ## §2.4 Reduction of the Tuple Calculus to the Algebra (foundation) -/

/-- **Database-relation calculus condition** (§2.4): the quantifier-free tuple calculus over a
fixed database of base relations — the faithful basis for the algebra↔calculus equivalence (a
generic-table atom would trivialise it). -/
abbrev tupleCalc_dbCond := @DeepWiki.QCond

/-- **Semantics of a database-relation condition** (§2.4): the table it denotes over `db`. -/
abbrev tupleCalc_dbCond_eval := @DeepWiki.evalQCond

/-- **Selection as a calculus condition** (§2.4): `rel i ∧ comp P` denotes the selection of the
base relation `db i` by `P`. -/
abbrev reduction_select := @DeepWiki.evalQCond_select

/-- **Difference as a calculus condition** (§2.4): `C ∧ ¬D` denotes the difference of the denoted
tables. -/
abbrev reduction_diff := @DeepWiki.evalQCond_diff

/-- **Converse translation calculus → algebra** (§2.4): every quantifier-free database-relation
condition is a relational-algebra expression. -/
abbrev reduction_calcToAlg := @DeepWiki.qcondToAlg

/-- **Converse translation correctness** (§2.4): the algebra translation denotes the same table —
giving the algebra ↔ calculus equivalence for the quantifier-free fragment. -/
abbrev reduction_calcToAlg_correct := @DeepWiki.evalAlg_qcondToAlg

/-- **First-order database-relation condition** (§2.4): the full tuple calculus with several
tuple variables (de Bruijn) of possibly different schemes, relation/computable/agreement atoms,
the boolean connectives and the existential. -/
abbrev tupleCalc_fo := @DeepWiki.FOCond

/-- **Semantics of a first-order condition** (§2.4). -/
abbrev tupleCalc_fo_eval := @DeepWiki.evalFO

/-- **Projection reduction** (§2.4, Step 3.5): projection of a base relation onto `Ω₁` is the
first-order expression `{s | ∃ t, t ∈ R ∧ s, t agree on Ω₁}` — the existential realises
projection. -/
abbrev reduction_projection := @DeepWiki.evalFOExpr_projQuery

/-- **Join reduction** (§2.4): the join of two base relations is the first-order expression
`{t | ∃ u w, u ∈ R ∧ w ∈ S ∧ t agrees with u, w on their schemes}` — two existentials realise the
join. -/
abbrev reduction_join := @DeepWiki.evalFOExpr_joinQuery

/-- **`FOCond` subsumes the quantifier-free calculus** (§2.4): the quantifier-free `QCond`
embeds into the first-order calculus with the same denotation, unifying the two layers. -/
abbrev reduction_qcond_subsumed := @DeepWiki.evalFOExpr_qcondToFO

/-- **Context thinning** (§2.4): an order-preserving embedding of de Bruijn contexts, the basis
of weakening. -/
abbrev calc_thinning := @DeepWiki.Thin

/-- **Condition weakening** (§2.4): reindex a first-order condition into a larger context (used to
compose sub-queries under the existentials), meaning preserved by `evalFO_wk`. -/
abbrev calc_weaken := @DeepWiki.FOCond.wk

/-- **Weakening correctness** (§2.4): the weakened condition over the larger environment holds iff
the original holds over the projected one. -/
abbrev calc_weaken_correct := @DeepWiki.evalFO_wk

/-- **Database-indexed relational algebra** (§2.4): algebra expressions indexed by their output
scheme — the source of the recursive translation to the calculus. -/
abbrev algebra_dbIndexed := @DeepWiki.DbAlgExpr

/-- **Recursive algebra → calculus translation** (§2.4): each algebra expression maps to a
single-free-variable first-order condition (projection and join introduce existentials). -/
abbrev reduction_algToCalc := @DeepWiki.algToFO

/-- **Codd's theorem, algebra ⊆ calculus** (§2.4): `algToFO` denotes the same table as the algebra
expression, `evalFOExpr (algToFO e) = evalDbAlg e` — the relational algebra is subsumed by the
first-order tuple calculus. -/
abbrev reduction_algToCalc_correct := @DeepWiki.evalFOExpr_algToFO

/-- **Algebra-expressibility / safety** (§2.4): a database-to-table map some algebra expression
computes for every database — the model's domain-independence notion for the converse reduction. -/
abbrev safety_isAlgExpressible := @DeepWiki.IsAlgExpressible

/-- **Safety is necessary** (§2.4): the complement `¬ R(t)` is *not* algebra-expressible (empty
database ⟹ complement is `univ` but every algebra expression is empty), so the calculus → algebra
reduction cannot be total — it must restrict to safe formulas. -/
abbrev safety_neg_not_expressible := @DeepWiki.neg_relA_not_isAlgExpressible

/-! ## §2.3 SQL: Structured Query Language -/

/-- **SQL query** (§2.3.1/§2.3.2, Fig 2.11, p.37): an elementary `Select … From … Where …` query
combined by the set operations `UNION`, `MINUS`, `INTERSECTION` (here at the set-operation level,
the elementary query given by its view instance). -/
abbrev sql_query := @DeepWiki.SqlQuery

/-- **View instance represented by an SQL query** (§2.3.4, p.43): the denotational semantics
`evalSql` of an SQL query as a table. -/
abbrev sql_view_instance := @DeepWiki.evalSql

/-- **Generating part — intersection from difference** (§2.3.5, p.45): `α INTERSECTION β`
denotes the same table as `α MINUS (α MINUS β)`. -/
abbrev sql_inter_from_minus := @DeepWiki.evalSql_inter_eq_minus

/-- **§2.3** SQL `UNION` is commutative (view-instance level). -/
abbrev sql_union_comm := @DeepWiki.evalSql_union_comm

/-- **§2.3** SQL `UNION` is associative (view-instance level). -/
abbrev sql_union_assoc := @DeepWiki.evalSql_union_assoc

/-- **§2.3** SQL `INTERSECTION` is commutative (view-instance level). -/
abbrev sql_inter_comm := @DeepWiki.evalSql_inter_comm

/-- **§2.3** SQL `α MINUS α = ∅` (view-instance level). -/
abbrev sql_minus_self := @DeepWiki.evalSql_minus_self

/-- **Elementary query** (§2.3.2, p.37): `Select Ω From r Where cond` — the SPJ core, a projection
of a selection over the input relation. -/
abbrev sql_elem_query := @DeepWiki.ElemQuery

/-- **§2.3.2**: the view instance of an elementary query (its reduction to project∘select). -/
abbrev sql_elem_eval := @DeepWiki.evalElem

/-! ## §2.5 Reduction of the relational algebra to SQL -/

/-- **§2.5**: the reduction translating an algebra expression to an SQL query (set operations to
`UNION`/`MINUS`, base/SPJ subexpressions to elementary queries). -/
abbrev reduction_algToSql := @DeepWiki.algToSql

/-- **§2.5**: correctness of the algebra-to-SQL reduction — it preserves the view instance. -/
abbrev reduction_algToSql_correct := @DeepWiki.evalSql_algToSql

/-- **§2.5** (converse): the reduction translating an SQL query to an algebra expression
(elementary queries to base relations; `UNION`/`MINUS`/`INTERSECTION` to union/diff/inter). -/
abbrev reduction_sqlToAlg := @DeepWiki.sqlToAlg

/-- **§2.5**: correctness of the SQL-to-algebra reduction. With `algToSql`, the relational algebra
and SQL have the same expressive power. -/
abbrev reduction_sqlToAlg_correct := @DeepWiki.evalAlg_sqlToAlg

end DeepWiki.Rdb
