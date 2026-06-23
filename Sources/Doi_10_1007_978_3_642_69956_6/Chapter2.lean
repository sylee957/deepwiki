import DeepWiki.RelationalDatabases.RelationalAlgebra
import DeepWiki.RelationalDatabases.RelationalAlgebraExpr
import DeepWiki.RelationalDatabases.TupleCalculus
import DeepWiki.RelationalDatabases.Sql
import DeepWiki.RelationalDatabases.QueryEquivalence
import DeepWiki.RelationalDatabases.QueryEquivalenceFO
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
§2.1: the renaming operator `ρ` of Example 2.4 [infra: an attribute bijection on the subtype
  row representation].
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
§2.3: the SQL elementary query `Select … From … Where …` internals — attribute lists, relation
  lists, conditions (elementary conditions `f(…)`, comparisons, set-comparisons `sθ`, `IN`,
  emptiness `(…)=∅`), and the generating-part reductions for `IN`/`UNION`/`MINUS` to the
  generating part (2.3.3/2.3.5) [infra: the elementary query reduces to the algebra; the query
  set-operation level and `INTERSECTION = α MINUS (α MINUS β)` are done].
§2.4: the full reduction of the tuple calculus to the relational algebra — the join reduction,
  the recursive translation function `calcToAlg` over the first-order calculus, and safety/domain-
  independence [research]. (Done: the database-relation calculus foundation `QCond`/`evalQCond`,
  the quantifier-free fragment ↔ algebra both directions, the first-order calculus `FOCond`/
  `evalFO` with de Bruijn variables, and the projection reduction `evalFOExpr_projQuery`.)
§2.5: the reduction of the relational algebra to SQL [infra].
§2.6: the reduction of SQL to the tuple calculus [infra].
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

end DeepWiki.Rdb
