import DeepWiki.RelationalDatabases.RelationalAlgebra
import DeepWiki.RelationalDatabases.RelationalAlgebraExpr

/-! # SQL (set-operation level)
The structure of an SQL query (§2.3.1): an elementary query (a `Select … From … Where …` view
instance) combined by the set operations `UNION`, `MINUS` and `INTERSECTION`. `evalSql` gives
its denotational semantics into a table, and `evalSql_inter_eq_minus` is the §2.3.5
generating-part identity `α INTERSECTION β = α MINUS (α MINUS β)`.

An elementary query is modelled by the table it produces; its internal `Select`/`From`/`Where`
structure (projection of a selection over a join, with conditions possibly containing
subqueries) reduces to the relational algebra and is layered on later. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v}

/-- An *SQL query* over output attributes `Ω`: an elementary query (its result table) combined
by the set operations union, difference (`MINUS`) and intersection. -/
inductive SqlQuery (Att : Type u) (Val : Type v) : Finset Att → Type (max u v) where
  /-- An elementary `Select … From … Where …` query, given by the view instance it produces. -/
  | elem {Ω : Finset Att} (v : Table Ω Val) : SqlQuery Att Val Ω
  /-- `α UNION β`. -/
  | union {Ω : Finset Att} (a b : SqlQuery Att Val Ω) : SqlQuery Att Val Ω
  /-- `α MINUS β`. -/
  | minus {Ω : Finset Att} (a b : SqlQuery Att Val Ω) : SqlQuery Att Val Ω
  /-- `α INTERSECTION β`. -/
  | inter {Ω : Finset Att} (a b : SqlQuery Att Val Ω) : SqlQuery Att Val Ω

/-- The *view instance represented by an SQL query*: its denotational semantics as a table. -/
def evalSql : {Ω : Finset Att} → SqlQuery Att Val Ω → Table Ω Val
  | _, .elem v => v
  | _, .union a b => union (evalSql a) (evalSql b)
  | _, .minus a b => diff (evalSql a) (evalSql b)
  | _, .inter a b => inter (evalSql a) (evalSql b)

@[simp] theorem evalSql_elem {Ω : Finset Att} (v : Table Ω Val) :
    evalSql (SqlQuery.elem v) = v := by
  simp only [evalSql]

@[simp] theorem evalSql_union {Ω : Finset Att} (a b : SqlQuery Att Val Ω) :
    evalSql (SqlQuery.union a b) = union (evalSql a) (evalSql b) := by
  simp only [evalSql]

@[simp] theorem evalSql_minus {Ω : Finset Att} (a b : SqlQuery Att Val Ω) :
    evalSql (SqlQuery.minus a b) = diff (evalSql a) (evalSql b) := by
  simp only [evalSql]

@[simp] theorem evalSql_inter {Ω : Finset Att} (a b : SqlQuery Att Val Ω) :
    evalSql (SqlQuery.inter a b) = inter (evalSql a) (evalSql b) := by
  simp only [evalSql]

/-- The generating part of SQL expresses intersection from difference (§2.3.5):
`α INTERSECTION β` denotes the same table as `α MINUS (α MINUS β)`. -/
theorem evalSql_inter_eq_minus {Ω : Finset Att} (a b : SqlQuery Att Val Ω) :
    evalSql (SqlQuery.inter a b) = evalSql (SqlQuery.minus a (SqlQuery.minus a b)) := by
  simp only [evalSql_inter, evalSql_minus]
  exact inter_eq_diff_diff _ _

/-- `UNION` is commutative (at the view-instance level). -/
theorem evalSql_union_comm {Ω : Finset Att} (a b : SqlQuery Att Val Ω) :
    evalSql (SqlQuery.union a b) = evalSql (SqlQuery.union b a) := by
  simp only [evalSql_union]; exact union_comm _ _

/-- `UNION` is associative (at the view-instance level). -/
theorem evalSql_union_assoc {Ω : Finset Att} (a b c : SqlQuery Att Val Ω) :
    evalSql (SqlQuery.union (SqlQuery.union a b) c)
      = evalSql (SqlQuery.union a (SqlQuery.union b c)) := by
  simp only [evalSql_union]; exact union_assoc _ _ _

/-- `INTERSECTION` is commutative (at the view-instance level). -/
theorem evalSql_inter_comm {Ω : Finset Att} (a b : SqlQuery Att Val Ω) :
    evalSql (SqlQuery.inter a b) = evalSql (SqlQuery.inter b a) := by
  simp only [evalSql_inter]; exact Set.inter_comm _ _

/-- Differencing the same query yields the empty view instance: `α MINUS α = ∅`. -/
theorem evalSql_minus_self {Ω : Finset Att} (a : SqlQuery Att Val Ω) :
    evalSql (SqlQuery.minus a a) = (∅ : Table Ω Val) := by
  simp only [evalSql_minus, diff]; ext x; simp

/-! ## The elementary query (§2.3.2): `Select … From … Where …` -/

/-- An *elementary SQL query* `Select Ω From r Where cond` (§2.3.2): over an input relation on
`Ω₀` (the `From` clause — itself possibly a join), keep the rows satisfying `cond` (the `Where`
clause) and project onto the output attributes `Ω ⊆ Ω₀` (the `Select` clause). -/
structure ElemQuery (Att : Type u) (Val : Type v) (Ω₀ Ω : Finset Att) where
  /-- The `Where` condition on input rows. -/
  cond : Tuple Ω₀ Val → Prop
  /-- The `Select` projection: the output attributes are among the input attributes. -/
  sub : Ω ⊆ Ω₀

/-- The view instance of an elementary query over an input table — projection of the selection. -/
def evalElem {Ω₀ Ω : Finset Att} (q : ElemQuery Att Val Ω₀ Ω) (r : Table Ω₀ Val) : Table Ω Val :=
  project q.sub (select q.cond r)

/-- An elementary query is exactly a projection of a selection (its reduction to the algebra). -/
theorem evalElem_eq {Ω₀ Ω : Finset Att} (q : ElemQuery Att Val Ω₀ Ω) (r : Table Ω₀ Val) :
    evalElem q r = project q.sub (select q.cond r) := rfl

/-- A tuple is in the elementary query's result iff it is the projection of an input row satisfying
the condition. -/
theorem mem_evalElem {Ω₀ Ω : Finset Att} (q : ElemQuery Att Val Ω₀ Ω) (r : Table Ω₀ Val)
    (s : Tuple Ω Val) : s ∈ evalElem q r ↔ ∃ t ∈ r, q.cond t ∧ t.restrict q.sub = s := by
  simp only [evalElem, mem_project, mem_select]
  constructor
  · rintro ⟨t, ⟨htr, hc⟩, rfl⟩; exact ⟨t, htr, hc, rfl⟩
  · rintro ⟨t, htr, hc, rfl⟩; exact ⟨t, ⟨htr, hc⟩, rfl⟩

/-! ## Reduction of the relational algebra to SQL (§2.5) -/

variable [DecidableEq Att]

/-- **Reduction of the algebra to SQL** (§2.5): translate an algebra expression to an SQL query —
the set operations map to SQL `UNION`/`MINUS`, and every base or SPJ subexpression becomes an
elementary query (here given by the view instance it produces). -/
def algToSql : {Ω : Finset Att} → AlgExpr Att Val Ω → SqlQuery Att Val Ω
  | _, .union e e' => .union (algToSql e) (algToSql e')
  | _, .diff e e' => .minus (algToSql e) (algToSql e')
  | _, .rel v => .elem v
  | _, .comp f => .elem {t | f t}
  | _, .proj h e => .elem (project h (evalAlg e))
  | _, .sel P e => .elem (select P (evalAlg e))
  | _, .join e e' => .elem (join (evalAlg e) (evalAlg e'))

/-- The algebra-to-SQL reduction is correct: it preserves the view instance. -/
theorem evalSql_algToSql : {Ω : Finset Att} → (e : AlgExpr Att Val Ω) →
    evalSql (algToSql e) = evalAlg e
  | _, .rel _ => by simp only [algToSql, evalSql_elem, evalAlg_rel]
  | _, .comp _ => by simp only [algToSql, evalSql_elem, evalAlg_comp]
  | _, .proj _ _ => by simp only [algToSql, evalSql_elem, evalAlg_proj]
  | _, .sel _ _ => by simp only [algToSql, evalSql_elem, evalAlg_sel]
  | _, .join _ _ => by simp only [algToSql, evalSql_elem, evalAlg_join]
  | _, .union e e' => by
      rw [algToSql, evalSql_union, evalSql_algToSql e, evalSql_algToSql e', evalAlg_union]
  | _, .diff e e' => by
      rw [algToSql, evalSql_minus, evalSql_algToSql e, evalSql_algToSql e', evalAlg_diff]

/-- **Reduction of SQL to the algebra**: every SQL query is an algebra expression — elementary
queries are base relations, and `UNION`/`MINUS`/`INTERSECTION` map to union/difference/intersection
(the last via the generating part `e − (e − e')`). -/
def sqlToAlg : {Ω : Finset Att} → SqlQuery Att Val Ω → AlgExpr Att Val Ω
  | _, .elem v => .rel v
  | _, .union a b => .union (sqlToAlg a) (sqlToAlg b)
  | _, .minus a b => .diff (sqlToAlg a) (sqlToAlg b)
  | _, .inter a b => (sqlToAlg a).inter (sqlToAlg b)

/-- The SQL-to-algebra reduction is correct: it preserves the view instance. With `algToSql`, the
relational algebra and SQL have the same expressive power. -/
theorem evalAlg_sqlToAlg : {Ω : Finset Att} → (q : SqlQuery Att Val Ω) →
    evalAlg (sqlToAlg q) = evalSql q
  | _, .elem _ => by simp only [sqlToAlg, evalAlg_rel, evalSql_elem]
  | _, .union a b => by
      rw [sqlToAlg, evalAlg_union, evalAlg_sqlToAlg a, evalAlg_sqlToAlg b, evalSql_union]
  | _, .minus a b => by
      rw [sqlToAlg, evalAlg_diff, evalAlg_sqlToAlg a, evalAlg_sqlToAlg b, evalSql_minus]
  | _, .inter a b => by
      rw [sqlToAlg, evalAlg_inter, evalAlg_sqlToAlg a, evalAlg_sqlToAlg b, evalSql_inter]

end DeepWiki
