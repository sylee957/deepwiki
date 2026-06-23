import DeepWiki.RelationalDatabases.RelationalAlgebra

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

end DeepWiki
