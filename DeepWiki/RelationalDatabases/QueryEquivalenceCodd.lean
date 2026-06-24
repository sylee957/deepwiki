import DeepWiki.RelationalDatabases.QueryEquivalenceFO

/-! # Codd's theorem: the recursive algebra → calculus translation
The per-operator reductions of `QueryEquivalenceFO` (projection, join, …) introduce existential
quantifiers, so composing them into one recursive translation of a whole algebra expression needs
**weakening**: a sub-query's condition, living in a context `Γ`, must be reindexed into the larger
context created by the surrounding quantifiers.

This file builds that weakening through order-preserving embeddings (`Thin`) of de Bruijn
contexts, then a database-indexed algebra (`DbAlgExpr`) and the recursive translation `algToFO`
with its correctness theorem — the relational algebra is subsumed by the first-order calculus
(one direction of Codd's theorem). -/

namespace DeepWiki

universe u v w

variable {Att : Type u} {Val : Type v}

/-- An order-preserving embedding (thinning) of one de Bruijn context into another: `Δ` is `Γ`
with extra bindings inserted, order preserved. -/
inductive Thin : Ctx Att → Ctx Att → Type u where
  /-- The empty embedding. -/
  | nil : Thin [] []
  /-- Keep the next binding of both contexts. -/
  | keep {Γ Δ : Ctx Att} {Ω : Finset Att} : Thin Γ Δ → Thin (Ω :: Γ) (Ω :: Δ)
  /-- Skip a binding present only in the larger context. -/
  | drop {Γ Δ : Ctx Att} {Ω : Finset Att} : Thin Γ Δ → Thin Γ (Ω :: Δ)

/-- Weaken a de Bruijn variable along a thinning. -/
def wkVar : {Γ Δ : Ctx Att} → {Ω : Finset Att} → Thin Γ Δ → Var Γ Ω → Var Δ Ω
  | _, _, _, .keep _, .here => .here
  | _, _, _, .keep θ, .there v => .there (wkVar θ v)
  | _, _, _, .drop θ, v => .there (wkVar θ v)

/-- Project an environment of the larger context back to the smaller one. -/
def projEnv : {Γ Δ : Ctx Att} → Thin Γ Δ → Env Val Δ → Env Val Γ
  | _, _, .nil, e => e
  | _, _, .keep θ, (t, e) => (t, projEnv θ e)
  | _, _, .drop θ, (_, e) => projEnv θ e

/-- Looking up a weakened variable reads the projected environment. -/
theorem lookup_wkVar : {Γ Δ : Ctx Att} → {Ω : Finset Att} → (θ : Thin Γ Δ) → (v : Var Γ Ω) →
    (e : Env Val Δ) → lookup (wkVar θ v) e = lookup v (projEnv θ e)
  | _, _, _, .keep _, .here, (_, _) => rfl
  | _, _, _, .keep θ, .there v, (_, e) => lookup_wkVar θ v e
  | _, _, _, .drop θ, v, (_, e) => lookup_wkVar θ v e

variable {ι : Type w} {sch : ι → Finset Att}

/-- Weaken a first-order condition along a thinning, reindexing every variable. -/
def FOCond.wk : {Γ Δ : Ctx Att} → Thin Γ Δ → FOCond ι sch Val Γ → FOCond ι sch Val Δ
  | _, _, θ, .relA i v => .relA i (wkVar θ v)
  | _, _, θ, .compA v P => .compA (wkVar θ v) P
  | _, _, θ, .agreeA v₁ v₂ X => .agreeA (wkVar θ v₁) (wkVar θ v₂) X
  | _, _, θ, .neg C => .neg (FOCond.wk θ C)
  | _, _, θ, .and C D => .and (FOCond.wk θ C) (FOCond.wk θ D)
  | _, _, θ, .or C D => .or (FOCond.wk θ C) (FOCond.wk θ D)
  | _, _, θ, .ex Ω C => .ex Ω (FOCond.wk θ.keep C)

/-- Weakening preserves meaning: the weakened condition over the larger environment holds exactly
when the original holds over the projected environment. -/
theorem evalFO_wk (db : (i : ι) → Table (sch i) Val) {Γ : Ctx Att} (C : FOCond ι sch Val Γ) :
    {Δ : Ctx Att} → (θ : Thin Γ Δ) → (e : Env Val Δ) →
      (evalFO db (C.wk θ) e ↔ evalFO db C (projEnv θ e)) := by
  induction C with
  | relA i v => intro Δ θ e; simp [FOCond.wk, evalFO, lookup_wkVar]
  | compA v P => intro Δ θ e; simp [FOCond.wk, evalFO, lookup_wkVar]
  | agreeA v₁ v₂ X => intro Δ θ e; simp only [FOCond.wk, evalFO, VarAgree, lookup_wkVar]
  | neg C ih => intro Δ θ e; simp only [FOCond.wk, evalFO]; rw [ih θ e]
  | and C D ihC ihD => intro Δ θ e; simp only [FOCond.wk, evalFO]; rw [ihC θ e, ihD θ e]
  | or C D ihC ihD => intro Δ θ e; simp only [FOCond.wk, evalFO]; rw [ihC θ e, ihD θ e]
  | ex Ω C ih => intro Δ θ e; simp only [FOCond.wk, evalFO]; exact exists_congr (fun t => ih θ.keep (t, e))

/-- A database-indexed relational-algebra expression, indexed by its output scheme: base
relations, selection, projection, join, union and difference. -/
inductive DbAlgExpr (ι : Type w) (sch : ι → Finset Att) (Val : Type v) [DecidableEq Att] :
    Finset Att → Type (max (max u v) w) where
  /-- A base relation. -/
  | base (i : ι) : DbAlgExpr ι sch Val (sch i)
  /-- Selection by a computable predicate. -/
  | sel {Ω : Finset Att} (P : Tuple Ω Val → Prop) (e : DbAlgExpr ι sch Val Ω) :
      DbAlgExpr ι sch Val Ω
  /-- Projection onto `Ω₁ ⊆ Ω`. -/
  | proj {Ω : Finset Att} (Ω₁ : Finset Att) (h : Ω₁ ⊆ Ω) (e : DbAlgExpr ι sch Val Ω) :
      DbAlgExpr ι sch Val Ω₁
  /-- Join (natural join over the union of schemes). -/
  | join {Ω Ω' : Finset Att} (e : DbAlgExpr ι sch Val Ω) (e' : DbAlgExpr ι sch Val Ω') :
      DbAlgExpr ι sch Val (Ω ∪ Ω')
  /-- Union of two expressions of the same scheme. -/
  | union {Ω : Finset Att} (e e' : DbAlgExpr ι sch Val Ω) : DbAlgExpr ι sch Val Ω
  /-- Difference of two expressions of the same scheme. -/
  | diff {Ω : Finset Att} (e e' : DbAlgExpr ι sch Val Ω) : DbAlgExpr ι sch Val Ω

/-- The table denoted by a database-indexed algebra expression over a database `db`. -/
def evalDbAlg [DecidableEq Att] (db : (i : ι) → Table (sch i) Val) :
    {Ω : Finset Att} → DbAlgExpr ι sch Val Ω → Table Ω Val
  | _, .base i => db i
  | _, .sel P e => select P (evalDbAlg db e)
  | _, .proj _ h e => project h (evalDbAlg db e)
  | _, .join e e' => join (evalDbAlg db e) (evalDbAlg db e')
  | _, .union e e' => union (evalDbAlg db e) (evalDbAlg db e')
  | _, .diff e e' => diff (evalDbAlg db e) (evalDbAlg db e')

/-- The recursive translation of a database-indexed algebra expression into a single-free-variable
first-order condition. Projection and join introduce existentials, under which the sub-queries are
weakened (`FOCond.wk`) so their free variable points at the freshly bound tuple. -/
def algToFO [DecidableEq Att] : {Ω : Finset Att} → DbAlgExpr ι sch Val Ω → FOCond ι sch Val [Ω]
  | _, .base i => FOCond.relA i Var.here
  | _, .sel P e => FOCond.and (algToFO e) (FOCond.compA Var.here P)
  | _, .proj Ω₁ _ e =>
      FOCond.ex _ (FOCond.and ((algToFO e).wk (Thin.keep (Thin.drop Thin.nil)))
        (FOCond.agreeA Var.here (Var.there Var.here) Ω₁))
  | _, @DbAlgExpr.join _ _ _ _ _ Ω Ω' e e' =>
      FOCond.ex Ω (FOCond.ex Ω'
        (FOCond.and
          (FOCond.and ((algToFO e).wk (Thin.drop (Thin.keep (Thin.drop Thin.nil))))
            ((algToFO e').wk (Thin.keep (Thin.drop (Thin.drop Thin.nil)))))
          (FOCond.and (FOCond.agreeA (Var.there (Var.there Var.here)) (Var.there Var.here) Ω)
            (FOCond.agreeA (Var.there (Var.there Var.here)) Var.here Ω'))))
  | _, .union e e' => FOCond.or (algToFO e) (algToFO e')
  | _, .diff e e' => FOCond.and (algToFO e) (FOCond.neg (algToFO e'))

/-- **Codd's theorem, the algebra ⊆ calculus direction**: every database-indexed algebra
expression denotes the same table as its first-order translation. The relational algebra is
subsumed by the first-order tuple calculus. -/
theorem evalFOExpr_algToFO [DecidableEq Att] (db : (i : ι) → Table (sch i) Val) {Ω : Finset Att}
    (e : DbAlgExpr ι sch Val Ω) : evalFOExpr db (algToFO e) = evalDbAlg db e := by
  induction e with
  | base i =>
      ext t
      simp only [evalFOExpr, algToFO, evalFO, lookup_here, evalDbAlg, Set.mem_setOf_eq]
  | sel P e ih =>
      have ihm : ∀ t, evalFO db (algToFO e) (t, PUnit.unit) ↔ t ∈ evalDbAlg db e := by
        rw [← ih]; exact fun _ => Iff.rfl
      ext t
      simp only [evalFOExpr, algToFO, evalFO, lookup_here, evalDbAlg, mem_select,
        Set.mem_setOf_eq, ihm]
  | proj Ω₁ h e ih =>
      have ihm : ∀ t, evalFO db (algToFO e) (t, PUnit.unit) ↔ t ∈ evalDbAlg db e := by
        rw [← ih]; exact fun _ => Iff.rfl
      ext s
      simp only [evalFOExpr, algToFO, evalFO, evalFO_wk, projEnv, lookup_here, lookup_there,
        VarAgree, evalDbAlg, mem_project, Set.mem_setOf_eq]
      constructor
      · rintro ⟨t, ht, hag⟩
        refine ⟨t, (ihm t).mp ht, ?_⟩
        funext a
        exact hag a.val a.property (h a.property) a.property
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, (ihm t).mpr ht, fun _ _ _ _ => rfl⟩
  | join e e' ih ih' =>
      have ihm : ∀ t, evalFO db (algToFO e) (t, PUnit.unit) ↔ t ∈ evalDbAlg db e := by
        rw [← ih]; exact fun _ => Iff.rfl
      have ihm' : ∀ t, evalFO db (algToFO e') (t, PUnit.unit) ↔ t ∈ evalDbAlg db e' := by
        rw [← ih']; exact fun _ => Iff.rfl
      ext t
      simp only [evalFOExpr, algToFO, evalFO, evalFO_wk, projEnv, lookup_here, lookup_there,
        VarAgree, evalDbAlg, mem_join, Set.mem_setOf_eq]
      constructor
      · rintro ⟨u, w, ⟨hu, hw⟩, hagu, hagw⟩
        refine ⟨?_, ?_⟩
        · have huu : t.restrict Finset.subset_union_left = u := by
            funext x
            exact hagu x.val x.property (Finset.subset_union_left x.property) x.property
          rw [huu]; exact (ihm u).mp hu
        · have hww : t.restrict Finset.subset_union_right = w := by
            funext x
            exact hagw x.val x.property (Finset.subset_union_right x.property) x.property
          rw [hww]; exact (ihm' w).mp hw
      · rintro ⟨hi, hj⟩
        exact ⟨t.restrict Finset.subset_union_left, t.restrict Finset.subset_union_right,
          ⟨(ihm _).mpr hi, (ihm' _).mpr hj⟩, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  | union e e' ih ih' =>
      have ihm : ∀ t, evalFO db (algToFO e) (t, PUnit.unit) ↔ t ∈ evalDbAlg db e := by
        rw [← ih]; exact fun _ => Iff.rfl
      have ihm' : ∀ t, evalFO db (algToFO e') (t, PUnit.unit) ↔ t ∈ evalDbAlg db e' := by
        rw [← ih']; exact fun _ => Iff.rfl
      ext t
      simp only [evalFOExpr, algToFO, evalFO, evalDbAlg, mem_union, Set.mem_setOf_eq, ihm, ihm']
  | diff e e' ih ih' =>
      have ihm : ∀ t, evalFO db (algToFO e) (t, PUnit.unit) ↔ t ∈ evalDbAlg db e := by
        rw [← ih]; exact fun _ => Iff.rfl
      have ihm' : ∀ t, evalFO db (algToFO e') (t, PUnit.unit) ↔ t ∈ evalDbAlg db e' := by
        rw [← ih']; exact fun _ => Iff.rfl
      ext t
      simp only [evalFOExpr, algToFO, evalFO, evalDbAlg, mem_diff, Set.mem_setOf_eq, ihm, ihm']

-- The relational algebra is subsumed by the first-order tuple calculus: every algebra
-- expression's table is denoted by some single-free-variable first-order condition.
example [DecidableEq Att] (db : (i : ι) → Table (sch i) Val) {Ω : Finset Att}
    (e : DbAlgExpr ι sch Val Ω) : ∃ C : FOCond ι sch Val [Ω], evalFOExpr db C = evalDbAlg db e :=
  ⟨algToFO e, evalFOExpr_algToFO db e⟩

/-! ## Safety: why the converse reduction must be restricted
The calculus → algebra direction is *not* total: a condition can denote a table no algebra
expression equals (for every database). The witness is negation, whose denotation depends on the
whole value space, not on the active domain — which is exactly what *safety* / domain-independence
rules out. -/

/-- A database-to-table map is *algebra-expressible* (the model's notion of a safe query): some
algebra expression computes it for every database. -/
def IsAlgExpressible [DecidableEq Att] {Ω : Finset Att}
    (T : ((i : ι) → Table (sch i) Val) → Table Ω Val) : Prop :=
  ∃ e : DbAlgExpr ι sch Val Ω, ∀ db, T db = evalDbAlg db e

/-- With every base relation empty, every algebra expression denotes the empty table — the
algebra cannot conjure tuples absent from its inputs. -/
theorem evalDbAlg_empty [DecidableEq Att] {Ω : Finset Att} (e : DbAlgExpr ι sch Val Ω) :
    evalDbAlg (fun _ => (∅ : Table _ Val)) e = ∅ := by
  induction e with
  | base i => rfl
  | sel P e ih => simp only [evalDbAlg, ih]; ext t; simp [mem_select]
  | proj Ω₁ h e ih => simp only [evalDbAlg, ih]; ext s; simp [mem_project]
  | join e e' ih ih' => simp only [evalDbAlg, ih]; ext t; simp [mem_join]
  | union e e' ih ih' => simp only [evalDbAlg, ih, ih']; ext t; simp [mem_union]
  | diff e e' ih ih' => simp only [evalDbAlg, ih]; ext t; simp [mem_diff]

/-- **Safety is necessary** (§2.4): the complement `¬ R(t)` is not algebra-expressible. With every
base relation empty the complement is all of `univ`, while every algebra expression is empty
(`evalDbAlg_empty`). So the calculus → algebra reduction cannot be total — it must restrict to
safe (domain-independent) formulas. -/
theorem neg_relA_not_isAlgExpressible [DecidableEq Att] [Nonempty Val] (i : ι) :
    ¬ IsAlgExpressible (Ω := sch i)
      (fun (db : (j : ι) → Table (sch j) Val) =>
        evalFOExpr db (FOCond.neg (FOCond.relA i (Var.here)))) := by
  rintro ⟨e, he⟩
  have h : evalFOExpr (fun _ => (∅ : Table (sch i) Val))
      (FOCond.neg (FOCond.relA i Var.here)) = ∅ := by
    have hh := he (fun _ => ∅)
    rw [evalDbAlg_empty] at hh
    exact hh
  have hne : (evalFOExpr (fun _ => (∅ : Table (sch i) Val))
      (FOCond.neg (FOCond.relA i Var.here))).Nonempty :=
    ⟨Classical.arbitrary (Tuple (sch i) Val), by simp [evalFOExpr, evalFO]⟩
  rw [h] at hne
  exact Set.not_nonempty_empty hne

/-! ## SQL over a database and its reduction to the calculus (§2.6) -/

/-- A *database-indexed SQL query*: an elementary query (a `Select/From/Where` SPJ query given as a
db-indexed algebra expression — faithful to SQL's `FROM` naming database relations) combined by
`UNION`/`MINUS`/`INTERSECTION`. -/
inductive DbSql (ι : Type w) (sch : ι → Finset Att) (Val : Type v) [DecidableEq Att] :
    Finset Att → Type (max (max u v) w) where
  /-- An elementary query, given by a db-indexed algebra (SPJ) expression. -/
  | elem {Ω : Finset Att} (e : DbAlgExpr ι sch Val Ω) : DbSql ι sch Val Ω
  /-- `α UNION β`. -/
  | union {Ω : Finset Att} (a b : DbSql ι sch Val Ω) : DbSql ι sch Val Ω
  /-- `α MINUS β`. -/
  | minus {Ω : Finset Att} (a b : DbSql ι sch Val Ω) : DbSql ι sch Val Ω
  /-- `α INTERSECTION β`. -/
  | inter {Ω : Finset Att} (a b : DbSql ι sch Val Ω) : DbSql ι sch Val Ω

variable [DecidableEq Att]

/-- The table denoted by a db-indexed SQL query. -/
def evalDbSql (db : (i : ι) → Table (sch i) Val) :
    {Ω : Finset Att} → DbSql ι sch Val Ω → Table Ω Val
  | _, .elem e => evalDbAlg db e
  | _, .union a b => union (evalDbSql db a) (evalDbSql db b)
  | _, .minus a b => diff (evalDbSql db a) (evalDbSql db b)
  | _, .inter a b => inter (evalDbSql db a) (evalDbSql db b)

/-- Reduce a db-indexed SQL query to the db-indexed algebra (set operations to union/difference,
`INTERSECTION` via the generating part `e − (e − e')`). -/
def dbSqlToAlg : {Ω : Finset Att} → DbSql ι sch Val Ω → DbAlgExpr ι sch Val Ω
  | _, .elem e => e
  | _, .union a b => .union (dbSqlToAlg a) (dbSqlToAlg b)
  | _, .minus a b => .diff (dbSqlToAlg a) (dbSqlToAlg b)
  | _, .inter a b => .diff (dbSqlToAlg a) (.diff (dbSqlToAlg a) (dbSqlToAlg b))

/-- The SQL-to-algebra reduction preserves the view instance. -/
theorem evalDbAlg_dbSqlToAlg (db : (i : ι) → Table (sch i) Val) :
    {Ω : Finset Att} → (q : DbSql ι sch Val Ω) → evalDbAlg db (dbSqlToAlg q) = evalDbSql db q
  | _, .elem _ => by simp only [dbSqlToAlg, evalDbSql]
  | _, .union a b => by
      simp only [dbSqlToAlg, evalDbSql, evalDbAlg, evalDbAlg_dbSqlToAlg db a,
        evalDbAlg_dbSqlToAlg db b]
  | _, .minus a b => by
      simp only [dbSqlToAlg, evalDbSql, evalDbAlg, evalDbAlg_dbSqlToAlg db a,
        evalDbAlg_dbSqlToAlg db b]
  | _, .inter a b => by
      simp only [dbSqlToAlg, evalDbSql, evalDbAlg, evalDbAlg_dbSqlToAlg db a,
        evalDbAlg_dbSqlToAlg db b]
      exact (inter_eq_diff_diff _ _).symm

/-- **Reduction of (db-indexed) SQL to the tuple calculus** (§2.6): an SQL query translates to a
single-free-variable first-order condition, via the algebra and `algToFO`. -/
def dbSqlToFO {Ω : Finset Att} (q : DbSql ι sch Val Ω) : FOCond ι sch Val [Ω] :=
  algToFO (dbSqlToAlg q)

/-- **Codd's theorem, the SQL ⊆ calculus direction** (§2.6): every db-indexed SQL query denotes the
same table as its first-order translation — SQL is subsumed by the first-order tuple calculus. -/
theorem evalFOExpr_dbSqlToFO (db : (i : ι) → Table (sch i) Val) {Ω : Finset Att}
    (q : DbSql ι sch Val Ω) : evalFOExpr db (dbSqlToFO q) = evalDbSql db q := by
  rw [dbSqlToFO, evalFOExpr_algToFO, evalDbAlg_dbSqlToAlg]

/-- Reduce a db-indexed algebra expression to a db-indexed SQL query: set operations to
`UNION`/`MINUS`, every base/SPJ subexpression to an elementary query. -/
def algToDbSql : {Ω : Finset Att} → DbAlgExpr ι sch Val Ω → DbSql ι sch Val Ω
  | _, .union e e' => .union (algToDbSql e) (algToDbSql e')
  | _, .diff e e' => .minus (algToDbSql e) (algToDbSql e')
  | _, .base i => .elem (.base i)
  | _, .sel P e => .elem (.sel P e)
  | _, .proj Ω₁ h e => .elem (.proj Ω₁ h e)
  | _, .join e e' => .elem (.join e e')

/-- The algebra-to-SQL reduction preserves the view instance. -/
theorem evalDbSql_algToDbSql (db : (i : ι) → Table (sch i) Val) :
    {Ω : Finset Att} → (e : DbAlgExpr ι sch Val Ω) → evalDbSql db (algToDbSql e) = evalDbAlg db e
  | _, .base _ => by simp only [algToDbSql, evalDbSql]
  | _, .sel _ _ => by simp only [algToDbSql, evalDbSql]
  | _, .proj _ _ _ => by simp only [algToDbSql, evalDbSql]
  | _, .join _ _ => by simp only [algToDbSql, evalDbSql]
  | _, .union e e' => by
      simp only [algToDbSql, evalDbSql, evalDbAlg, evalDbSql_algToDbSql db e,
        evalDbSql_algToDbSql db e']
  | _, .diff e e' => by
      simp only [algToDbSql, evalDbSql, evalDbAlg, evalDbSql_algToDbSql db e,
        evalDbSql_algToDbSql db e']

/-- **Expressive equivalence of the db-indexed algebra and SQL**: over any database, a view instance
is SQL-expressible iff algebra-expressible. With `dbSqlToFO`/`algToFO`, both are subsumed by the
first-order tuple calculus. -/
theorem dbSql_expressible_iff_alg_expressible (db : (i : ι) → Table (sch i) Val) {Ω : Finset Att}
    (r : Table Ω Val) :
    (∃ q : DbSql ι sch Val Ω, evalDbSql db q = r) ↔ (∃ e : DbAlgExpr ι sch Val Ω, evalDbAlg db e = r) := by
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨dbSqlToAlg q, evalDbAlg_dbSqlToAlg db q⟩
  · rintro ⟨e, rfl⟩; exact ⟨algToDbSql e, evalDbSql_algToDbSql db e⟩

/-! ## Codd's theorem, expressive-power form (§2.4, the chapter's main result)
The query *systems* coincide at the level of which database-to-view maps they compute: algebra and
SQL are equi-expressive, and both are subsumed by the first-order tuple calculus. The reverse
inclusion (calculus ⊆ algebra) holds only under a *safety* restriction — `neg_relA_not_isAlgExpressible`
exhibits a calculus query (the complement) expressible by no algebra expression. -/

/-- A database-to-table map is *calculus-expressible*: some single-free-variable first-order condition
computes it for every database. -/
def IsCalcExpressible {Ω : Finset Att}
    (T : ((i : ι) → Table (sch i) Val) → Table Ω Val) : Prop :=
  ∃ C : FOCond ι sch Val [Ω], ∀ db, T db = evalFOExpr db C

/-- A database-to-table map is *SQL-expressible*: some db-indexed SQL query computes it for every
database. -/
def IsSqlExpressible {Ω : Finset Att}
    (T : ((i : ι) → Table (sch i) Val) → Table Ω Val) : Prop :=
  ∃ q : DbSql ι sch Val Ω, ∀ db, T db = evalDbSql db q

/-- **Codd's theorem, algebra ⊆ calculus** (§2.4, expressive-power form): every algebra-expressible
view map is calculus-expressible — the relational algebra is subsumed by the first-order tuple
calculus. (The converse needs safety: `neg_relA_not_isAlgExpressible`.) -/
theorem isCalcExpressible_of_isAlgExpressible {Ω : Finset Att}
    {T : ((i : ι) → Table (sch i) Val) → Table Ω Val} (h : IsAlgExpressible T) :
    IsCalcExpressible T := by
  obtain ⟨e, he⟩ := h
  exact ⟨algToFO e, fun db => (he db).trans (evalFOExpr_algToFO db e).symm⟩

/-- **SQL ⊆ calculus** (§2.6, expressive-power form): every SQL-expressible view map is
calculus-expressible. -/
theorem isCalcExpressible_of_isSqlExpressible {Ω : Finset Att}
    {T : ((i : ι) → Table (sch i) Val) → Table Ω Val} (h : IsSqlExpressible T) :
    IsCalcExpressible T := by
  obtain ⟨q, hq⟩ := h
  exact ⟨dbSqlToFO q, fun db => (hq db).trans (evalFOExpr_dbSqlToFO db q).symm⟩

/-- **Algebra ≡ SQL** (§2.5/§2.6, expressive-power form): a view map is SQL-expressible iff
algebra-expressible — the two systems compute exactly the same database-to-view maps. -/
theorem isSqlExpressible_iff_isAlgExpressible {Ω : Finset Att}
    {T : ((i : ι) → Table (sch i) Val) → Table Ω Val} :
    IsSqlExpressible T ↔ IsAlgExpressible T := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨dbSqlToAlg q, fun db => (hq db).trans (evalDbAlg_dbSqlToAlg db q).symm⟩
  · rintro ⟨e, he⟩
    exact ⟨algToDbSql e, fun db => (he db).trans (evalDbSql_algToDbSql db e).symm⟩

end DeepWiki
