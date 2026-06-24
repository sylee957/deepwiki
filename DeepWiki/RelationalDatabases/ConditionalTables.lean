import DeepWiki.RelationalDatabases.RelationalAlgebra

/-! # Conditional tables (C-tables) — §6.1/§6.2
The third representation system for existing-but-unknown nulls (§6.1). A **V-table** lets each entry
be a *constant* or a *marked variable* (`Val ⊕ Var`); two occurrences of the same variable denote the
same (unknown) value. A **C-table** is a V-table in which each row carries a *condition* (a
conjunction of equalities/inequalities among variables and constants — Def 6.3) plus a *global*
condition. Its semantics (`CTable.rep`) is the set of ordinary relations obtained from all valuations
`ν : Var → Val` satisfying the global condition, keeping the rows whose condition holds under `ν`.
C-tables overcome the limitations of Codd tables (the `Option`-null `NullTable` of `NullValues`) and
plain V-tables. -/

namespace DeepWiki

universe u v w

variable {Att : Type u} {Val : Type v} {Var : Type w} {Ω : Finset Att}

/-- A V-table *entry*: a constant value (`Sum.inl`) or a marked null / variable (`Sum.inr`). -/
abbrev VEntry (Val : Type v) (Var : Type w) : Type _ := Val ⊕ Var

/-- A **V-tuple**: each attribute holds a constant or a variable. -/
abbrev VTuple (Ω : Finset Att) (Val : Type v) (Var : Type w) : Type _ := Tuple Ω (VEntry Val Var)

/-- Evaluate an entry under a valuation `ν : Var → Val` (constants fixed, variables substituted). -/
def evalEntry (ν : Var → Val) : VEntry Val Var → Val := Sum.elim id ν

@[simp] theorem evalEntry_const (ν : Var → Val) (v : Val) : evalEntry ν (Sum.inl v) = v := rfl

@[simp] theorem evalEntry_var (ν : Var → Val) (x : Var) : evalEntry ν (Sum.inr x) = ν x := rfl

/-- Apply a valuation to a V-tuple, yielding an ordinary tuple (naive evaluation). -/
def applyV (ν : Var → Val) (vt : VTuple Ω Val Var) : Tuple Ω Val := fun a => evalEntry ν (vt a)

@[simp] theorem applyV_apply (ν : Var → Val) (vt : VTuple Ω Val Var) (a : {a : Att // a ∈ Ω}) :
    applyV ν vt a = evalEntry ν (vt a) := rfl

/-- An ordinary tuple as a (constant) V-tuple. -/
def Tuple.toV (t : Tuple Ω Val) : VTuple Ω Val Var := fun a => Sum.inl (t a)

/-- A constant V-tuple is valuation-invariant. -/
@[simp] theorem applyV_toV (ν : Var → Val) (t : Tuple Ω Val) :
    applyV ν (Tuple.toV (Var := Var) t) = t := by
  funext a; simp [applyV, Tuple.toV]

/-- An **elementary condition** (Def 6.3): an equality or inequality between two entries. -/
inductive ECond (Val : Type v) (Var : Type w)
  | eq : VEntry Val Var → VEntry Val Var → ECond Val Var
  | ne : VEntry Val Var → VEntry Val Var → ECond Val Var

/-- A **condition** is a conjunction of elementary conditions (Def 6.3). (Named `CCond` — the
C-table condition — to avoid clashing with the tuple-calculus `Cond`.) -/
abbrev CCond (Val : Type v) (Var : Type w) : Type _ := List (ECond Val Var)

/-- Whether an elementary condition holds under a valuation. -/
def ECond.Holds (ν : Var → Val) : ECond Val Var → Prop
  | .eq e₁ e₂ => evalEntry ν e₁ = evalEntry ν e₂
  | .ne e₁ e₂ => evalEntry ν e₁ ≠ evalEntry ν e₂

/-- A condition holds under `ν` iff every conjunct does. -/
def CCond.Holds (ν : Var → Val) (F : CCond Val Var) : Prop := ∀ c ∈ F, c.Holds ν

/-- The empty condition holds under every valuation. -/
@[simp] theorem CCond.holds_nil (ν : Var → Val) : CCond.Holds ν ([] : CCond Val Var) := by
  simp [CCond.Holds]

/-- A condition `c :: F` holds iff `c` holds and `F` holds. -/
@[simp] theorem CCond.holds_cons (ν : Var → Val) (c : ECond Val Var) (F : CCond Val Var) :
    CCond.Holds ν (c :: F) ↔ c.Holds ν ∧ CCond.Holds ν F := by
  simp [CCond.Holds]

/-- A **conditional table** (C-table, §6.1): V-tuples each tagged with a condition, plus a global
condition constraining the admissible valuations. -/
structure CTable (Ω : Finset Att) (Val : Type v) (Var : Type w) where
  /-- The conditioned rows: V-tuples paired with their local condition. -/
  rows : Set (VTuple Ω Val Var × CCond Val Var)
  /-- The global condition, restricting which valuations are admissible. -/
  global : CCond Val Var

/-- The ordinary relation a C-table yields under a single valuation: the images of the rows whose
local condition holds under `ν`. -/
def CTable.instAt (T : CTable Ω Val Var) (ν : Var → Val) : Table Ω Val :=
  { t | ∃ p ∈ T.rows, p.2.Holds ν ∧ applyV ν p.1 = t }

@[simp] theorem CTable.mem_instAt {T : CTable Ω Val Var} {ν : Var → Val} {t : Tuple Ω Val} :
    t ∈ T.instAt ν ↔ ∃ p ∈ T.rows, p.2.Holds ν ∧ applyV ν p.1 = t := Iff.rfl

/-- **Representation of a C-table** (§6.1): the relations it denotes — its instances under all
valuations satisfying the global condition. -/
def CTable.rep (T : CTable Ω Val Var) : Set (Table Ω Val) :=
  { r | ∃ ν : Var → Val, T.global.Holds ν ∧ T.instAt ν = r }

theorem CTable.mem_rep {T : CTable Ω Val Var} {r : Table Ω Val} :
    r ∈ T.rep ↔ ∃ ν : Var → Val, T.global.Holds ν ∧ T.instAt ν = r := Iff.rfl

/-- A C-table with no rows denotes only the empty relation under every valuation. -/
@[simp] theorem CTable.instAt_empty (ν : Var → Val) (g : CCond Val Var) :
    CTable.instAt (Ω := Ω) ⟨∅, g⟩ ν = (∅ : Table Ω Val) := by
  ext t; simp [CTable.instAt]

end DeepWiki
