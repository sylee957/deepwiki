import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic

/-! # Boolean satisfiability (CNF-SAT)
The decision problem at the base of NP-completeness: a CNF formula and the question of whether some
Boolean assignment satisfies it. Pure data + a decidable evaluator; the NP-membership verifier and the
Cook–Levin reduction are built on top of this (`CookLevin.lean`).

A formula is a conjunction of clauses; a clause a disjunction of literals; a literal a variable index
with a sign. `Satisfiable` is decidable (finitely many assignments over `Fin n → Bool`).
-/

namespace DeepWiki

/-- A **literal** over `n` Boolean variables: a variable index with a sign (`true` = positive
occurrence, `false` = negated). -/
abbrev Literal (n : ℕ) := Fin n × Bool

/-- A **clause**: a disjunction of literals over `n` variables. -/
abbrev Clause (n : ℕ) := List (Literal n)

/-- A **CNF formula**: a conjunction of clauses over a fixed number of variables. -/
structure CnfFormula where
  /-- the number of Boolean variables -/
  numVars : ℕ
  /-- the conjuncts (clauses) -/
  clauses : List (Clause numVars)

namespace CnfFormula

/-- A literal `(v, s)` is satisfied by `assign` iff `assign v = s`. -/
def litSat {n : ℕ} (assign : Fin n → Bool) (l : Literal n) : Bool := assign l.1 == l.2

/-- A clause is satisfied by `assign` iff at least one of its literals is. -/
def clauseSat {n : ℕ} (assign : Fin n → Bool) (c : Clause n) : Bool := c.any (litSat assign)

/-- A formula `φ` evaluates to `true` under `assign` iff every clause is satisfied. -/
def eval (φ : CnfFormula) (assign : Fin φ.numVars → Bool) : Bool :=
  φ.clauses.all (clauseSat assign)

/-- The **total size** of a formula: variable count plus the total number of literal occurrences —
the natural encoding-size measure for the poly-time bounds. -/
def size (φ : CnfFormula) : ℕ := φ.numVars + (φ.clauses.map List.length).sum

end CnfFormula

/-- A CNF formula is **satisfiable** iff some Boolean assignment makes it evaluate to `true`. This is
the SAT decision problem. -/
def Satisfiable (φ : CnfFormula) : Prop := ∃ assign : Fin φ.numVars → Bool, φ.eval assign = true

/-- `Satisfiable` is decidable: there are finitely many assignments `Fin n → Bool`. -/
instance (φ : CnfFormula) : Decidable (Satisfiable φ) :=
  Fintype.decidableExistsFintype

/-- The **empty formula** (no clauses) is satisfied by every assignment. -/
@[simp] theorem eval_nil {n : ℕ} (assign : Fin n → Bool) :
    CnfFormula.eval ⟨n, []⟩ assign = true := rfl

/-- A formula with no clauses is satisfiable (as long as it has at least the empty assignment, which it
always does). -/
theorem satisfiable_of_clauses_nil {n : ℕ} : Satisfiable ⟨n, []⟩ :=
  ⟨fun _ => false, rfl⟩

/-- A clause containing **no literals** (the empty disjunction) is satisfied by no assignment. -/
@[simp] theorem clauseSat_nil {n : ℕ} (assign : Fin n → Bool) :
    CnfFormula.clauseSat assign ([] : Clause n) = false := rfl

/-- A formula containing an **empty clause** is unsatisfiable: the empty disjunction is never true, so
the conjunction fails on every assignment. -/
theorem not_satisfiable_of_mem_clause_nil {φ : CnfFormula} (h : ([] : Clause φ.numVars) ∈ φ.clauses) :
    ¬ Satisfiable φ := by
  rintro ⟨assign, hassign⟩
  rw [CnfFormula.eval, List.all_eq_true] at hassign
  simpa using hassign [] h

end DeepWiki
