import DeepWiki.RelationalDatabases.RelationalAlgebra

/-! # Query-system equivalence (Codd's theorem), foundation
The relational algebra, the tuple calculus and SQL express the same queries (§2.4–2.6). A
faithful statement requires the calculus to reference only the *database relations* and
computable predicates — a generic "membership in an arbitrary table" atom would trivialise the
equivalence. We therefore fix a database `db : ι → Table Ω Val` of base relations and build the
tuple calculus over those relations.

This file establishes the foundation and the quantifier-free fragment: a condition over `db`
denotes a table, and the boolean connectives realise exactly selection, union and difference of
base relations. The existential quantifier (needed for projection and join), the full
algebra↔calculus translation and the SQL leg are layered on in later steps. -/

namespace DeepWiki

universe u v w

variable {Att : Type u} {Val : Type v} {Ω : Finset Att}

/-- A *database-relation calculus condition* over a database `db : ι → Table Ω Val`
(quantifier-free, single free tuple): the free tuple lies in a base relation (`rel i`),
satisfies a computable predicate (`comp`), or a boolean combination. -/
inductive QCond (ι : Type w) (Ω : Finset Att) (Val : Type v) where
  /-- The free tuple is in the base relation `db i`. -/
  | rel : ι → QCond ι Ω Val
  /-- The free tuple satisfies a computable predicate. -/
  | comp : (Tuple Ω Val → Prop) → QCond ι Ω Val
  /-- Negation (complement over all tuples). -/
  | neg : QCond ι Ω Val → QCond ι Ω Val
  /-- Conjunction. -/
  | and : QCond ι Ω Val → QCond ι Ω Val → QCond ι Ω Val
  /-- Disjunction. -/
  | or : QCond ι Ω Val → QCond ι Ω Val → QCond ι Ω Val

/-- The table denoted by a database-relation calculus condition over `db`. -/
def evalQCond {ι : Type w} (db : ι → Table Ω Val) : QCond ι Ω Val → Table Ω Val
  | .rel i => db i
  | .comp P => {t | P t}
  | .neg C => (evalQCond db C)ᶜ
  | .and C D => evalQCond db C ∩ evalQCond db D
  | .or C D => evalQCond db C ∪ evalQCond db D

variable {ι : Type w} {db : ι → Table Ω Val}

@[simp] theorem evalQCond_rel (i : ι) : evalQCond db (QCond.rel i) = db i := by
  simp only [evalQCond]

@[simp] theorem evalQCond_comp (P : Tuple Ω Val → Prop) :
    evalQCond db (QCond.comp (ι := ι) P) = {t | P t} := by simp only [evalQCond]

@[simp] theorem evalQCond_or (C D : QCond ι Ω Val) :
    evalQCond db (C.or D) = union (evalQCond db C) (evalQCond db D) := by simp only [evalQCond, union]

@[simp] theorem evalQCond_and (C D : QCond ι Ω Val) :
    evalQCond db (C.and D) = inter (evalQCond db C) (evalQCond db D) := by
  simp only [evalQCond, inter]

@[simp] theorem evalQCond_neg (C : QCond ι Ω Val) :
    evalQCond db C.neg = (evalQCond db C)ᶜ := by simp only [evalQCond]

/-- Selection of a base relation is the calculus condition `rel i ∧ comp P`. -/
theorem evalQCond_select (i : ι) (P : Tuple Ω Val → Prop) :
    evalQCond db ((QCond.rel i).and (QCond.comp P)) = select P (db i) := by
  rw [evalQCond_and, evalQCond_rel, evalQCond_comp]
  ext t
  simp only [mem_inter, mem_select, Set.mem_setOf_eq]

/-- Difference of base-relation conditions is `C ∧ ¬D`. -/
theorem evalQCond_diff (C D : QCond ι Ω Val) :
    evalQCond db (C.and D.neg) = diff (evalQCond db C) (evalQCond db D) := by
  rw [evalQCond_and, evalQCond_neg]
  ext t
  simp only [mem_inter, mem_diff, Set.mem_compl_iff]

end DeepWiki
