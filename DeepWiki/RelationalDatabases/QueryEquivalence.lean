import DeepWiki.RelationalDatabases.RelationalAlgebra
import DeepWiki.RelationalDatabases.RelationalAlgebraExpr

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

/-- The converse translation: every database-relation condition is a relational-algebra
expression (negation uses the universe `comp (fun _ => True)` minus the subexpression). -/
def qcondToAlg [DecidableEq Att] (db : ι → Table Ω Val) : QCond ι Ω Val → AlgExpr Att Val Ω
  | .rel i => AlgExpr.rel (db i)
  | .comp P => AlgExpr.comp P
  | .neg C => AlgExpr.diff (AlgExpr.comp (fun _ => True)) (qcondToAlg db C)
  | .and C D => (qcondToAlg db C).inter (qcondToAlg db D)
  | .or C D => AlgExpr.union (qcondToAlg db C) (qcondToAlg db D)

/-- The converse translation is correct: every quantifier-free database-relation calculus
condition denotes the same table as its algebra translation. Together with `evalQCond_select`,
`evalQCond_or` and `evalQCond_diff` this is the algebra ↔ calculus equivalence for the
quantifier-free (projection- and join-free) fragment. -/
theorem evalAlg_qcondToAlg [DecidableEq Att] (db : ι → Table Ω Val) (C : QCond ι Ω Val) :
    evalAlg (qcondToAlg db C) = evalQCond db C := by
  induction C with
  | rel i => rw [qcondToAlg, evalAlg_rel, evalQCond_rel]
  | comp P => rw [qcondToAlg, evalAlg_comp, evalQCond_comp]
  | neg C ih =>
    rw [qcondToAlg, evalAlg_diff, evalAlg_comp, ih, evalQCond_neg]
    ext t; simp only [mem_diff, Set.mem_setOf_eq, Set.mem_compl_iff, true_and]
  | and C D ihC ihD => rw [qcondToAlg, evalAlg_inter, ihC, ihD, evalQCond_and]
  | or C D ihC ihD => rw [qcondToAlg, evalAlg_union, ihC, ihD, evalQCond_or]

end DeepWiki
