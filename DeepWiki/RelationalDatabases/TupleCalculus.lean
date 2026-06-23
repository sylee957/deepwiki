import DeepWiki.RelationalDatabases.RelationalAlgebra

/-! # The tuple calculus
The tuple calculus as a deep embedding: conditions over a de Bruijn context of tuple variables
(each variable ranging over rows of its own attribute set), with denotational semantics into
`Prop`. A calculus expression `{t(A₁,…,Aₙ) | C}` denotes the table of rows satisfying `C`.

The primitives are a generic atom (an environment predicate), negation, disjunction and the
existential tuple quantifier; conjunction, implication and the universal quantifier are derived
forms, and the generating-part identities `∀ = ¬∃¬`, `∧ = ¬(¬∨¬)`, `⇒ = ¬∨` are proved at the
semantic level (so the generating part generates the whole calculus). The concrete atom shapes
`r(t)`, `f(…)`, `t(A) θ t'(B)` and the reduction to the algebra are layered on top later. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v}

/-- A typing context for tuple variables (de Bruijn): the attribute set of each variable. -/
abbrev Ctx (Att : Type u) : Type u := List (Finset Att)

/-- An environment for a context: a row for each tuple variable in scope. -/
def Env (Val : Type v) : Ctx Att → Type (max u v)
  | [] => PUnit
  | Ω :: Γ => Tuple Ω Val × Env Val Γ

/-- A *condition* of the tuple calculus over a context `Γ`: a generic atom (an environment
predicate), negation, disjunction, and the existential tuple quantifier (which extends the
context by one variable). -/
inductive Cond (Att : Type u) (Val : Type v) : Ctx Att → Type (max u v) where
  /-- A generic atom: a predicate on the environment (covers `r(t)`, `f(…)`, comparisons). -/
  | atom {Γ : Ctx Att} (p : Env Val Γ → Prop) : Cond Att Val Γ
  /-- Negation `¬C`. -/
  | neg {Γ : Ctx Att} (C : Cond Att Val Γ) : Cond Att Val Γ
  /-- Disjunction `C ∨ D`. -/
  | disj {Γ : Ctx Att} (C D : Cond Att Val Γ) : Cond Att Val Γ
  /-- Existential quantifier `∃ t : Tuple Ω, C` (binds a new tuple variable). -/
  | ex {Γ : Ctx Att} (Ω : Finset Att) (C : Cond Att Val (Ω :: Γ)) : Cond Att Val Γ

/-- The semantics of a condition: the proposition it asserts of an environment. The existential
ranges over all rows of the bound attribute set (full domain `Val`). -/
def evalCond : {Γ : Ctx Att} → Cond Att Val Γ → Env Val Γ → Prop
  | _, .atom p, e => p e
  | _, .neg C, e => ¬ evalCond C e
  | _, .disj C D, e => evalCond C e ∨ evalCond D e
  | _, .ex Ω C, e => ∃ t : Tuple Ω Val, evalCond C (t, e)

/-- Conjunction as a derived form: `C ∧ D := ¬(¬C ∨ ¬D)`. -/
def Cond.conj {Γ : Ctx Att} (C D : Cond Att Val Γ) : Cond Att Val Γ :=
  .neg (.disj (.neg C) (.neg D))

/-- Implication as a derived form: `C ⇒ D := ¬C ∨ D`. -/
def Cond.imp {Γ : Ctx Att} (C D : Cond Att Val Γ) : Cond Att Val Γ :=
  .disj (.neg C) D

/-- The universal quantifier as a derived form: `∀ t, C := ¬∃ t, ¬C`. -/
def Cond.all {Γ : Ctx Att} (Ω : Finset Att) (C : Cond Att Val (Ω :: Γ)) : Cond Att Val Γ :=
  .neg (.ex Ω (.neg C))

@[simp] theorem evalCond_atom {Γ : Ctx Att} (p : Env Val Γ → Prop) (e : Env Val Γ) :
    evalCond (Cond.atom p) e ↔ p e := Iff.rfl

@[simp] theorem evalCond_neg {Γ : Ctx Att} (C : Cond Att Val Γ) (e : Env Val Γ) :
    evalCond (Cond.neg C) e ↔ ¬ evalCond C e := Iff.rfl

@[simp] theorem evalCond_disj {Γ : Ctx Att} (C D : Cond Att Val Γ) (e : Env Val Γ) :
    evalCond (Cond.disj C D) e ↔ evalCond C e ∨ evalCond D e := Iff.rfl

@[simp] theorem evalCond_ex {Γ : Ctx Att} (Ω : Finset Att) (C : Cond Att Val (Ω :: Γ))
    (e : Env Val Γ) : evalCond (Cond.ex Ω C) e ↔ ∃ t : Tuple Ω Val, evalCond C (t, e) := Iff.rfl

/-- The generating part expresses conjunction: `¬(¬C ∨ ¬D)` asserts `C ∧ D`. -/
theorem evalCond_conj {Γ : Ctx Att} (C D : Cond Att Val Γ) (e : Env Val Γ) :
    evalCond (C.conj D) e ↔ evalCond C e ∧ evalCond D e := by
  classical
  simp only [Cond.conj, evalCond_neg, evalCond_disj]
  tauto

/-- The generating part expresses implication: `¬C ∨ D` asserts `C ⇒ D`. -/
theorem evalCond_imp {Γ : Ctx Att} (C D : Cond Att Val Γ) (e : Env Val Γ) :
    evalCond (C.imp D) e ↔ (evalCond C e → evalCond D e) := by
  classical
  simp only [Cond.imp, evalCond_disj, evalCond_neg]
  tauto

/-- The generating part expresses the universal quantifier: `¬∃ t, ¬C` asserts `∀ t, C`. -/
theorem evalCond_all {Γ : Ctx Att} (Ω : Finset Att) (C : Cond Att Val (Ω :: Γ)) (e : Env Val Γ) :
    evalCond (C.all Ω) e ↔ ∀ t : Tuple Ω Val, evalCond C (t, e) := by
  classical
  simp only [Cond.all, evalCond_neg, evalCond_ex, not_exists, not_not]

/-- The *view instance represented by a calculus expression* `{t(Ω) | C}`: the rows `t` over
`Ω` for which the single-free-variable condition `C` holds. -/
def evalCalcExpr {Ω : Finset Att} (C : Cond Att Val [Ω]) : Table Ω Val :=
  {t | evalCond C (t, PUnit.unit)}

@[simp] theorem mem_evalCalcExpr {Ω : Finset Att} (C : Cond Att Val [Ω]) (t : Tuple Ω Val) :
    t ∈ evalCalcExpr C ↔ evalCond C (t, PUnit.unit) := Iff.rfl

end DeepWiki
