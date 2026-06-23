import DeepWiki.RelationalDatabases.RelationalAlgebra

/-! # Algebraic expressions and their semantics
The syntax of the relational algebra as an inductive family `AlgExpr Ω` of expressions
denoting a table over the output attribute set `Ω`, together with the denotational semantics
`evalAlg : AlgExpr Ω → Table Ω` (the *view instance* an expression represents). Base operands
are relation instances (`rel`) and computable instances (`comp`, covering `DOM(A)` and the
comparative instances); the operators are projection, selection, join, union and difference.

This makes "expressible in the relational algebra" a formal object — the target into which the
tuple calculus and SQL reductions land. The generating part (everything but selection) already
expresses intersection, the first expressive-completeness step (`evalAlg_inter`). -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v} [DecidableEq Att]

/-- An *algebraic expression* over output attributes `Ω` (the generating part plus selection):
a syntactic query denoting a table over `Ω`. -/
inductive AlgExpr (Att : Type u) (Val : Type v) [DecidableEq Att] :
    Finset Att → Type (max u v) where
  /-- A base relation instance over `Ω`. -/
  | rel {Ω : Finset Att} (v : Table Ω Val) : AlgExpr Att Val Ω
  /-- A computable instance `{t | f t}` over `Ω` (covers `DOM(A)` and comparative instances). -/
  | comp {Ω : Finset Att} (f : Tuple Ω Val → Prop) : AlgExpr Att Val Ω
  /-- Projection `Π(e; Ω₁)` of `e` onto `Ω₁ ⊆ Ω`. -/
  | proj {Ω Ω₁ : Finset Att} (h : Ω₁ ⊆ Ω) (e : AlgExpr Att Val Ω) : AlgExpr Att Val Ω₁
  /-- Selection `σ(e; P)`. -/
  | sel {Ω : Finset Att} (P : Tuple Ω Val → Prop) (e : AlgExpr Att Val Ω) : AlgExpr Att Val Ω
  /-- Join `e ⋈ e'`. -/
  | join {Ω Ω' : Finset Att} (e : AlgExpr Att Val Ω) (e' : AlgExpr Att Val Ω') :
      AlgExpr Att Val (Ω ∪ Ω')
  /-- Union `e ∪ e'`. -/
  | union {Ω : Finset Att} (e e' : AlgExpr Att Val Ω) : AlgExpr Att Val Ω
  /-- Difference `e − e'`. -/
  | diff {Ω : Finset Att} (e e' : AlgExpr Att Val Ω) : AlgExpr Att Val Ω

/-- The *view instance* represented by an algebraic expression: its denotational semantics as
a table over the output attributes. -/
def evalAlg : {Ω : Finset Att} → AlgExpr Att Val Ω → Table Ω Val
  | _, .rel v => v
  | _, .comp f => {t | f t}
  | _, .proj h e => project h (evalAlg e)
  | _, .sel P e => select P (evalAlg e)
  | _, .join e e' => join (evalAlg e) (evalAlg e')
  | _, .union e e' => union (evalAlg e) (evalAlg e')
  | _, .diff e e' => diff (evalAlg e) (evalAlg e')

@[simp] theorem evalAlg_rel {Ω : Finset Att} (v : Table Ω Val) :
    evalAlg (AlgExpr.rel v) = v := rfl

@[simp] theorem evalAlg_comp {Ω : Finset Att} (f : Tuple Ω Val → Prop) :
    evalAlg (AlgExpr.comp (Att := Att) (Val := Val) f) = {t | f t} := rfl

@[simp] theorem evalAlg_proj {Ω Ω₁ : Finset Att} (h : Ω₁ ⊆ Ω) (e : AlgExpr Att Val Ω) :
    evalAlg (AlgExpr.proj h e) = project h (evalAlg e) := rfl

@[simp] theorem evalAlg_sel {Ω : Finset Att} (P : Tuple Ω Val → Prop) (e : AlgExpr Att Val Ω) :
    evalAlg (AlgExpr.sel P e) = select P (evalAlg e) := rfl

@[simp] theorem evalAlg_join {Ω Ω' : Finset Att} (e : AlgExpr Att Val Ω) (e' : AlgExpr Att Val Ω') :
    evalAlg (AlgExpr.join e e') = join (evalAlg e) (evalAlg e') := rfl

@[simp] theorem evalAlg_union {Ω : Finset Att} (e e' : AlgExpr Att Val Ω) :
    evalAlg (AlgExpr.union e e') = union (evalAlg e) (evalAlg e') := rfl

@[simp] theorem evalAlg_diff {Ω : Finset Att} (e e' : AlgExpr Att Val Ω) :
    evalAlg (AlgExpr.diff e e') = diff (evalAlg e) (evalAlg e') := rfl

/-- Two algebraic expressions are *equivalent* when they denote the same view instance. -/
def AlgEquiv {Ω : Finset Att} (e e' : AlgExpr Att Val Ω) : Prop := evalAlg e = evalAlg e'

/-- Intersection as a generating-part expression: `e ∩ e' := e − (e − e')`. -/
def AlgExpr.inter {Ω : Finset Att} (e e' : AlgExpr Att Val Ω) : AlgExpr Att Val Ω :=
  .diff e (.diff e e')

/-- The generating part expresses intersection: `e − (e − e')` denotes `e ∩ e'`
(expressive-completeness, intersection step). -/
@[simp] theorem evalAlg_inter {Ω : Finset Att} (e e' : AlgExpr Att Val Ω) :
    evalAlg (e.inter e') = DeepWiki.inter (evalAlg e) (evalAlg e') := by
  show diff (evalAlg e) (diff (evalAlg e) (evalAlg e')) = DeepWiki.inter (evalAlg e) (evalAlg e')
  exact (inter_eq_diff_diff _ _).symm

end DeepWiki
