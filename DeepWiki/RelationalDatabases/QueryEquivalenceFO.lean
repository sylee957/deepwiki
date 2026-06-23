import DeepWiki.RelationalDatabases.TupleCalculus

/-! # First-order database-relation calculus: variable infrastructure
Toward the full Codd equivalence: the existential quantifier (needed for projection and join)
requires a calculus with several tuple variables of possibly different schemes. This file builds
the de Bruijn variable machinery over the context/environment of `TupleCalculus`: a variable
`Var Γ Ω` names a tuple of scheme `Ω` at some position of the context `Γ`, `lookup` reads it from
an environment, and `VarAgree` is the heterogeneous agreement of two variables on the attributes
common to their schemes (the relationship a projection's existential asserts).

The first-order syntax (relation/computable/agreement atoms + the existential), its semantics and
the projection/join translations are layered on this. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v}

/-- A de Bruijn variable of scheme `Ω` in a context `Γ`: `Ω` occurs at some position of `Γ`. -/
inductive Var : Ctx Att → Finset Att → Type u where
  /-- The most recently bound variable. -/
  | here {Γ : Ctx Att} {Ω : Finset Att} : Var (Ω :: Γ) Ω
  /-- A variable bound further out. -/
  | there {Γ : Ctx Att} {Ω Ω' : Finset Att} : Var Γ Ω → Var (Ω' :: Γ) Ω

/-- Read the tuple bound to a de Bruijn variable from an environment. -/
def lookup : {Γ : Ctx Att} → {Ω : Finset Att} → Var Γ Ω → Env Val Γ → Tuple Ω Val
  | _, _, Var.here, (t, _) => t
  | _, _, Var.there v, (_, e) => lookup v e

@[simp] theorem lookup_here {Γ : Ctx Att} {Ω : Finset Att} (t : Tuple Ω Val) (e : Env Val Γ) :
    lookup Var.here (t, e) = t := rfl

@[simp] theorem lookup_there {Γ : Ctx Att} {Ω Ω' : Finset Att} (v : Var Γ Ω)
    (t : Tuple Ω' Val) (e : Env Val Γ) : lookup (Var.there v) (t, e) = lookup v e := rfl

/-- Heterogeneous agreement of two variables on `X`: their tuples share every value on an
attribute of `X` lying in both schemes. -/
def VarAgree {Γ : Ctx Att} {Ω Ω' : Finset Att} (X : Finset Att)
    (v₁ : Var Γ Ω) (v₂ : Var Γ Ω') (e : Env Val Γ) : Prop :=
  ∀ a ∈ X, ∀ (ha : a ∈ Ω) (ha' : a ∈ Ω'), lookup v₁ e ⟨a, ha⟩ = lookup v₂ e ⟨a, ha'⟩

/-- Heterogeneous agreement is symmetric. -/
theorem VarAgree.symm {Γ : Ctx Att} {Ω Ω' : Finset Att} {X : Finset Att}
    {v₁ : Var Γ Ω} {v₂ : Var Γ Ω'} {e : Env Val Γ} (h : VarAgree X v₁ v₂ e) :
    VarAgree X v₂ v₁ e :=
  fun a ha ha' ha'' => (h a ha ha'' ha').symm

/-- Agreement restricts to a smaller attribute set. -/
theorem VarAgree.mono {Γ : Ctx Att} {Ω Ω' : Finset Att} {X Y : Finset Att}
    {v₁ : Var Γ Ω} {v₂ : Var Γ Ω'} {e : Env Val Γ} (hsub : X ⊆ Y)
    (h : VarAgree Y v₁ v₂ e) : VarAgree X v₁ v₂ e :=
  fun a ha => h a (hsub ha)

end DeepWiki
