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

universe u v w

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

/-- A *first-order database-relation condition* over a database of base relations (all of scheme
`Ω₀`), in a context `Γ`: relation membership of a variable, a computable predicate on a variable,
heterogeneous agreement of two variables, the boolean connectives, and the existential tuple
quantifier (which extends the context). -/
inductive FOCond (ι : Type w) (Ω₀ : Finset Att) (Val : Type v) : Ctx Att → Type (max (max u v) w) where
  /-- The variable `v` lies in base relation `i`. -/
  | relA {Γ : Ctx Att} (v : Var Γ Ω₀) (i : ι) : FOCond ι Ω₀ Val Γ
  /-- The variable `v` (of scheme `Ω`) satisfies a computable predicate. -/
  | compA {Γ : Ctx Att} {Ω : Finset Att} (v : Var Γ Ω) (P : Tuple Ω Val → Prop) : FOCond ι Ω₀ Val Γ
  /-- The variables `v₁`, `v₂` agree on `X`. -/
  | agreeA {Γ : Ctx Att} {Ω Ω' : Finset Att} (v₁ : Var Γ Ω) (v₂ : Var Γ Ω') (X : Finset Att) :
      FOCond ι Ω₀ Val Γ
  /-- Negation. -/
  | neg {Γ : Ctx Att} (C : FOCond ι Ω₀ Val Γ) : FOCond ι Ω₀ Val Γ
  /-- Conjunction. -/
  | and {Γ : Ctx Att} (C D : FOCond ι Ω₀ Val Γ) : FOCond ι Ω₀ Val Γ
  /-- Disjunction. -/
  | or {Γ : Ctx Att} (C D : FOCond ι Ω₀ Val Γ) : FOCond ι Ω₀ Val Γ
  /-- Existential quantifier over a fresh tuple of scheme `Ω`. -/
  | ex {Γ : Ctx Att} (Ω : Finset Att) (C : FOCond ι Ω₀ Val (Ω :: Γ)) : FOCond ι Ω₀ Val Γ

variable {ι : Type w} {Ω₀ : Finset Att}

/-- The proposition a first-order condition asserts of an environment, over a database `db`. -/
def evalFO (db : ι → Table Ω₀ Val) : {Γ : Ctx Att} → FOCond ι Ω₀ Val Γ → Env Val Γ → Prop
  | _, .relA v i, e => lookup v e ∈ db i
  | _, .compA v P, e => P (lookup v e)
  | _, .agreeA v₁ v₂ X, e => VarAgree X v₁ v₂ e
  | _, .neg C, e => ¬ evalFO db C e
  | _, .and C D, e => evalFO db C e ∧ evalFO db D e
  | _, .or C D, e => evalFO db C e ∨ evalFO db D e
  | _, .ex Ω C, e => ∃ t : Tuple Ω Val, evalFO db C (t, e)

/-- The table denoted by a single-free-variable first-order condition `{t(Ω) | C}`. -/
def evalFOExpr (db : ι → Table Ω₀ Val) {Ω : Finset Att} (C : FOCond ι Ω₀ Val [Ω]) : Table Ω Val :=
  {t | evalFO db C (t, PUnit.unit)}

/-- The first-order expression for the projection of base relation `i` onto `Ω₁`:
`{s(Ω₁) | ∃ t(Ω₀), t ∈ db i ∧ s and t agree on Ω₁}`. -/
def projQuery (i : ι) (Ω₁ : Finset Att) : FOCond ι Ω₀ Val [Ω₁] :=
  FOCond.ex Ω₀
    (FOCond.and (FOCond.relA Var.here i) (FOCond.agreeA (Var.there Var.here) Var.here Ω₁))

/-- **Projection reduction** (§2.4): the projection of a base relation onto `Ω₁ ⊆ Ω₀` is
expressed by the first-order condition `projQuery` — an existential over the base relation,
constraining the free tuple to agree with the witness on `Ω₁`. -/
theorem evalFOExpr_projQuery (db : ι → Table Ω₀ Val) {Ω₁ : Finset Att} (h : Ω₁ ⊆ Ω₀) (i : ι) :
    evalFOExpr db (projQuery i Ω₁) = project h (db i) := by
  ext s
  simp only [evalFOExpr, projQuery, evalFO, lookup_here, lookup_there, VarAgree, mem_project,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, hag⟩
    refine ⟨t, ht, ?_⟩
    funext a
    exact (hag a.val a.property a.property (h a.property)).symm
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, fun _ _ _ _ => rfl⟩

end DeepWiki
