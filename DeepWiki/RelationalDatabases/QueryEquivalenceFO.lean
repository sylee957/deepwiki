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

/-- A *first-order database-relation condition* over a database with relation schemes `sch`, in a
context `Γ`: relation membership of a variable (of the relation's scheme), a computable predicate
on a variable, heterogeneous agreement of two variables, the boolean connectives, and the
existential tuple quantifier (which extends the context). -/
inductive FOCond (ι : Type w) (sch : ι → Finset Att) (Val : Type v) :
    Ctx Att → Type (max (max u v) w) where
  /-- The variable `v` (of relation `i`'s scheme) lies in base relation `i`. -/
  | relA {Γ : Ctx Att} (i : ι) (v : Var Γ (sch i)) : FOCond ι sch Val Γ
  /-- The variable `v` (of scheme `Ω`) satisfies a computable predicate. -/
  | compA {Γ : Ctx Att} {Ω : Finset Att} (v : Var Γ Ω) (P : Tuple Ω Val → Prop) : FOCond ι sch Val Γ
  /-- The variables `v₁`, `v₂` agree on `X`. -/
  | agreeA {Γ : Ctx Att} {Ω Ω' : Finset Att} (v₁ : Var Γ Ω) (v₂ : Var Γ Ω') (X : Finset Att) :
      FOCond ι sch Val Γ
  /-- Negation. -/
  | neg {Γ : Ctx Att} (C : FOCond ι sch Val Γ) : FOCond ι sch Val Γ
  /-- Conjunction. -/
  | and {Γ : Ctx Att} (C D : FOCond ι sch Val Γ) : FOCond ι sch Val Γ
  /-- Disjunction. -/
  | or {Γ : Ctx Att} (C D : FOCond ι sch Val Γ) : FOCond ι sch Val Γ
  /-- Existential quantifier over a fresh tuple of scheme `Ω`. -/
  | ex {Γ : Ctx Att} (Ω : Finset Att) (C : FOCond ι sch Val (Ω :: Γ)) : FOCond ι sch Val Γ

variable {ι : Type w} {sch : ι → Finset Att}

/-- The proposition a first-order condition asserts of an environment, over a database `db`. -/
def evalFO (db : (i : ι) → Table (sch i) Val) :
    {Γ : Ctx Att} → FOCond ι sch Val Γ → Env Val Γ → Prop
  | _, .relA i v, e => lookup v e ∈ db i
  | _, .compA v P, e => P (lookup v e)
  | _, .agreeA v₁ v₂ X, e => VarAgree X v₁ v₂ e
  | _, .neg C, e => ¬ evalFO db C e
  | _, .and C D, e => evalFO db C e ∧ evalFO db D e
  | _, .or C D, e => evalFO db C e ∨ evalFO db D e
  | _, .ex Ω C, e => ∃ t : Tuple Ω Val, evalFO db C (t, e)

/-- The table denoted by a single-free-variable first-order condition `{t(Ω) | C}`. -/
def evalFOExpr (db : (i : ι) → Table (sch i) Val) {Ω : Finset Att} (C : FOCond ι sch Val [Ω]) :
    Table Ω Val :=
  {t | evalFO db C (t, PUnit.unit)}

/-- The first-order expression for the projection of base relation `i` onto `Ω₁`:
`{s(Ω₁) | ∃ t(sch i), t ∈ db i ∧ s and t agree on Ω₁}`. -/
def projQuery (i : ι) (Ω₁ : Finset Att) : FOCond ι sch Val [Ω₁] :=
  FOCond.ex (sch i)
    (FOCond.and (FOCond.relA i Var.here) (FOCond.agreeA (Var.there Var.here) Var.here Ω₁))

/-- **Projection reduction** (§2.4): the projection of a base relation onto `Ω₁ ⊆ sch i` is
expressed by `projQuery` — an existential over the base relation, constraining the free tuple to
agree with the witness on `Ω₁`. -/
theorem evalFOExpr_projQuery (db : (i : ι) → Table (sch i) Val) (i : ι) {Ω₁ : Finset Att}
    (h : Ω₁ ⊆ sch i) : evalFOExpr db (projQuery i Ω₁) = project h (db i) := by
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

/-- The first-order expression for the join of base relations `i` and `j`:
`{t(sch i ∪ sch j) | ∃ u(sch i), ∃ w(sch j), u ∈ db i ∧ w ∈ db j ∧ t agrees with u on sch i and
with w on sch j}`. -/
def joinQuery [DecidableEq Att] (i j : ι) : FOCond ι sch Val [sch i ∪ sch j] :=
  FOCond.ex (sch i) (FOCond.ex (sch j)
    (FOCond.and (FOCond.relA i (Var.there Var.here))
      (FOCond.and (FOCond.relA j Var.here)
        (FOCond.and
          (FOCond.agreeA (Var.there (Var.there Var.here)) (Var.there Var.here) (sch i))
          (FOCond.agreeA (Var.there (Var.there Var.here)) Var.here (sch j))))))

/-- **Join reduction** (§2.4): the join of two base relations is expressed by `joinQuery` — two
existentials pinning the `sch i`- and `sch j`-parts of the free tuple to rows of `db i` and
`db j`. -/
theorem evalFOExpr_joinQuery [DecidableEq Att] (db : (i : ι) → Table (sch i) Val) (i j : ι) :
    evalFOExpr db (joinQuery i j) = join (db i) (db j) := by
  ext t
  simp only [evalFOExpr, joinQuery, evalFO, lookup_here, lookup_there, VarAgree, mem_join,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, w, hu, hw, hagu, hagw⟩
    refine ⟨?_, ?_⟩
    · have : t.restrict Finset.subset_union_left = u := by
        funext x; exact hagu x.val x.property (Finset.subset_union_left x.property) x.property
      rw [this]; exact hu
    · have : t.restrict Finset.subset_union_right = w := by
        funext x; exact hagw x.val x.property (Finset.subset_union_right x.property) x.property
      rw [this]; exact hw
  · rintro ⟨hi, hj⟩
    exact ⟨t.restrict Finset.subset_union_left, t.restrict Finset.subset_union_right, hi, hj,
      fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

end DeepWiki
