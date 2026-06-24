import DeepWiki.RelationalDatabases.QueryEquivalenceFO
import DeepWiki.RelationalDatabases.RelationalAlgebraExpr

/-! # Reduction of the tuple calculus to the algebra (§2.4): context flattening
The hard direction of Codd's theorem. The book's method (§2.4.1) tags each tuple variable's
attributes by its index, forming a clash-free *product scheme*, then translates recursively. Here
the de Bruijn context already *is* the tagging: this file builds the bridge from a context to its
product scheme — `flattenCtx Γ` is the union of all the variable schemes, and `envToTuple` glues an
environment into a single flat row over it. Under a pairwise-disjoint context (no attribute clashes,
so no renaming `ρ` is needed) reading a variable is reading the flat row restricted to its scheme;
the recursive translation of conditions is layered on this. -/

namespace DeepWiki

universe u v w

variable {Att : Type u} [DecidableEq Att] {Val : Type v}

/-- The *product scheme* of a context: the union of all its variable schemes. -/
def flattenCtx : Ctx Att → Finset Att
  | [] => ∅
  | Ω :: Γ => Ω ∪ flattenCtx Γ

@[simp] theorem flattenCtx_nil : flattenCtx ([] : Ctx Att) = ∅ := rfl

@[simp] theorem flattenCtx_cons (Ω : Finset Att) (Γ : Ctx Att) :
    flattenCtx (Ω :: Γ) = Ω ∪ flattenCtx Γ := rfl

theorem mem_flattenCtx_cons {a : Att} {Ω : Finset Att} {Γ : Ctx Att} :
    a ∈ flattenCtx (Ω :: Γ) ↔ a ∈ Ω ∨ a ∈ flattenCtx Γ := by
  simp [flattenCtx]

/-- Glue an environment into a single flat row over the product scheme: each attribute reads from
the first (innermost) variable whose scheme contains it. -/
def envToTuple : {Γ : Ctx Att} → Env Val Γ → Tuple (flattenCtx Γ) Val
  | [], _ => fun a => absurd a.property (Finset.notMem_empty a.val)
  | Ω :: _, (t, e) => fun a =>
      if h : a.val ∈ Ω then t ⟨a.val, h⟩
      else (envToTuple e) ⟨a.val, (mem_flattenCtx_cons.mp a.property).resolve_left h⟩

/-- An attribute of any context scheme lies in the product scheme. -/
theorem mem_flattenCtx_of_mem {a : Att} {Ω : Finset Att} {Γ : Ctx Att} (hΩ : Ω ∈ Γ)
    (ha : a ∈ Ω) : a ∈ flattenCtx Γ := by
  induction Γ with
  | nil => exact absurd hΩ (by simp)
  | cons Ω' Γ' ih =>
    rw [mem_flattenCtx_cons]
    rcases List.mem_cons.mp hΩ with h | h
    · exact Or.inl (h ▸ ha)
    · exact Or.inr (ih h)

/-- A *disjoint context*: the variable schemes are pairwise disjoint (no attribute clashes, so the
book's renaming `ρ` is unnecessary). -/
def CtxDisjoint (Γ : Ctx Att) : Prop := Γ.Pairwise Disjoint

omit [DecidableEq Att] in
/-- The scheme of a de Bruijn variable occurs in its context. -/
theorem Var.scheme_mem : {Γ : Ctx Att} → {Ω : Finset Att} → Var Γ Ω → Ω ∈ Γ
  | _, _, .here => List.mem_cons.mpr (.inl rfl)
  | _, _, .there v => List.mem_cons.mpr (.inr v.scheme_mem)

/-- **Lookup bridge**: in a disjoint context, reading a variable equals the flattened row restricted
to that variable's scheme. -/
theorem lookup_eq_envToTuple : {Γ : Ctx Att} → {Ω : Finset Att} → (v : Var Γ Ω) →
    CtxDisjoint Γ → (e : Env Val Γ) → {a : Att} → (ha : a ∈ Ω) → (hflat : a ∈ flattenCtx Γ) →
    lookup v e ⟨a, ha⟩ = envToTuple e ⟨a, hflat⟩
  | _, _, .here, _, (_, _), a, ha, _ => by
      simp only [lookup, envToTuple, dif_pos ha]
  | _, _, .there v', hd, (_, e'), a, ha, _ => by
      have hne : a ∉ _ := Finset.disjoint_right.mp ((List.pairwise_cons.mp hd).1 _ v'.scheme_mem) ha
      simp only [lookup, envToTuple, dif_neg hne]
      exact lookup_eq_envToTuple v' (List.pairwise_cons.mp hd).2 e' ha _

/-- A context scheme is a subset of the product scheme. -/
theorem scheme_subset_flattenCtx {Ω : Finset Att} {Γ : Ctx Att} (hΩ : Ω ∈ Γ) :
    Ω ⊆ flattenCtx Γ := fun _ ha => mem_flattenCtx_of_mem hΩ ha

/-- The flat-row form of heterogeneous variable agreement on `X`: the row's `Ω`- and `Ω'`-parts
share every value on a common attribute of `X`. -/
def flatAgree {S Ω Ω' : Finset Att} (X : Finset Att) (sub₁ : Ω ⊆ S) (sub₂ : Ω' ⊆ S)
    (flat : Tuple S Val) : Prop :=
  ∀ a ∈ X, ∀ (h : a ∈ Ω) (h' : a ∈ Ω'), flat ⟨a, sub₁ h⟩ = flat ⟨a, sub₂ h'⟩

variable {ι : Type w} {sch : ι → Finset Att}

/-- **Reduction of the tuple calculus to the algebra** (§2.4): translate a first-order condition to
an algebra expression over the product scheme. Atoms become computable predicates (`comp`) on the
flat row; negation is the domain-relative complement (`DOM − ·`); conjunction/disjunction are
intersection/union; the existential is projection (dropping the bound variable's scheme). The
correctness holds on a disjoint context (the book's renaming `ρ` is unnecessary there). -/
def calcToAlg (db : (i : ι) → Table (sch i) Val) :
    {Γ : Ctx Att} → FOCond ι sch Val Γ → AlgExpr Att Val (flattenCtx Γ)
  | _, .relA i v =>
      AlgExpr.comp (fun flat => flat.restrict (scheme_subset_flattenCtx v.scheme_mem) ∈ db i)
  | _, .compA v P =>
      AlgExpr.comp (fun flat => P (flat.restrict (scheme_subset_flattenCtx v.scheme_mem)))
  | _, .agreeA v₁ v₂ X =>
      AlgExpr.comp (flatAgree X (scheme_subset_flattenCtx v₁.scheme_mem)
        (scheme_subset_flattenCtx v₂.scheme_mem))
  | _, .neg C => AlgExpr.diff (AlgExpr.comp (fun _ => True)) (calcToAlg db C)
  | _, .and C D => (calcToAlg db C).inter (calcToAlg db D)
  | _, .or C D => AlgExpr.union (calcToAlg db C) (calcToAlg db D)
  | _, .ex _ C => AlgExpr.proj Finset.subset_union_right (calcToAlg db C)

end DeepWiki
