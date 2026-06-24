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

end DeepWiki
