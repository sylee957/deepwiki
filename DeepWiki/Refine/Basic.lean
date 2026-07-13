/-! # A relational refinement kernel (CoqEAL/Trocq-style), isolated — no `simp`

The principled core of proof transfer: a heterogeneous **refinement relation** `R : C → A → Prop`
between a concrete (computable) type `C` and an abstract type `A`, the **respectful arrow** `⟹`
lifting relations to function types, and the **single composition rule** `Refines.app` that a
resolver chains to transfer a whole term. This is the relational logic behind Isabelle's `Transfer`,
CoqEAL's `refines`, and Trocq — built directly, not on top of `simp`/`@[denote]`.

The automation (a `MetaM` resolver that decomposes a term by head symbol, looks up per-operation
witnesses, and composes via `Refines.app` with explicit higher-order unification — the step Lean's
typeclass synthesis refuses) is a separate layer built on this core. -/

namespace DeepWiki.Refine

universe u v u' v'

/-- `Refines R c a`: concrete `c` and abstract `a` are related by the refinement relation `R`. A
class so per-operation witnesses can be indexed and looked up. -/
class Refines {C : Type u} {A : Type v} (R : C → A → Prop) (c : C) (a : A) : Prop where
  /-- The underlying relatedness proof. -/
  prf : R c a

/-- The **respectful arrow**: functions are related iff they send related inputs to related outputs —
the relational interpretation of the function type (`respectful` / `==>` in Coq's `Morphisms`). -/
@[reducible] def Respectful {C : Type u} {A : Type v} {C' : Type u'} {A' : Type v'}
    (R : C → A → Prop) (S : C' → A' → Prop) : (C → C') → (A → A') → Prop :=
  fun f g => ∀ c a, R c a → S (f c) (g a)

@[inherit_doc] scoped infixr:40 " ⟹ " => Respectful

/-- The **composition rule**: a related function applied to a related argument yields related results.
This single lemma, chained, transfers an entire applicative term (`refines_apply` in CoqEAL). -/
theorem Refines.app {C : Type u} {A : Type v} {C' : Type u'} {A' : Type v'}
    {R : C → A → Prop} {S : C' → A' → Prop} {f : C → C'} {g : A → A'} {c : C} {a : A}
    (hf : Refines (R ⟹ S) f g) (hc : Refines R c a) : Refines S (f c) (g a) :=
  ⟨hf.prf c a hc.prf⟩

/-- A **functional refinement**: the relation `denote c = a`. Under it, every term refines its own
denotation (the leaf case of the resolver), and per-operation witnesses are exactly the denotation
homomorphism squares `denote (op x y) = absOp (denote x) (denote y)`. -/
def DenoteRel {C : Type u} {A : Type v} (denote : C → A) : C → A → Prop :=
  fun c a => denote c = a

/-- Under a functional relation, a term refines its denotation — the resolver's leaf rule. -/
theorem refines_denote {C : Type u} {A : Type v} (denote : C → A) (c : C) :
    Refines (DenoteRel denote) c (denote c) := ⟨rfl⟩

/-- `Subsumes R S`: the finer relation `R` implies the coarser `S`. Registering these gives the
resolver a **relation-hierarchy coercion** (Trocq's relation lattice): a transfer proved at `R` can be
weakened to `S` (e.g. equality `⟹` associated-up-to-a-unit). -/
def Subsumes {C : Type u} {A : Type v} (R S : C → A → Prop) : Prop := ∀ c a, R c a → S c a

/-- Weaken a refinement along a subsumption `R ⊑ S`. -/
theorem Refines.weaken {C : Type u} {A : Type v} {R S : C → A → Prop} {c : C} {a : A}
    (h : Subsumes R S) (hr : Refines R c a) : Refines S c a := ⟨h c a hr.prf⟩

end DeepWiki.Refine
