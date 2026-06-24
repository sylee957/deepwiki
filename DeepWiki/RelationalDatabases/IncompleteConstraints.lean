import DeepWiki.RelationalDatabases.ConditionalTables
import DeepWiki.RelationalDatabases.FunctionalDependencies

/-! # Constraints in incomplete databases — §6.3
Functional dependencies over a V-table (entries are constants or marked variables). A *completion*
fills the variables with a valuation; the V-table is *permissible* under a set of fds if some
completion satisfies them (Def 6.5). Def 6.6 splits the obstruction into **hard** violations — two
rows that agree on `X` carry *different constants* on `A`, which no valuation can repair — and
**soft** violations — they differ on `A` but at least one entry is a variable, repairable by filling
in. The forward direction of Theorem 6.9 is here: a hard violation of a required fd blocks
permissibility. (The converse — exhaustive fill-in with no hard violation yields a permissible
completion — needs the fill-in process as a terminating function; deferred.) -/

namespace DeepWiki

universe u v w

variable {Att : Type u} {Val : Type v} {Var : Type w} {Ω : Finset Att}

/-- Two V-tuples *agree on* `X` when they carry identical entries (constants or variables) on every
attribute of `X`. -/
def VAgree (X : Finset Att) (t₁ t₂ : VTuple Ω Val Var) : Prop :=
  ∀ a : {x : Att // x ∈ Ω}, a.val ∈ X → t₁ a = t₂ a

/-- Entry-agreement is preserved by every valuation: agreeing V-tuples have agreeing completions. -/
theorem applyV_agree_of_vAgree {X : Finset Att} {t₁ t₂ : VTuple Ω Val Var} (h : VAgree X t₁ t₂)
    (ν : Var → Val) : Agree X (applyV ν t₁) (applyV ν t₂) :=
  fun a ha => by simp only [applyV_apply, h a ha]

/-- **Definition 6.5** (§6.3): a V-table is *permissible* under a set of fds when some completion
(the image `applyV ν '' T` of a valuation) satisfies every fd. -/
def IsPermissible (T : VTable Ω Val Var) (F : Set (Finset Att × Finset Att)) : Prop :=
  ∃ ν : Var → Val, ∀ p ∈ F, SatisfiesFd (applyV ν '' T) p.1 p.2

/-- **Definition 6.6** (§6.3), hard violation: two rows agree on `X` but carry *different constants*
on `A` — no valuation can repair this, since constants are fixed. -/
def HardViolation (T : VTable Ω Val Var) (X : Finset Att) (a : {x : Att // x ∈ Ω}) : Prop :=
  ∃ t₁ ∈ T, ∃ t₂ ∈ T, VAgree X t₁ t₂ ∧
    ∃ v₁ v₂ : Val, t₁ a = Sum.inl v₁ ∧ t₂ a = Sum.inl v₂ ∧ v₁ ≠ v₂

/-- **Definition 6.6** (§6.3), soft violation: two rows agree on `X` and differ on `A`, but at least
one `A`-entry is a variable — repairable by filling in the nulls. -/
def SoftViolation (T : VTable Ω Val Var) (X : Finset Att) (a : {x : Att // x ∈ Ω}) : Prop :=
  ∃ t₁ ∈ T, ∃ t₂ ∈ T, VAgree X t₁ t₂ ∧ t₁ a ≠ t₂ a ∧ ((t₁ a).isRight ∨ (t₂ a).isRight)

/-- **Theorem 6.9** (§6.3, forward direction): a hard violation of a required fd blocks
permissibility — no completion can satisfy `X → {A}` when two rows agreeing on `X` hold distinct
constants on `A`. -/
theorem not_isPermissible_of_hardViolation {T : VTable Ω Val Var}
    {F : Set (Finset Att × Finset Att)} {X : Finset Att} {a : {x : Att // x ∈ Ω}}
    (hfd : (X, ({a.val} : Finset Att)) ∈ F) (hv : HardViolation T X a) : ¬ IsPermissible T F := by
  rintro ⟨ν, hF⟩
  obtain ⟨t₁, h1, t₂, h2, hag, v₁, v₂, hv1, hv2, hne⟩ := hv
  have hsat := hF (X, {a.val}) hfd
  have hA := hsat (applyV ν t₁) ⟨t₁, h1, rfl⟩ (applyV ν t₂) ⟨t₂, h2, rfl⟩
    (applyV_agree_of_vAgree hag ν) a (Finset.mem_singleton_self a.val)
  simp only [applyV_apply, hv1, hv2, evalEntry_const] at hA
  exact hne hA

end DeepWiki
