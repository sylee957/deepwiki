import Book.Servers
import Mathlib.Logic.Relation

/-! # Concatenation of servers
The concatenation of two servers — the output of the first feeds the
second — is relation composition `Relation.Comp`, and is again a server:
causality composes through the intermediate curve (`C ≤ B ≤ A`) and
left-totality chains the output witnesses. Iterated self-concatenation is
`compPow`, with the identity relation as the zeroth power. -/

namespace DeepWiki

/-- Causality composes: the concatenation of causal relations is causal,
`C ≤ B ≤ A` through the intermediate output. -/
theorem IsCausal.comp {S₁ S₂ : Curve → Curve → Prop}
    (h₁ : IsCausal S₁) (h₂ : IsCausal S₂) :
    IsCausal (Relation.Comp S₁ S₂) := by
  rintro A C ⟨B, hAB, hBC⟩
  exact fun t => le_trans (h₂ B C hBC t) (h₁ A B hAB t)

/-- Left-totality composes: chain the two output witnesses. -/
theorem IsLeftTotal.comp {S₁ S₂ : Curve → Curve → Prop}
    (h₁ : IsLeftTotal S₁) (h₂ : IsLeftTotal S₂) :
    IsLeftTotal (Relation.Comp S₁ S₂) := fun A =>
  let ⟨B, hB⟩ := h₁ A
  let ⟨C, hC⟩ := h₂ B
  ⟨C, B, hB, hC⟩

/-- **The concatenation of two servers is a server.** The book's `S₂ ∘ S₁`
(feed `S₁`'s output to `S₂`) is `Relation.Comp S₁ S₂`. -/
theorem IsServer.comp {S₁ S₂ : Curve → Curve → Prop}
    (h₁ : IsServer S₁) (h₂ : IsServer S₂) :
    IsServer (Relation.Comp S₁ S₂) :=
  ⟨h₁.1.comp h₂.1, h₁.2.comp h₂.2⟩

/-- The identity relation is a server: every curve serves itself. -/
theorem isServer_eq : IsServer (· = · : Curve → Curve → Prop) := by
  refine ⟨fun A D h => ?_, fun A => ⟨A, rfl⟩⟩
  subst h
  exact fun _ => le_rfl

/-- Iterated self-composition of a relation: `compPow r 0` is the identity
relation and `compPow r (n + 1) = Relation.Comp (compPow r n) r`. -/
def compPow {α : Type*} (r : α → α → Prop) : ℕ → α → α → Prop
  | 0 => (· = ·)
  | n + 1 => Relation.Comp (compPow r n) r

/-- `compPow r 0` is the identity relation. -/
theorem compPow_zero {α : Type*} (r : α → α → Prop) :
    compPow r 0 = (· = ·) :=
  rfl

/-- `compPow r (n + 1)` composes one more copy of `r` on the output
side. -/
theorem compPow_succ {α : Type*} (r : α → α → Prop) (n : ℕ) :
    compPow r (n + 1) = Relation.Comp (compPow r n) r :=
  rfl

/-- The first power is the relation itself. -/
theorem compPow_one {α : Type*} (r : α → α → Prop) :
    compPow r 1 = r := by
  rw [compPow_succ, compPow_zero, Relation.eq_comp]

/-- Every power of a server is a server (`n`-fold self-concatenation; the
zeroth power is the identity server). -/
theorem IsServer.compPow {S : Curve → Curve → Prop} (h : IsServer S) :
    ∀ n, IsServer (compPow S n)
  | 0 => isServer_eq
  | n + 1 => (h.compPow n).comp h

/-! ## Book restatement (concatenation of servers)
`S₂ ∘ S₁ = {(A, C) | ∃ B ∈ 𝒞, (A, B) ∈ S₁ ∧ (B, C) ∈ S₂}` is
`Relation.Comp S₁ S₂`, with `S⁰ = {(A, A) | A ∈ 𝒞}` and `Sⁿ⁺¹ = S ∘ Sⁿ`
as `compPow`; if `S₁` and `S₂` are two servers, then so is `S₂ ∘ S₁`. -/
example (S₁ S₂ : Curve → Curve → Prop) (A C : Curve) :
    Relation.Comp S₁ S₂ A C ↔ ∃ B : Curve, S₁ A B ∧ S₂ B C :=
  Iff.rfl

example {S₁ S₂ : Curve → Curve → Prop}
    (h₁ : IsServer S₁) (h₂ : IsServer S₂) :
    IsServer (Relation.Comp S₁ S₂) :=
  h₁.comp h₂

example (S : Curve → Curve → Prop) (A A' : Curve) :
    (compPow S 0 A A' ↔ A = A') ∧
      ∀ n, compPow S (n + 1) = Relation.Comp (compPow S n) S :=
  ⟨Iff.rfl, fun _ => rfl⟩

end DeepWiki
