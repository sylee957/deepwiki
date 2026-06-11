import Book.Servers
import Book.ServiceCurveMaximal
import Book.CurveDioidEReal
import Mathlib.Logic.Relation

/-! # Concatenation of servers
The concatenation of two servers — the output of the first feeds the
second — is relation composition `Relation.Comp`, and is again a server:
causality composes through the intermediate curve (`C ≤ B ≤ A`) and
left-totality chains the output witnesses. Iterated self-concatenation is
`compPow`, with the identity relation as the zeroth power. A flow crossing
two servers offering min-plus (or maximal) service curves `β₁`, `β₂` is
globally offered `β₁ ∗ β₂`. -/

namespace DeepWiki

open scoped Classical NNReal

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

/-! ## Concatenation of servers in a convolution
Composing the two offers through the intermediate curve by isotony, then
reassociating the convolution onto the input. `BddBelowReal` keeps the
`EReal` convolution associative (no `(+∞) + (−∞)` collision; the book's
curves are nonnegative, hence bounded below). -/

/-- `curveE A` is bounded below by a real (curves are nonnegative). -/
theorem bddBelowReal_curveE (A : Curve) : BddBelowReal (curveE A) :=
  (isNonneg_liftEReal ⇑A).bddBelowReal

/-- **Concatenated servers offer the convolution of their min-plus service
curves**: if `S₁` offers `β₁` and `S₂` offers `β₂`, the concatenation
`Relation.Comp S₁ S₂` offers `β₁ ∗ β₂` (bounded-below curves). -/
theorem IsMinimalServiceCurve.comp {S₁ S₂ : Curve → Curve → Prop}
    {β₁ β₂ : ℝ≥0 → EReal}
    (h₁ : IsMinimalServiceCurve β₁ S₁) (h₂ : IsMinimalServiceCurve β₂ S₂)
    (hb₁ : BddBelowReal β₁) (hb₂ : BddBelowReal β₂) :
    IsMinimalServiceCurve (minConv β₁ β₂) (Relation.Comp S₁ S₂) := by
  rintro A C ⟨B, hAB, hBC⟩
  calc minConv (curveE A) (minConv β₁ β₂)
      = minConv (minConv (curveE A) β₁) β₂ :=
        (minConv_assoc (bddBelowReal_curveE A) hb₁ hb₂).symm
    _ ≤ minConv (curveE B) β₂ := fun t =>
        minConv_le_minConv (h₁ A B hAB) (fun _ => le_rfl) t
    _ ≤ curveE C := h₂ B C hBC

/-- The largest-relation form of the concatenation theorem:
`Smp(β₂) ∘ Smp(β₁) ⊆ Smp(β₁ ∗ β₂)`. -/
theorem comp_minimalServiceRel_le {β₁ β₂ : ℝ≥0 → EReal}
    (hb₁ : BddBelowReal β₁) (hb₂ : BddBelowReal β₂) :
    Relation.Comp (minimalServiceRel β₁) (minimalServiceRel β₂)
      ≤ minimalServiceRel (minConv β₁ β₂) := by
  rintro A C ⟨B, hAB, hBC⟩
  exact ⟨le_trans hBC.1 hAB.1,
    ((isMinimalServiceCurve_minimalServiceRel β₁).comp
        (isMinimalServiceCurve_minimalServiceRel β₂) hb₁ hb₂)
      A C ⟨B, hAB, hBC⟩⟩

/-- The same holds for maximal service curves: the concatenation offers
the convolution, `D ≤ A ∗ β` composing through the intermediate output. -/
theorem IsMaximalServiceCurve.comp {S₁ S₂ : Curve → Curve → Prop}
    {β₁ β₂ : ℝ≥0 → EReal}
    (h₁ : IsMaximalServiceCurve β₁ S₁) (h₂ : IsMaximalServiceCurve β₂ S₂)
    (hb₁ : BddBelowReal β₁) (hb₂ : BddBelowReal β₂) :
    IsMaximalServiceCurve (minConv β₁ β₂) (Relation.Comp S₁ S₂) := by
  rintro A C ⟨B, hAB, hBC⟩
  calc curveE C
      ≤ minConv (curveE B) β₂ := h₂ B C hBC
    _ ≤ minConv (minConv (curveE A) β₁) β₂ := fun t =>
        minConv_le_minConv (h₁ A B hAB) (fun _ => le_rfl) t
    _ = minConv (curveE A) (minConv β₁ β₂) :=
        minConv_assoc (bddBelowReal_curveE A) hb₁ hb₂

/-- The largest-relation form for maximal service curves:
`Smax(β₂) ∘ Smax(β₁) ⊆ Smax(β₁ ∗ β₂)`. -/
theorem comp_maximalServiceRel_le {β₁ β₂ : ℝ≥0 → EReal}
    (hb₁ : BddBelowReal β₁) (hb₂ : BddBelowReal β₂) :
    Relation.Comp (maximalServiceRel β₁) (maximalServiceRel β₂)
      ≤ maximalServiceRel (minConv β₁ β₂) :=
  (isMaximalServiceCurve_maximalServiceRel β₁).comp
    (isMaximalServiceCurve_maximalServiceRel β₂) hb₁ hb₂

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

/-! ## Book restatement (concatenation of servers in a convolution)
A flow crossing two servers respectively offering min-plus service curves
`β₁` and `β₂` is globally offered a min-plus service curve `β₁ ∗ β₂`:
`Smp(β₂) ∘ Smp(β₁) ⊆ Smp(β₁ ∗ β₂)`, and the same holds for maximal
service curves: `Smax(β₂) ∘ Smax(β₁) ⊆ Smax(β₁ ∗ β₂)`. The convolution
is commutative but the composition is not — the inclusions can be strict,
so the convolution does not exactly model the composition. -/
example {β₁ β₂ : ℝ≥0 → EReal}
    (hb₁ : BddBelowReal β₁) (hb₂ : BddBelowReal β₂) :
    Relation.Comp (minimalServiceRel β₁) (minimalServiceRel β₂)
        ≤ minimalServiceRel (minConv β₁ β₂) ∧
      Relation.Comp (maximalServiceRel β₁) (maximalServiceRel β₂)
        ≤ maximalServiceRel (minConv β₁ β₂) :=
  ⟨comp_minimalServiceRel_le hb₁ hb₂, comp_maximalServiceRel_le hb₁ hb₂⟩

end DeepWiki
