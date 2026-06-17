import DeepWiki.ReactiveSystems.HmlRecursion
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Set.Insert

/-! # The recursive safety property `F =ν [a]ff ∧ [b]F`
The LTS `p ↺b`, `q —b→ p`, `q —b→ r`, `q —a→ s`, `r ↺b`, `s` dead. The greatest
solution of `F =ν [a]ff ∧ [b]F` (no `a` is reachable along any `b`-path) is
`{p, r, s}`: only `q` can perform `a`. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- Actions `a`/`b` for the recursive-safety LTS. -/
inductive Lab713 | a | b
  deriving DecidableEq, Fintype

/-- States of the recursive-safety LTS. -/
inductive S713 | p | q | r | s
  deriving DecidableEq, Fintype

/-- Edges: `p —b→ p`, `q —b→ p`, `q —b→ r`, `q —a→ s`, `r —b→ r`; `s` dead. -/
def edge713 : S713 → Lab713 → S713 → Bool
  | .p, .b, .p => true
  | .q, .b, .p => true
  | .q, .b, .r => true
  | .q, .a, .s => true
  | .r, .b, .r => true
  | _, _, _ => false

/-- The recursive-safety LTS (reducible, so step facts are decidable). -/
abbrev L713 : LTS S713 Lab713 := ⟨fun u y v => edge713 u y v = true⟩

/-- `F =ν [a]ff ∧ [b]F`: no `a` now, and the property persists through every `b`. -/
def F713 : HMLR Lab713 := .and (.box .a .ff) (.box .b .var)

/-- The set of states satisfying the recursive
safety property `F =ν [a]ff ∧ [b]F` is `{p, r, s}`: `q` is excluded because
`q —a→ s`, while `p`, `r`, `s` reach no `a` along any `b`-path. (The companion
question — which states pass the test `X ≝ ā.bad.0 + b̄.X` — has the same answer
`{p, r, s}` by the testing characterization.) -/
theorem safeStates_L713_eq : recMax L713 F713 = {S713.p, S713.r, S713.s} := by
  -- `{p, r, s}` is a fixed point of the denotation functional `denotR F`.
  have hcomp : denotR L713 F713 {S713.p, S713.r, S713.s} = {S713.p, S713.r, S713.s} := by
    ext x
    cases x <;>
      simp only [F713, denotR, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff,
        Set.mem_insert_iff, Set.mem_empty_iff_false] <;>
      decide
  apply le_antisymm
  · -- recMax ⊆ {p, r, s}: only q is excluded, since q —a→ s breaks `[a]ff`.
    intro x hx
    cases x with
    | p => simp
    | r => simp
    | s => simp
    | q =>
        have hfix : S713.q ∈ denotR L713 F713 (recMax L713 F713) :=
          (OrderHom.map_gfp (denotRHom L713 F713)).ge hx
        exact (hfix.1 S713.s (by decide)).elim
  · -- {p, r, s} ≤ recMax: being a fixed point, it is a post-fixed point.
    exact (denotRHom L713 F713).le_gfp hcomp.ge

end DeepWiki.ReactiveSystems
