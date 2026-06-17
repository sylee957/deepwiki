import DeepWiki.ReactiveSystems.HmlRecursion
import DeepWiki.ReactiveSystems.HmlRecursionSystems
import Mathlib.Tactic.DeriveFintype

/-! # HML-with-recursion computations (Exercises 6.4, 6.16, 6.17)
Concrete evaluations of the semantic functional `O_F = denotR` and of
`LivelockNow` (greatest solution of `X =ν ⟨τ⟩X`) on small LTSs. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-! ## Exercise 6.4 — evaluating `O_{[b]ff ∧ [a]X}({p₂})` -/

/-- Actions `a`/`b` for Exercise 6.4. -/
inductive Lab62 | a | b
  deriving DecidableEq, Fintype

/-- States of the Figure 6.2 LTS. -/
inductive S62 | p1 | p2 | p3
  deriving DecidableEq, Fintype

/-- Figure 6.2 edges: `p₁ —a→ p₂`, `p₁ —b→ p₃`, `p₃ —a→ p₁`, `p₃ —a→ p₂`; `p₂` dead. -/
def edge62 : S62 → Lab62 → S62 → Bool
  | .p1, .a, .p2 => true
  | .p1, .b, .p3 => true
  | .p3, .a, .p1 => true
  | .p3, .a, .p2 => true
  | _, _, _ => false

/-- The Figure 6.2 LTS (reducible for decidability). -/
abbrev L62 : LTS S62 Lab62 := ⟨fun p x q => edge62 p x q = true⟩

/-- **Exercise 6.4** (§6.2, p.110). `O_{[b]ff ∧ [a]X}({p₂}) = {p₂}`: a single
evaluation of the semantic functional (no fixed point). -/
theorem ex_6_4 :
    denotR L62 (HMLR.and (HMLR.box .b HMLR.ff) (HMLR.box .a HMLR.var)) {S62.p2}
      = {S62.p2} := by
  ext x
  cases x <;>
    simp only [denotR, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff,
      Set.mem_empty_iff_false] <;>
    decide

/-! ## Exercises 6.16/6.17 — LivelockNow computations -/

/-- Actions for the livelock examples. -/
inductive Act6 | a | tau
  deriving DecidableEq

/-! ## Exercise 6.16 — only the `τ`-self-loop state is livelocked -/

/-- States of the Exercise 6.16 LTS. -/
inductive S616 | s | p | q | r
  deriving DecidableEq

/-- Transitions: `s —a→ p`, `p —τ→ p` (self-loop), `p —τ→ q`, `q —τ→ r`; `r` dead. -/
inductive Step616 : S616 → Act6 → S616 → Prop
  | sa : Step616 .s .a .p
  | pτp : Step616 .p .tau .p
  | pτq : Step616 .p .tau .q
  | qτr : Step616 .q .tau .r

/-- The Exercise 6.16 LTS. -/
def L616 : LTS S616 Act6 := ⟨Step616⟩

/-- **Exercise 6.16** (§6.7, p.135). The only livelocked state is `p`:
`LivelockNow = {p}`. -/
theorem ex_6_16 : LivelockNow L616 .tau = {S616.p} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨x', hstep, hx'⟩ := (OrderHom.map_gfp (livelockFun L616 .tau)).ge hx
    cases x with
    | p => rfl
    | s => cases hstep
    | r => cases hstep
    | q =>
        cases hstep
        obtain ⟨_, hr, _⟩ := (OrderHom.map_gfp (livelockFun L616 .tau)).ge hx'
        cases hr
  · exact (livelockFun L616 .tau).le_gfp (by
      intro y hy; cases hy; exact ⟨.p, Step616.pτp, rfl⟩)

/-! ## Exercise 6.17 — every state is livelocked -/

/-- States of the Exercise 6.17 LTS. -/
inductive S617 | s | s1 | s2 | s3
  deriving DecidableEq

/-- Transitions: `s ⇄ s₁` (a `τ`-2-cycle), `s₂ —a→ s₁`, `s₂ —τ→ s₃`, `s₃ —τ→ s₃`. -/
inductive Step617 : S617 → Act6 → S617 → Prop
  | sτs1 : Step617 .s .tau .s1
  | s1τs : Step617 .s1 .tau .s
  | s2a : Step617 .s2 .a .s1
  | s2τs3 : Step617 .s2 .tau .s3
  | s3τs3 : Step617 .s3 .tau .s3

/-- The Exercise 6.17 LTS. -/
def L617 : LTS S617 Act6 := ⟨Step617⟩

/-- **Exercise 6.17** (§6.7, p.135). Every state has an outgoing `τ`, so every state
is livelocked: `LivelockNow = univ`. -/
theorem ex_6_17 : LivelockNow L617 .tau = Set.univ := by
  apply le_antisymm (Set.subset_univ _)
  exact (livelockFun L617 .tau).le_gfp (by
    intro x _
    cases x with
    | s => exact ⟨.s1, Step617.sτs1, trivial⟩
    | s1 => exact ⟨.s, Step617.s1τs, trivial⟩
    | s2 => exact ⟨.s3, Step617.s2τs3, trivial⟩
    | s3 => exact ⟨.s3, Step617.s3τs3, trivial⟩)

end DeepWiki.ReactiveSystems
