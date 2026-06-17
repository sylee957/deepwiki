import DeepWiki.ReactiveSystems.HmlRecursionSystems

/-! # LivelockNow computations (Exercises 6.16, 6.17)
Two concrete `LivelockNow` (greatest solution of `X =ν ⟨τ⟩X`) computations: a
4-state LTS where only `p` (a `τ`-self-loop) is livelocked (Ex 6.16), and one where
every state has an outgoing `τ`, so all are livelocked (Ex 6.17). -/

namespace DeepWiki.ReactiveSystems

open LTS

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
