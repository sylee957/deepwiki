import DeepWiki.ReactiveSystems.HmlRecursion
import DeepWiki.ReactiveSystems.HmlRecursionSystems
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Set.Insert

/-! # HML-with-recursion fixed-point computations
Concrete evaluations of the semantic functional `O_F = denotR` and of
`LivelockNow` (greatest solution of `X =ν ⟨τ⟩X`) on small LTSs. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-! ## Evaluating `O_{[b]ff ∧ [a]X}({p₂})` -/

/-- Actions `a`/`b`. -/
inductive Lab62 | a | b
  deriving DecidableEq, Fintype

/-- States of the three-state LTS. -/
inductive S62 | p1 | p2 | p3
  deriving DecidableEq, Fintype

/-- Edges: `p₁ —a→ p₂`, `p₁ —b→ p₃`, `p₃ —a→ p₁`, `p₃ —a→ p₂`; `p₂` dead. -/
def edge62 : S62 → Lab62 → S62 → Bool
  | .p1, .a, .p2 => true
  | .p1, .b, .p3 => true
  | .p3, .a, .p1 => true
  | .p3, .a, .p2 => true
  | _, _, _ => false

/-- The three-state LTS (reducible for decidability). -/
abbrev L62 : LTS S62 Lab62 := ⟨fun p x q => edge62 p x q = true⟩

/-- `O_{[b]ff ∧ [a]X}({p₂}) = {p₂}`: a single
evaluation of the semantic functional (no fixed point). -/
theorem denotR_L62_singleton :
    denotR L62 (HMLR.and (HMLR.box .b HMLR.ff) (HMLR.box .a HMLR.var)) {S62.p2}
      = {S62.p2} := by
  ext x
  cases x <;>
    simp only [denotR, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff,
      Set.mem_empty_iff_false] <;>
    decide

/-! ## Least solution `Y =μ ⟨b⟩tt ∨ ⟨{a,b}⟩Y` is everything -/

/-- States of the LTS. -/
inductive S66 | s | s1 | s2 | t | t1
  deriving DecidableEq

/-- Transitions: `s —a→ s₁/s₂`, `t —a→ s₂/t₁`, `s₁ —b→ s₂`, `s₂ —b→ s₂`,
`t₁ —b→ t₁`. -/
inductive Step66 : S66 → Lab62 → S66 → Prop
  | sa1 : Step66 .s .a .s1
  | sa2 : Step66 .s .a .s2
  | ta2 : Step66 .t .a .s2
  | tt1 : Step66 .t .a .t1
  | s1b : Step66 .s1 .b .s2
  | s2b : Step66 .s2 .b .s2
  | t1b : Step66 .t1 .b .t1

/-- The LTS. -/
def L66 : LTS S66 Lab62 := ⟨Step66⟩

/-- `Y =μ ⟨b⟩tt ∨ ⟨{a,b}⟩Y` (with `⟨{a,b}⟩Y = ⟨a⟩Y ∨ ⟨b⟩Y`). -/
def FY66 : HMLR Lab62 := .or (.dia .b .tt) (.or (.dia .a .var) (.dia .b .var))

/-- The least solution of `Y =μ ⟨b⟩tt ∨ ⟨{a,b}⟩Y`
is the whole state space: every state can reach (via `a`/`b`) a `b`-looping state. -/
theorem lfp_FY66_univ : recMin L66 FY66 = Set.univ := by
  apply le_antisymm (Set.subset_univ _)
  refine (denotRHom L66 FY66).le_lfp ?_
  intro S hS x _
  have hs2 : S66.s2 ∈ S := hS (Or.inl ⟨.s2, Step66.s2b, trivial⟩)
  cases x with
  | s2 => exact hs2
  | s1 => exact hS (Or.inl ⟨.s2, Step66.s1b, trivial⟩)
  | t1 => exact hS (Or.inl ⟨.t1, Step66.t1b, trivial⟩)
  | s => exact hS (Or.inr (Or.inl ⟨.s2, Step66.sa2, hs2⟩))
  | t => exact hS (Or.inr (Or.inl ⟨.s2, Step66.ta2, hs2⟩))

/-! ## recMax / recMin / livelock on one LTS -/

/-- States of the LTS. -/
inductive S67 | s | s1 | s2 | t | t1
  deriving DecidableEq

/-- Transitions: `s —a→ s₁`, `s₁ —b→ s₂`, `s₂ —b→ s₁` (a `b`-loop), `t —a→ t₁`,
`t₁ —a→ t₁` (an `a`-loop with no `b`). -/
inductive Step67 : S67 → Lab62 → S67 → Prop
  | sa1 : Step67 .s .a .s1
  | s1b : Step67 .s1 .b .s2
  | s2b : Step67 .s2 .b .s1
  | ta1 : Step67 .t .a .t1
  | t1a : Step67 .t1 .a .t1

/-- The LTS. -/
def L67 : LTS S67 Lab62 := ⟨Step67⟩

/-- `X =ν ⟨b⟩tt ∧ [b]X`. -/
def F67 : HMLR Lab62 := .and (.dia .b .tt) (.box .b .var)

/-- `Y =μ ⟨b⟩tt ∨ ⟨{a,b}⟩Y`. -/
def FY67 : HMLR Lab62 := .or (.dia .b .tt) (.or (.dia .a .var) (.dia .b .var))

/-- `s₁ ⊨ X =ν ⟨b⟩tt ∧ [b]X`: `{s₁, s₂}` is a
post-fixed point (each has a `b`-move staying inside). -/
theorem s1_mem_gfp_F67 : S67.s1 ∈ recMax L67 F67 := by
  have h : ({S67.s1, S67.s2} : Set S67) ≤ recMax L67 F67 := by
    refine (denotRHom L67 F67).le_gfp ?_
    intro x hx
    rcases (show x = .s1 ∨ x = .s2 by simpa using hx) with rfl | rfl
    · exact ⟨⟨.s2, Step67.s1b, trivial⟩, by intro p' hstep; cases hstep; simp [denotR]⟩
    · exact ⟨⟨.s1, Step67.s2b, trivial⟩, by intro p' hstep; cases hstep; simp [denotR]⟩
  exact h (show S67.s1 ∈ ({S67.s1, S67.s2} : Set S67) by simp)

/-- For `Y =μ ⟨b⟩tt ∨ ⟨{a,b}⟩Y`: `s ⊨ Y` (it reaches a
`b`-state) but `t ⊭ Y` (the `t`-component has no `b`-move). -/
theorem s_mem_lfp_FY67_and_t_nmem : S67.s ∈ recMin L67 FY67 ∧ S67.t ∉ recMin L67 FY67 := by
  have hfix : denotR L67 FY67 (recMin L67 FY67) = recMin L67 FY67 :=
    OrderHom.map_lfp (denotRHom L67 FY67)
  refine ⟨?_, ?_⟩
  · have hs1 : S67.s1 ∈ recMin L67 FY67 := hfix ▸ (Or.inl ⟨.s2, Step67.s1b, trivial⟩)
    exact hfix ▸ (Or.inr (Or.inl ⟨.s1, Step67.sa1, hs1⟩))
  · intro ht
    have hsub : recMin L67 FY67 ⊆ ({S67.s, S67.s1, S67.s2} : Set S67) :=
      (denotRHom L67 FY67).lfp_le (by
        intro x hx
        cases x with
        | s => simp
        | s1 => simp
        | s2 => simp
        | t =>
            rcases hx with ⟨_, hs, _⟩ | ⟨_, hs, hm⟩ | ⟨_, hs, _⟩
            · cases hs
            · cases hs; simp [denotR] at hm
            · cases hs
        | t1 =>
            rcases hx with ⟨_, hs, _⟩ | ⟨_, hs, hm⟩ | ⟨_, hs, _⟩
            · cases hs
            · cases hs; simp [denotR] at hm
            · cases hs)
    have := hsub ht
    simp at this

/-- `t` is livelocked on `a`: `t ⊨ Z =ν ⟨a⟩Z`. -/
theorem t_livelocked_L67_a : S67.t ∈ LivelockNow L67 .a :=
  (livelockFun L67 .a).le_gfp (a := {S67.t, S67.t1}) (by
    intro x hx
    rcases (show x = .t ∨ x = .t1 by simpa using hx) with rfl | rfl
    · exact ⟨.t1, Step67.ta1, by simp⟩
    · exact ⟨.t1, Step67.t1a, by simp⟩)
    (by simp)

/-! ## Largest solution of an equational system -/

/-- The two variables `X, Y` of the equational system. -/
inductive V69 | X | Y
  deriving DecidableEq

/-- States of the LTS. -/
inductive P69 | p | q | r
  deriving DecidableEq

/-- Transitions (single action): `p —a→ p`, `p —a→ q`, `q —a→ r`; `r` dead. -/
inductive Step69 : P69 → Unit → P69 → Prop
  | pp : Step69 .p () .p
  | pq : Step69 .p () .q
  | qr : Step69 .q () .r

/-- The LTS. -/
def L69 : LTS P69 Unit := ⟨Step69⟩

/-- The system `X =ν [a]Y`, `Y =ν ⟨a⟩X`. -/
def D69 : V69 → HMLV V69 Unit
  | .X => .box () (.var .Y)
  | .Y => .dia () (.var .X)

/-- The claimed largest solution: `X ↦ {p, r}`, `Y ↦ {p, q}`. -/
def sol69 : V69 → Set P69
  | .X => {P69.p, P69.r}
  | .Y => {P69.p, P69.q}

/-- The largest solution of `X =ν [a]Y`,
`Y =ν ⟨a⟩X` over the 3-state LTS is `X = {p, r}`, `Y = {p, q}`. -/
theorem sysMax_D69_eq_sol69 : sysMax L69 D69 = sol69 := by
  apply le_antisymm
  · -- sysMax ≤ sol69, by coinduction: any post-fixed point is ≤ sol69
    have key : ∀ σ : V69 → Set P69, σ ≤ sysFun L69 D69 σ → σ ≤ sol69 := by
      intro σ hσ
      have hY : σ .Y ⊆ ({P69.p, P69.q} : Set P69) := by
        intro x hx
        obtain ⟨x', hstep, _⟩ := hσ .Y hx
        cases x with
        | p => simp
        | q => simp
        | r => cases hstep
      intro v x hx
      cases v with
      | Y => exact hY hx
      | X =>
          have hbox := hσ .X hx
          cases x with
          | p => simp [sol69]
          | r => simp [sol69]
          | q => exact absurd (hY (hbox P69.r Step69.qr)) (by simp)
    exact key _ (OrderHom.map_gfp (sysFun L69 D69)).ge
  · -- sol69 ≤ sysMax, since sol69 is a post-fixed point
    refine (sysFun L69 D69).le_gfp ?_
    intro v x hx
    cases v with
    | X =>
        -- x ∈ {p,r} ⊆ denotV sol69 (box () (var Y)) = {x | ∀ a-succ ∈ {p,q}}
        intro p' hstep
        cases x with
        | p => cases hstep <;> simp [denotV, sol69]
        | r => cases hstep
        | q => simp [sol69] at hx
    | Y =>
        -- x ∈ {p,q} ⊆ denotV sol69 (dia () (var X)) = {x | ∃ a-succ ∈ {p,r}}
        cases x with
        | p => exact ⟨.p, Step69.pp, by simp [denotV, sol69]⟩
        | q => exact ⟨.r, Step69.qr, by simp [denotV, sol69]⟩
        | r => simp [sol69] at hx

/-! ## LivelockNow computations -/

/-- Actions for the livelock examples. -/
inductive Act6 | a | tau
  deriving DecidableEq

/-! ## Only the `τ`-self-loop state is livelocked -/

/-- States of the LTS. -/
inductive S616 | s | p | q | r
  deriving DecidableEq

/-- Transitions: `s —a→ p`, `p —τ→ p` (self-loop), `p —τ→ q`, `q —τ→ r`; `r` dead. -/
inductive Step616 : S616 → Act6 → S616 → Prop
  | sa : Step616 .s .a .p
  | pτp : Step616 .p .tau .p
  | pτq : Step616 .p .tau .q
  | qτr : Step616 .q .tau .r

/-- The LTS. -/
def L616 : LTS S616 Act6 := ⟨Step616⟩

/-- The only livelocked state is `p`:
`LivelockNow = {p}`. -/
theorem livelockNow_L616_tau_singleton : LivelockNow L616 .tau = {S616.p} := by
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

/-! ## Every state is livelocked -/

/-- States of the LTS. -/
inductive S617 | s | s1 | s2 | s3
  deriving DecidableEq

/-- Transitions: `s ⇄ s₁` (a `τ`-2-cycle), `s₂ —a→ s₁`, `s₂ —τ→ s₃`, `s₃ —τ→ s₃`. -/
inductive Step617 : S617 → Act6 → S617 → Prop
  | sτs1 : Step617 .s .tau .s1
  | s1τs : Step617 .s1 .tau .s
  | s2a : Step617 .s2 .a .s1
  | s2τs3 : Step617 .s2 .tau .s3
  | s3τs3 : Step617 .s3 .tau .s3

/-- The LTS. -/
def L617 : LTS S617 Act6 := ⟨Step617⟩

/-- Every state has an outgoing `τ`, so every state
is livelocked: `LivelockNow = univ`. -/
theorem livelockNow_L617_tau_univ : LivelockNow L617 .tau = Set.univ := by
  apply le_antisymm (Set.subset_univ _)
  exact (livelockFun L617 .tau).le_gfp (by
    intro x _
    cases x with
    | s => exact ⟨.s1, Step617.sτs1, trivial⟩
    | s1 => exact ⟨.s, Step617.s1τs, trivial⟩
    | s2 => exact ⟨.s3, Step617.s2τs3, trivial⟩
    | s3 => exact ⟨.s3, Step617.s3τs3, trivial⟩)

end DeepWiki.ReactiveSystems
