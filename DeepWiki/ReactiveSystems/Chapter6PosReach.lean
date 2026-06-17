import DeepWiki.ReactiveSystems.Chapter6Examples
import Mathlib.Order.FixedPoints

/-! # Exercise 6.18 — reachability of a livelock via the `Pos` template
`Pos(F) =μ F ∨ ⟨Act⟩Pos(F)` describes the states from which a state satisfying `F`
is reachable. Per the stratified reading of (6.17) (solve the `ν`-block
`LivelockNow` first, then the `μ`-block `Pos` over it as a constant), the formula
`F = ⟨Act⟩Pos(LivelockNow)` over the Exercise 6.17 LTS denotes the whole state
space: every state is livelocked (Exercise 6.17) and every state can move, so a
livelock is reachable from everywhere. -/

namespace DeepWiki.ReactiveSystems

open LTS

variable {Proc Act : Type*}

/-- The `⟨Act⟩` modality: states with an outgoing transition into `X`. -/
def diaAll (L : LTS Proc Act) (X : Set Proc) : Set Proc :=
  {p | ∃ a p', L.step p a p' ∧ p' ∈ X}

theorem diaAll_mono (L : LTS Proc Act) : Monotone (diaAll L) :=
  fun _ _ h _ hp => let ⟨a, p', hs, hp'⟩ := hp; ⟨a, p', hs, h hp'⟩

/-- The `Pos` functional `X ↦ S ∪ ⟨Act⟩X` whose least fixed point is `Pos(F)` with
`⟦F⟧ = S`. -/
def posFun (L : LTS Proc Act) (S : Set Proc) : Set Proc →o Set Proc where
  toFun X := S ∪ diaAll L X
  monotone' _ _ h := Set.union_subset_union_right S (diaAll_mono L h)

/-- `Pos(F)` (with `⟦F⟧ = S`): the least solution of `X =μ S ∨ ⟨Act⟩X` — the states
from which `S` is reachable. -/
def posOf (L : LTS Proc Act) (S : Set Proc) : Set Proc := OrderHom.lfp (posFun L S)

/-- `S ⊆ Pos(F)`: a state satisfying `F` reaches `F` in zero steps. -/
theorem subset_posOf (L : LTS Proc Act) (S : Set Proc) : S ⊆ posOf L S := by
  have h : posFun L S (posOf L S) = posOf L S := OrderHom.map_lfp (posFun L S)
  rw [← h]
  exact Set.subset_union_left

/-- **Exercise 6.18** (§6.7, p.138). On the Exercise 6.17 LTS, the set of states
satisfying `⟨Act⟩Pos(LivelockNow)` is the whole state space: every state is
livelocked (`ex_6_17`), so `Pos(LivelockNow) = univ`, and every state can move, so
prefixing with `⟨Act⟩` keeps it `univ`. -/
theorem ex_6_18 :
    diaAll L617 (posOf L617 (LivelockNow L617 Act6.tau)) = Set.univ := by
  have hpos : posOf L617 (LivelockNow L617 Act6.tau) = Set.univ := by
    apply le_antisymm (Set.subset_univ _)
    rw [ex_6_17]
    exact subset_posOf L617 Set.univ
  rw [hpos]
  refine le_antisymm (Set.subset_univ _) (fun p _ => ?_)
  cases p with
  | s => exact ⟨Act6.tau, S617.s1, Step617.sτs1, trivial⟩
  | s1 => exact ⟨Act6.tau, S617.s, Step617.s1τs, trivial⟩
  | s2 => exact ⟨Act6.a, S617.s1, Step617.s2a, trivial⟩
  | s3 => exact ⟨Act6.tau, S617.s3, Step617.s3τs3, trivial⟩

end DeepWiki.ReactiveSystems
