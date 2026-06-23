import DeepWiki.NetworkCalculus.NetworkTopology
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! # A four-server cyclic network and its feed-forward transformation
The worked feed-forward transformation of the four-server toy network (servers
`1,2,3,4`, four flows). The flow routing has a cyclic dependency graph, so no
server ranking makes every flow path strictly increasing
(`fourServerNetwork_not_feedForward`): the network is genuinely cyclic. Removing
two arcs by *splitting* the offending flows into sub-flows (the *turn
prohibition* / feed-forward transformation) yields an acyclic sub-flow routing
that **is** feed-forward (`feedForwardTransform_isFeedForward`), under the rank
`1,2 ↦ 0`, `3 ↦ 1`, `4 ↦ 2`.

Flow paths (server lists). Flows `1,2,3` are determined by the splits at the two
removed arcs `(4,2)` and `(2,1)`; flow `4` is left whole. The acyclic reading
forces flow `4 = ⟨2,3⟩` (so the split routing has no `3↔2` two-cycle). -/

namespace DeepWiki

/-- The cyclic four-server network's flow routing: flow `1 = ⟨3,4,2⟩`,
`2 = ⟨4,2,3⟩`, `3 = ⟨2,1,3⟩`, `4 = ⟨2,3⟩` (servers numbered `1..4` as `ℕ`). -/
def fourServerPaths : Fin 4 → List ℕ
  | 0 => [3, 4, 2]
  | 1 => [4, 2, 3]
  | 2 => [2, 1, 3]
  | 3 => [2, 3]

/-- The split (feed-forward-transformed) routing: each removed arc `(4,2)`,
`(2,1)` cuts a flow into sub-flows. `(1,1)=⟨3,4⟩`, `(1,2)=⟨2⟩`, `(2,1)=⟨4⟩`,
`(2,2)=⟨2,3⟩`, `(3,1)=⟨2⟩`, `(3,2)=⟨1,3⟩`, `(4,1)=⟨2,3⟩`. -/
def feedForwardSubPaths : Fin 7 → List ℕ
  | 0 => [3, 4]   -- (1,1)
  | 1 => [2]      -- (1,2)
  | 2 => [4]      -- (2,1)
  | 3 => [2, 3]   -- (2,2)
  | 4 => [2]      -- (3,1)
  | 5 => [1, 3]   -- (3,2)
  | 6 => [2, 3]   -- (4,1)

/-- A server ranking witnessing acyclicity of the split routing: servers `1,2`
have rank `0`, server `3` rank `1`, server `4` rank `2`. Every sub-flow path is
strictly increasing under it. -/
def feedForwardRank : ℕ → ℕ
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | _ => 0

/-- The original four-server routing has **no** feed-forward ranking: any rank
would need `rank 3 < rank 4 < rank 2` (flow 1) yet `rank 4 < rank 2 < rank 3`
(flow 2), forcing `rank 2 < rank 3 < rank 2`. So the network is cyclic. -/
theorem fourServerNetwork_not_feedForward :
    ¬ ∃ rank : ℕ → ℕ, IsFeedForward rank fourServerPaths := by
  rintro ⟨rank, h⟩
  have h0 : List.IsChain (fun a b => rank a < rank b) [3, 4, 2] := h 0
  have h1 : List.IsChain (fun a b => rank a < rank b) [4, 2, 3] := h 1
  simp only [List.isChain_cons, List.head?_cons, List.head?_nil,
    Option.mem_def, Option.some.injEq, List.isChain_nil, and_true] at h0 h1
  have a0 : rank 3 < rank 4 := h0.1 4 rfl
  have a1 : rank 4 < rank 2 := h0.2.1 2 rfl
  have b1 : rank 2 < rank 3 := h1.2.1 3 rfl
  omega

/-- The split routing **is** feed-forward under `feedForwardRank`: every
sub-flow path is a strictly rank-increasing chain. This is the result of
removing the arcs `(4,2)` and `(2,1)` by turn prohibition. -/
theorem feedForwardTransform_isFeedForward :
    IsFeedForward feedForwardRank feedForwardSubPaths := by
  intro i; fin_cases i <;> decide

/-- The split routing realizes the cycle-breaking: it admits *some* feed-forward
ranking (existential form of `feedForwardTransform_isFeedForward`), whereas the
original (`fourServerNetwork_not_feedForward`) admits none. -/
theorem feedForwardTransform_exists_feedForward :
    ∃ rank : ℕ → ℕ, IsFeedForward rank feedForwardSubPaths :=
  ⟨feedForwardRank, feedForwardTransform_isFeedForward⟩

end DeepWiki
