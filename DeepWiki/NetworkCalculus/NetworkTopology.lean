import Mathlib.Data.List.Infix
import Mathlib.Data.List.Chain

/-! # Network topology classes
The special topologies of modular analysis, over flow paths represented as
`List κ` of server indices (the same path representation the concatenation
chain uses): a *tandem* is a line of servers crossed by contiguous subpaths,
a *nested tandem* has its flow paths totally ordered by contiguous-subpath
inclusion (the book's (Nest) condition), and a *feed-forward* network admits a
server ranking under which every flow path strictly increases — i.e. the flow
graph is acyclic. -/

namespace DeepWiki

/-- A family of flow paths is a **nested tandem** when any two paths are
comparable under contiguous-subpath (infix) inclusion: `pᵢ <:+: pⱼ` or
`pⱼ <:+: pᵢ` (the book's (Nest) condition). -/
def IsNestedTandem {κ ι : Type*} (paths : ι → List κ) : Prop :=
  ∀ i j : ι, paths i <:+: paths j ∨ paths j <:+: paths i

/-- A **tandem** network: there is a line of servers `line` of which every flow
path is a contiguous subpath (infix). -/
def IsTandemNetwork {κ ι : Type*} (line : List κ) (paths : ι → List κ) : Prop :=
  ∀ i : ι, paths i <:+: line

/-- A **feed-forward** network: the servers admit a ranking `rank : κ → ℕ`
under which every flow path is strictly increasing (consecutive servers
increase in rank), so the flow graph is acyclic. -/
def IsFeedForward {κ ι : Type*} (rank : κ → ℕ) (paths : ι → List κ) : Prop :=
  ∀ i : ι, (paths i).IsChain (fun a b => rank a < rank b)

/-- A single-flow network is trivially a nested tandem (a path is an infix of
itself). -/
theorem isNestedTandem_of_subsingleton {κ ι : Type*} [Subsingleton ι]
    (paths : ι → List κ) : IsNestedTandem paths := fun i j => by
  rw [Subsingleton.elim i j]; exact Or.inl (List.infix_refl _)

end DeepWiki
