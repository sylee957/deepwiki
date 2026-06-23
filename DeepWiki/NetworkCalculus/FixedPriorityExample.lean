import DeepWiki.NetworkCalculus.FeedForwardTransformExample
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! # Furthest-destination-first (FDF) priorities on the four-server network
The §12.3 fixed-priority "furthest destination first" policy on the four-server
cyclic network of Figure 12.1. FDF gives a flow its priority at each server by
its *remaining distance* — the number of servers it has yet to cross after the
current one — with priority to the flow furthest from its destination
(`remainingDistance`, higher = higher priority). Priorities may differ per
server.

At **server 3** the FDF order matches the book exactly: flow `1` (remaining `2`)
is strictly above flow `4` (remaining `1`), which is strictly above flows `2`
and `3` (both remaining `0`, tied) —
`fdf_server3_flow1_above_flow4`, `fdf_server3_flow4_above_flows23`,
`fdf_server3_flows2_3_tie`. This server-3 reading pins flow `4 = ⟨3,2⟩`.

The four flows here use the cyclic routing of `fourServerNetwork`; flows
`1,2,3` are as in `fourServerPaths`, and flow `4 = ⟨3,2⟩` is the reading forced
by the server-3 priorities of Example 12.2 (see the note at the end on the
cross-example flow-`4` ambiguity). -/

namespace DeepWiki

/-- **Remaining distance** of flow path `p` at server `h`: the number of servers
strictly after the first occurrence of `h` in `p` (the servers `p` has yet to
cross once it is at `h`). FDF gives higher priority to larger remaining distance.
For `h ∉ p` it is `0`. -/
def remainingDistance (h : ℕ) (p : List ℕ) : ℕ :=
  (p.dropWhile (· ≠ h)).length - 1

/-- **FDF priority order** at server `h`: flow path `p` has strictly higher
priority than `q` when its remaining distance at `h` is larger ("furthest
destination first"). Equal remaining distance is a tie (arbitrary policy). -/
def fdfHigherPriority (h : ℕ) (p q : List ℕ) : Prop :=
  remainingDistance h q < remainingDistance h p

/-- Flow `4`'s path under the Example 12.2 (server-3 FDF) reading: `⟨3,2⟩`. -/
def flow4PathFdf : List ℕ := [3, 2]

/-! ### Server 3 priorities (matching the book exactly) -/

/-- At server 3, flow 1 (`⟨3,4,2⟩`, remaining distance `2`) has strictly higher
FDF priority than flow 4 (`⟨3,2⟩`, remaining distance `1`). -/
theorem fdf_server3_flow1_above_flow4 :
    fdfHigherPriority 3 (fourServerPaths 0) flow4PathFdf := by
  unfold fdfHigherPriority; decide

/-- At server 3, flow 4 (`⟨3,2⟩`, remaining distance `1`) has strictly higher
FDF priority than flows 2 and 3 (remaining distance `0`). -/
theorem fdf_server3_flow4_above_flows23 :
    fdfHigherPriority 3 flow4PathFdf (fourServerPaths 1)
      ∧ fdfHigherPriority 3 flow4PathFdf (fourServerPaths 2) := by
  unfold fdfHigherPriority; refine ⟨?_, ?_⟩ <;> decide

/-- At server 3, flows 2 (`⟨4,2,3⟩`) and 3 (`⟨2,1,3⟩`) share priority: both have
remaining distance `0`, so neither is strictly above the other. -/
theorem fdf_server3_flows2_3_tie :
    remainingDistance 3 (fourServerPaths 1) = remainingDistance 3 (fourServerPaths 2)
      ∧ ¬ fdfHigherPriority 3 (fourServerPaths 1) (fourServerPaths 2)
      ∧ ¬ fdfHigherPriority 3 (fourServerPaths 2) (fourServerPaths 1) := by
  unfold fdfHigherPriority; refine ⟨?_, ?_, ?_⟩ <;> decide

/-- At server 3, flow 1 is the unique highest-priority flow (above every other
crossing flow): above flow 4, flow 2, and flow 3. -/
theorem fdf_server3_flow1_highest :
    fdfHigherPriority 3 (fourServerPaths 0) flow4PathFdf
      ∧ fdfHigherPriority 3 (fourServerPaths 0) (fourServerPaths 1)
      ∧ fdfHigherPriority 3 (fourServerPaths 0) (fourServerPaths 2) := by
  unfold fdfHigherPriority; refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### Server 2 priorities (the FDF computation; see the erratum note)

The book's Example 12.2 states that at server 2 "flows 4 and 3 share the
highest priority, and flow 1 is given the lowest priority." Under the topology
the *computed* FDF remaining distances at server 2 are flow 3 = `2`, flow 2 =
`1`, flow 1 = flow 4 = `0`, so the actual FDF order is flow 3 strictly highest,
then flow 2, then {flow 1, flow 4} tied lowest — which does **not** match the
book's server-2 sentence (and is inconsistent with the server-3 reading's
flow `4 = ⟨3,2⟩`). The verifiable FDF facts at server 2 are recorded here; the
mismatch with the prose is a book erratum (see the closing note). -/

/-- At server 2, flow 3 (`⟨2,1,3⟩`, remaining distance `2`) is the actual FDF
highest-priority flow, strictly above flows 2, 1 and 4. -/
theorem fdf_server2_flow3_highest :
    fdfHigherPriority 2 (fourServerPaths 2) (fourServerPaths 1)
      ∧ fdfHigherPriority 2 (fourServerPaths 2) (fourServerPaths 0)
      ∧ fdfHigherPriority 2 (fourServerPaths 2) flow4PathFdf := by
  unfold fdfHigherPriority; refine ⟨?_, ?_, ?_⟩ <;> decide

/-- At server 2, flows 1 (`⟨3,4,2⟩`) and 4 (`⟨3,2⟩`) are tied lowest: both have
remaining distance `0`. -/
theorem fdf_server2_flows1_4_tie :
    remainingDistance 2 (fourServerPaths 0) = remainingDistance 2 flow4PathFdf
      ∧ remainingDistance 2 (fourServerPaths 0) = 0 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### Note on the flow-`4` ambiguity

Flow `4` is left whole by the feed-forward transformation (Example 12.1), so
Example 12.1 only constrains it to contain neither removed arc `(4,2)` nor
`(2,1)`; both `⟨2,3⟩` and `⟨3,2⟩` qualify. The two worked examples then pull in
opposite directions:

* **Example 12.1** ("removing arc `(4,2)` gives an *acyclic* network") forces
  flow `4 = ⟨2,3⟩` — otherwise `⟨3,2⟩` re-introduces a `3↔2` two-cycle in the
  split routing. This is the reading used in `FeedForwardTransformExample`.
* **Example 12.2** (server 3: flow 4 strictly between flow 1 and flows 2,3)
  forces flow `4 = ⟨3,2⟩` — the reading used here (`flow4PathFdf`); under
  `⟨2,3⟩` flow 4 would tie with flows 2,3 at server 3.

The book's server-2 sentence matches neither reading, so it is taken as an
illustrative misstatement. Each example is formalized under the flow-`4` path
its own claim requires. -/

end DeepWiki
