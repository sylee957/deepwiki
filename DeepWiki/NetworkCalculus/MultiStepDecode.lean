import DeepWiki.NetworkCalculus.UnifTransition
import DeepWiki.NetworkCalculus.StackShapePropagation

/-!
# Multi-step decode for the Cook- and Levin-style tableau

Layer 3c-iv: the **multi-step decode**.  Chaining the per-time-step correctness
(`unifTransClauses_spec`) with the stack-shape invariant propagation
(`isStackShape_propagate`) across the whole time axis, a satisfying assignment's
unified readback follows the uniform machine: `readUnif t = (unifStep tm.m)^[t]
(readUnif 0)`, with the `IsStackShape` invariant carried as a joint induction
hypothesis.

* `step_decode` — single-step joint advance: one `unifStep` of the readback plus
  `IsStackShape` at `t+1` (`.1` is `unifTransClauses_spec`, `.2` is
  `isStackShape_propagate` after splitting off the cell clauses).
* `readUnif_iterate` — the `ℕ`-indexed induction: `readUnif n = unifStep^[n]
  (readUnif 0)` and `IsStackShape@n`, for every `n ≤ T`.
* `readUnif_last` — the `Fin.last` corollary: `readUnif (last T) = unifStep^[T]
  (readUnif 0)`.

## Deferred

This chunk is the multi-step decode **only**, taking `IsStackShape@0`, the per-time
room bound `length < S` at every time, and "all transition clauses hold" as
hypotheses.  Deriving the room bound from a space bound `S ≥ init + T` (poly-size
setup), the init- and accept- clauses, connecting `readUnif 0` to the actual
`initUnif` and `readUnif (last T)` to acceptance (via `UnifSimulation`), and the
final reduction correctness are **later** layers.
-/

open Turing

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep
open Turing.TM2 Turing.TM2.Stmt

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-! ## (0) `Fin (T+1)` index bookkeeping

The induction runs over a `ℕ` time index and packages back to `Fin (T+1)`; these
two `Fin.ext`/`omega` helpers convert `castSucc`/`succ` of a `⟨n, _⟩ : Fin T` to the
plain `⟨n, _⟩` / `⟨n+1, _⟩` shape the readback is indexed by. -/

/-- `castSucc ⟨n, hlt⟩ = ⟨n, _⟩`: the `Fin (T+1)` recast of an index below `T`. -/
theorem castSucc_mk_eq {n : ℕ} (hlt : n < T) (h : n < T + 1) :
    (⟨n, hlt⟩ : Fin T).castSucc = ⟨n, h⟩ := by
  apply Fin.ext; simp

/-- `succ ⟨n, hlt⟩ = ⟨n+1, _⟩`: the `Fin (T+1)` successor of an index below `T`. -/
theorem succ_mk_eq {n : ℕ} (hlt : n < T) (h : n + 1 < T + 1) :
    (⟨n, hlt⟩ : Fin T).succ = ⟨n + 1, h⟩ := by
  apply Fin.ext; simp

/-! ## (1) Single-step joint advance -/

/-- **Single-step joint advance.** Under full consistency, with the stack shape and
room (`length < S`) at the time-`t` cells, the unified transition clauses force one
`unifStep` of the readback *and* propagate the stack shape to `t+1`: `.1` is
`unifTransClauses_spec`, `.2` is `isStackShape_propagate` (after splitting off the
`cellTransClauses` part with `satisfiesAll_append`). -/
theorem step_decode {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {t : Fin T} {hS0 : 0 < S}
    (htrans : satisfiesAll assign (unifTransClauses tm S t hS0))
    (hsh : ∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) t.castSucc k i)
      (readStack (mainAssign assign) t.castSucc k))
    (hlen : ∀ k, (readStack (mainAssign assign) t.castSucc k).length < S) :
    readUnif assign t.succ = unifStep tm.m (readUnif assign t.castSucc) ∧
      (∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) t.succ k i)
        (readStack (mainAssign assign) t.succ k)) := by
  refine ⟨unifTransClauses_spec hcons htrans hsh hlen, fun k => ?_⟩
  -- the cell-transition clauses are the last `++` operand of `unifTransClauses`
  have hcell : satisfiesAll assign (cellTransClauses tm S t) := by
    rw [unifTransClauses, satisfiesAll_append] at htrans
    exact htrans.2
  exact isStackShape_propagate hcons hcell hsh hlen k

/-! ## (2) The multi-step decode -/

/-- **Multi-step decode (`ℕ`-indexed).** Given all per-time transition clauses, the
stack shape at time `0`, and per-time room (`length < S`) at every time, for every
`n ≤ T` the readback at time `n` is the `n`-fold `unifStep` of the readback at time
`0`, and the stack shape holds at time `n`.  Induction on `n`: base by
`Function.iterate_zero`; step by `step_decode` at `t := ⟨n, _⟩` plus
`Function.iterate_succ_apply'` and the IH. -/
theorem readUnif_iterate {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {hS0 : 0 < S}
    (htrans : ∀ t : Fin T, satisfiesAll assign (unifTransClauses tm S t hS0))
    (hsh0 : ∀ k, IsStackShape
      (fun i : Fin S => readCell (mainAssign assign) ⟨0, by omega⟩ k i)
      (readStack (mainAssign assign) ⟨0, by omega⟩ k))
    (hlen : ∀ t : Fin (T + 1),
      ∀ k, (readStack (mainAssign assign) t k).length < S) :
    ∀ (n : ℕ), (hn : n ≤ T) →
      readUnif assign ⟨n, by omega⟩ =
        (unifStep tm.m)^[n] (readUnif assign ⟨0, by omega⟩) ∧
      (∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) ⟨n, by omega⟩ k i)
        (readStack (mainAssign assign) ⟨n, by omega⟩ k)) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨?_, hsh0⟩
    rw [Function.iterate_zero, id_eq]
  | succ m ih =>
    intro hle
    have hmlt : m < T := by omega
    obtain ⟨iheq, ihsh⟩ := ih (by omega)
    -- run a single joint step at `t := ⟨m, _⟩`, converting `castSucc`/`succ` of `⟨m,_⟩`
    have hcs : (⟨m, hmlt⟩ : Fin T).castSucc = (⟨m, by omega⟩ : Fin (T + 1)) :=
      castSucc_mk_eq hmlt (by omega)
    have hsc : (⟨m, hmlt⟩ : Fin T).succ = (⟨m + 1, by omega⟩ : Fin (T + 1)) :=
      succ_mk_eq hmlt (by omega)
    have hshcs : ∀ k, IsStackShape
        (fun i : Fin S => readCell (mainAssign assign) (⟨m, hmlt⟩ : Fin T).castSucc k i)
        (readStack (mainAssign assign) (⟨m, hmlt⟩ : Fin T).castSucc k) := by
      rw [hcs]; exact ihsh
    have hlencs : ∀ k,
        (readStack (mainAssign assign) (⟨m, hmlt⟩ : Fin T).castSucc k).length < S := by
      rw [hcs]; exact hlen _
    obtain ⟨steq, stsh⟩ := step_decode hcons (htrans ⟨m, hmlt⟩) hshcs hlencs
    rw [hsc, hcs] at steq
    rw [hsc] at stsh
    refine ⟨?_, stsh⟩
    -- compose: readUnif@(m+1) = unifStep (readUnif@m) = unifStep (unifStep^[m] @0) = unifStep^[m+1] @0
    rw [steq, iheq, Function.iterate_succ_apply']

/-- **Multi-step decode at `Fin.last`.** Instantiating `readUnif_iterate` at `n = T`:
the readback at the final time is the `T`-fold `unifStep` of the initial readback. -/
theorem readUnif_last {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {hS0 : 0 < S}
    (htrans : ∀ t : Fin T, satisfiesAll assign (unifTransClauses tm S t hS0))
    (hsh0 : ∀ k, IsStackShape
      (fun i : Fin S => readCell (mainAssign assign) ⟨0, by omega⟩ k i)
      (readStack (mainAssign assign) ⟨0, by omega⟩ k))
    (hlen : ∀ t : Fin (T + 1),
      ∀ k, (readStack (mainAssign assign) t k).length < S) :
    readUnif assign (Fin.last T) =
      (unifStep tm.m)^[T] (readUnif assign 0) := by
  have h := (readUnif_iterate hcons (hS0 := hS0) htrans hsh0 hlen T le_rfl).1
  -- `Fin.last T = ⟨T, _⟩` and `(0 : Fin (T+1)) = ⟨0, _⟩`
  rw [show (Fin.last T) = (⟨T, by omega⟩ : Fin (T + 1)) from rfl,
    show (0 : Fin (T + 1)) = (⟨0, by omega⟩ : Fin (T + 1)) from rfl]
  exact h

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The final readback is the `T`-fold uniform step of the initial readback.
example {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {hS0 : 0 < S}
    (htrans : ∀ t : Fin T, satisfiesAll assign (unifTransClauses tm S t hS0))
    (hsh0 : ∀ k, IsStackShape
      (fun i : Fin S => readCell (mainAssign assign) ⟨0, by omega⟩ k i)
      (readStack (mainAssign assign) ⟨0, by omega⟩ k))
    (hlen : ∀ t : Fin (T + 1),
      ∀ k, (readStack (mainAssign assign) t k).length < S) :
    readUnif assign (Fin.last T) =
      (unifStep tm.m)^[T] (readUnif assign 0) :=
  readUnif_last hcons (hS0 := hS0) htrans hsh0 hlen

end Examples

end CombinedTableau

end DeepWiki
