import DeepWiki.NetworkCalculus.TableauCellTransition

/-!
# Tableau state-transition clauses (keep / load / peek)

Layer 3b-iii(d) of a Cook- and Levin-style formalization: the **state (`σ`) transition clause
families** relating the internal state at time `t` to the state at `t+1`, each with correctness
at the `readState` level.  The `σ`-side parallel of the cell-transition gadget, indexed by
`t : Fin T` (`Fin.castSucc t` / `Fin.succ t` are the consecutive times in `Fin (T+1)`):

* `keepStateClauses t` — state **unchanged**: `state(t) ↔ state(t+1)`, a `funClauses` identity
  with `f = id`.  Correctness `keepState_readState` : `readState (t+1) = readState t`.
* `loadStateClauses t a` — state **loaded** by `a : σ → σ`: `state(t+1) = a (state(t))`, a
  `funClauses` link.  Correctness `loadState_readState` : `readState (t+1) = a (readState t)`.
* `peekStateClauses t k f` — state **peek-updated** by `f : σ → Option (Γ k) → σ` reading the
  **top cell** of stack `k` (the cell at position `0`): `state(t+1) = f (state(t)) (top@t)`, a
  `funClauses₂` link.  Correctness `peekState_readState` :
  `readState (t+1) = f (readState t) (readCell t k 0)`, and `peekState_readState_head` rewrites
  the top cell to the list head `(readStack t k).head?` under the stack-shape bridge.

`pop`'s state update **is** `peek`'s — both are `f v (S k).head?` (the top of stack `k`); `pop`
additionally shifts the cells, which is handled by `popCellClauses` in the cell layer.

## Deferred

Only the keep/load/peek state gadgets and their `readState` correctness (plus the top-cell = head
bridge) live here.  The continuation-coordinate dispatch (which gadget fires per `Stmt` head —
needs a continuation schema), the per-`stmtStep` assembly combining cell- and state- and
continuation-clauses, halt-padding, the `branch`/`goto`/`halt` continuation logic, and reduction
correctness are **later** layers.
-/

open Turing

namespace DeepWiki

namespace TableauSchema

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

open BooleanConstraints

variable {tm : FinTM2} {T S : ℕ} [∀ k, Fintype (tm.Γ k)]

/-! ## (0) The top-cell = list-head bridge

Under stack shape, the cell at position `0` is exactly the head of the reconstructed stack: the
`0`-th entry of `List.ofFn cells = L.map some ++ replicate _ none` reads off `L.head?`. -/

/-- **Top cell = head.** Under consistency, if the time-`t` cells of stack `k` are in stack shape
for `L`, the cell at position `0` is the head of `L` (= the head of `readStack t k`). -/
theorem readCell_zero_eq_head {assign : Fin (numVars tm T S) → Bool} {t : Fin (T + 1)} {k : tm.K}
    {L : List (tm.Γ k)} (hS0 : 0 < S)
    (h : IsStackShape (fun i : Fin S => readCell assign t k i) L) :
    readCell assign t k ⟨0, hS0⟩ = L.head? := by
  -- `ofFn cells` has the explicit `0`-th entry `cells ⟨0,_⟩`; under stack shape it also equals
  -- the `0`-th entry of `L.map some ++ replicate _ none`, whose head is `L.head?`.
  have hlhs : (List.ofFn fun i : Fin S => readCell assign t k i).head?
      = some (readCell assign t k ⟨0, hS0⟩) := by
    cases S with
    | zero => exact absurd hS0 (by omega)
    | succ m =>
      rw [List.ofFn_succ]
      rfl
  rw [IsStackShape] at h
  rw [h] at hlhs
  -- the head of `L.map some ++ replicate _ none` is `L.head?` (mapped through `some`)
  have hrhs : (L.map some ++ List.replicate (S - L.length) none).head? = some L.head? := by
    cases L with
    | nil =>
      cases S with
      | zero => exact absurd hS0 (by omega)
      | succ m => simp [List.replicate_succ]
    | cons x xs => simp
  rw [hrhs] at hlhs
  exact (Option.some.inj hlhs).symm

/-! ## (1) The state slot's coordinate map -/

/-- The state-coordinate variable map at time `t`: `s ↦ coordVar (stateCoord t s)` — the
`funClauses` input/output map for the state slot. -/
noncomputable def stateVar (t : Fin (T + 1)) (s : tm.σ) : Fin (numVars tm T S) :=
  coordVar (stateCoord t s)

/-! ## (2) Keep: the state is unchanged from `t` to `t+1`

A single `funClauses` identity (`f = id`) links the state at `(castSucc t)` to the state at
`(succ t)`: whichever state holds at time `t` also holds at `t+1`. -/

/-- The **keep state clauses** over `t → t+1`: the `funClauses` identity linking
`state(castSucc t)` to `state(succ t)`. -/
noncomputable def keepStateClauses (t : Fin T) : List (Clause (numVars tm T S)) :=
  funClauses (fun s : tm.σ => stateVar (Fin.castSucc t) s)
    (fun s : tm.σ => stateVar (Fin.succ t) s) id

/-- **Keep, `readState` correctness.** Under consistency, the keep clauses force the state at
`t+1` to equal the state at `t`. -/
theorem keepState_readState {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} (h : satisfiesAll assign (keepStateClauses (T := T) (S := S) t)) :
    readState assign (Fin.succ t) = readState assign (Fin.castSucc t) := by
  -- the read time-`t` state's coordinate is true; forward `funClauses` propagates it to `t+1`
  have hin := readState_self_true hcons (Fin.castSucc t)
  have hout := funClauses_spec _ _ id assign h (readState assign (Fin.castSucc t)) hin
  simpa [stateVar] using readState_eq hcons hout

/-! ## (3) Load: the state at `t+1` is `a (state@t)`

A `funClauses` for `a : σ → σ` links the state at `(castSucc t)` to the state `a (state@t)` at
`(succ t)`. -/

/-- The **load state clauses** over `t → t+1` with loader `a : σ → σ`: the `funClauses` link
`state(succ t) = a (state(castSucc t))`. -/
noncomputable def loadStateClauses (t : Fin T) (a : tm.σ → tm.σ) :
    List (Clause (numVars tm T S)) :=
  funClauses (fun s : tm.σ => stateVar (Fin.castSucc t) s)
    (fun s : tm.σ => stateVar (Fin.succ t) s) a

/-- **Load, `readState` correctness.** Under consistency, the load clauses force the state at
`t+1` to be `a` of the state at `t`. -/
theorem loadState_readState {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {a : tm.σ → tm.σ}
    (h : satisfiesAll assign (loadStateClauses (T := T) (S := S) t a)) :
    readState assign (Fin.succ t) = a (readState assign (Fin.castSucc t)) := by
  have hin := readState_self_true hcons (Fin.castSucc t)
  have hout := funClauses_spec _ _ a assign h (readState assign (Fin.castSucc t)) hin
  simpa [stateVar] using readState_eq hcons hout

/-! ## (4) Peek/pop state update: `f (state@t) (top of stack k @t)`

A `funClauses₂` links the state at `(castSucc t)` **and** the top cell of stack `k` (the cell at
position `0`, needing `0 < S`) at time `t` to the state at `(succ t)`, set to `f` of the two.
This is the state update of both `peek` and `pop` (their `σ`-side coincides). -/

/-- The **peek/pop state clauses** over `t → t+1` for stack `k` with update
`f : σ → Option (Γ k) → σ` reading the top cell (position `0`, requiring `0 < S`): the
`funClauses₂` link `state(succ t) = f (state(castSucc t)) (cell(castSucc t, k, 0))`. -/
noncomputable def peekStateClauses (t : Fin T) (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ)
    (hS0 : 0 < S) : List (Clause (numVars tm T S)) :=
  funClauses₂ (fun s : tm.σ => stateVar (Fin.castSucc t) s)
    (fun c : Option (tm.Γ k) => coordVar (cellCoord (Fin.castSucc t) k ⟨0, hS0⟩ c))
    (fun s : tm.σ => stateVar (Fin.succ t) s) f

/-- **Peek/pop, `readState` correctness.** Under consistency, the peek clauses force the state at
`t+1` to be `f` of the state at `t` and the top cell `(castSucc t, k, 0)` at `t`. -/
theorem peekState_readState {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} {f : tm.σ → Option (tm.Γ k) → tm.σ} {hS0 : 0 < S}
    (h : satisfiesAll assign (peekStateClauses (T := T) (S := S) t k f hS0)) :
    readState assign (Fin.succ t)
      = f (readState assign (Fin.castSucc t)) (readCell assign (Fin.castSucc t) k ⟨0, hS0⟩) := by
  -- both inputs' read coordinates are true; the binary `funClauses₂` propagates the output
  have hinS := readState_self_true hcons (Fin.castSucc t)
  have hinC := readCell_self_true hcons (Fin.castSucc t) k ⟨0, hS0⟩
  have hout := funClauses₂_spec _ _ _ f assign h (readState assign (Fin.castSucc t))
    (readCell assign (Fin.castSucc t) k ⟨0, hS0⟩) hinS hinC
  simpa [stateVar] using readState_eq hcons hout

/-- **Peek/pop, `readState` via the list head.** Under consistency and the stack-shape bridge, the
peek clauses give the state at `t+1` as `f` of the state at `t` and the head of `readStack t k`. -/
theorem peekState_readState_head {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} {f : tm.σ → Option (tm.Γ k) → tm.σ} {hS0 : 0 < S}
    (h : satisfiesAll assign (peekStateClauses (T := T) (S := S) t k f hS0))
    (hshape : IsStackShape (fun i : Fin S => readCell assign (Fin.castSucc t) k i)
      (readStack assign (Fin.castSucc t) k)) :
    readState assign (Fin.succ t)
      = f (readState assign (Fin.castSucc t)) ((readStack assign (Fin.castSucc t) k).head?) := by
  rw [peekState_readState hcons h, readCell_zero_eq_head hS0 hshape]

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

-- Keep: the state at `t+1` equals the state at `t`.
example {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} (h : satisfiesAll assign (keepStateClauses (T := T) (S := S) t)) :
    readState assign (Fin.succ t) = readState assign (Fin.castSucc t) :=
  keepState_readState hcons h

-- Load: the state at `t+1` is `a (state@t)`.
example {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {a : tm.σ → tm.σ}
    (h : satisfiesAll assign (loadStateClauses (T := T) (S := S) t a)) :
    readState assign (Fin.succ t) = a (readState assign (Fin.castSucc t)) :=
  loadState_readState hcons h

-- Peek/pop: the state at `t+1` is `f (state@t) (top cell of stack k @t)`.
example {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} {f : tm.σ → Option (tm.Γ k) → tm.σ} {hS0 : 0 < S}
    (h : satisfiesAll assign (peekStateClauses (T := T) (S := S) t k f hS0)) :
    readState assign (Fin.succ t)
      = f (readState assign (Fin.castSucc t)) (readCell assign (Fin.castSucc t) k ⟨0, hS0⟩) :=
  peekState_readState hcons h

-- Peek/pop via head: the state at `t+1` is `f (state@t) ((readStack t k).head?)`.
example {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} {f : tm.σ → Option (tm.Γ k) → tm.σ} {hS0 : 0 < S}
    (h : satisfiesAll assign (peekStateClauses (T := T) (S := S) t k f hS0))
    (hshape : IsStackShape (fun i : Fin S => readCell assign (Fin.castSucc t) k i)
      (readStack assign (Fin.castSucc t) k)) :
    readState assign (Fin.succ t)
      = f (readState assign (Fin.castSucc t)) ((readStack assign (Fin.castSucc t) k).head?) :=
  peekState_readState_head hcons h hshape

end Examples

end TableauSchema

end DeepWiki
