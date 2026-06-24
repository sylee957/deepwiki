import DeepWiki.NetworkCalculus.CombinedTableau
import DeepWiki.NetworkCalculus.TableauStateTransition
import DeepWiki.NetworkCalculus.ReachableCont

/-!
# State-transition assembly for the Cook- and Levin-style tableau

Layer 3c-i of a Cook- and Levin-style formalization: the **state (`σ`) transition assembly**.
The per-constructor `σ`-update gadgets of `TableauStateTransition` (`keepStateClauses`,
`loadStateClauses`, `peekStateClauses`) are dispatched by the *continuation* at time `t` —
the register value `cont : ReachableCont.ContTok tm` — via `BooleanConstraints.conditionOn`,
each lifted from the main tableau block into the combined space with
`BooleanConstraints.liftClausesL`.  The resulting `stateTransClauses t` is correct at the
`readState` level: it forces `readState (t+1)` to equal the **state component** of one uniform
small-step `UnifSmallStep.unifStep` applied to the read continuation, state, and stacks.

* `stateGadgetFor cont t` — picks the right main-space gadget for the head of `cont`:
  `keepStateClauses` for `none`/`push`/`branch`/`goto`/`halt` (state unchanged),
  `loadStateClauses … a` for `load a _`, `peekStateClauses … k f` for `peek k f _`/`pop k f _`
  (their `σ`-updates coincide).
* `stateTransClauses t` — the combined-space assembly: over every continuation token, guard the
  lifted gadget by that token's `contVar` and append.
* `stateTransClauses_spec` — under `FullConsistent` and the per-stack stack-shape hypothesis at
  `t`, `readState (t+1) = (unifStep tm.m (contToUnif (cont@t), state@t, stacks@t)).2.1`.

## Deferred

This chunk is **only** the `σ`-side assembly and its `readState` correctness (taking
`IsStackShape@t` and `0 < S` as hypotheses).  The cell-transition assembly (push- and pop- per
continuation), the `IsStackShape` invariant *propagation* across time, the continuation-register
transition clauses, the full `readUnif (t+1) = unifStep (readUnif t)` combining the
continuation-, state-, and cell- components, init- and accept- clauses, and reduction
correctness are **later** layers.
-/

open Turing

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep
open Turing.TM2 Turing.TM2.Stmt

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

open scoped Classical

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-! ## (0) Forgetting the membership proof of a continuation token

A `ContTok tm` is `none` (halted) or `some ⟨q, _⟩`; `contToUnif` drops the membership proof,
giving the `Option (Turing.TM2.Stmt …)` continuation `unifStep` consumes. -/

/-- Forget a continuation token's relevance proof: `Option.map Subtype.val`. -/
def contToUnif (cont : ContTok tm) : Option (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :=
  cont.map Subtype.val

omit [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- `contToUnif none = none`. -/
@[simp] theorem contToUnif_none : contToUnif (tm := tm) none = none := rfl

omit [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- `contToUnif (some ⟨q, _⟩) = some q`. -/
@[simp] theorem contToUnif_some (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hq : q ∈ relevantStmts tm) : contToUnif (some ⟨q, hq⟩) = some q := rfl

/-! ## (1) Per-continuation state gadget (main space) -/

/-- The **state-update gadget for `cont`** over `t → t+1` (main tableau space): `keepStateClauses`
when the head leaves `σ` unchanged (`none`/`push`/`branch`/`goto`/`halt`), `loadStateClauses … a`
for `load a _`, `peekStateClauses … k f` for `peek k f _` and `pop k f _` (whose `σ`-updates
coincide). -/
noncomputable def stateGadgetFor (cont : ContTok tm) (t : Fin T) (hS0 : 0 < S) :
    List (Clause (numVars tm T S)) :=
  match cont with
  | none => keepStateClauses t
  | some ⟨q, _⟩ =>
    match q with
    | push _ _ _ => keepStateClauses t
    | branch _ _ _ => keepStateClauses t
    | goto _ => keepStateClauses t
    | halt => keepStateClauses t
    | load a _ => loadStateClauses t a
    | peek k f _ => peekStateClauses t k f hS0
    | pop k f _ => peekStateClauses t k f hS0

/-! ## (2) The combined-space state-transition assembly -/

variable (tm S) in
/-- The **state-transition clauses** over `t → t+1`: over every continuation token, guard the
left-lifted state gadget by that token's `contVar` at `t`, and append. `conditionOn` selects the
active token's gadget; `liftClausesL` embeds the main-space gadget into the combined space. -/
noncomputable def stateTransClauses (t : Fin T) (hS0 : 0 < S) :
    List (Clause (fullNumVars tm T S (ContTok tm))) :=
  (Finset.univ : Finset (ContTok tm)).toList.flatMap
    (fun cont => conditionOn (contVar (V := ContTok tm) (Fin.castSucc t) cont)
      (liftClausesL (stateGadgetFor cont t hS0)))

/-! ## (3) Dispatch extraction: drop to the active token's gadget on the main block -/

/-- **`flatMap` extraction.** If `x ∈ l` and `assign` satisfies `l.flatMap g`, then it satisfies
the single group `g x`. -/
theorem satisfiesAll_flatMap_of_mem {n : ℕ} {α : Type*} {assign : Fin n → Bool}
    {l : List α} {g : α → List (Clause n)} {x : α} (hx : x ∈ l)
    (h : satisfiesAll assign (l.flatMap g)) : satisfiesAll assign (g x) := by
  rw [List.flatMap_def, satisfiesAll_flatten] at h
  exact h (g x) (List.mem_map.2 ⟨x, hx, rfl⟩)

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Dispatch extraction.** Under full consistency, satisfying `stateTransClauses` forces the
**active** continuation's gadget (for `cont₀ = readContC assign (castSucc t)`) to be satisfied on
the main block `mainAssign assign`. -/
theorem satisfiesAll_stateGadgetFor_active {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {t : Fin T} {hS0 : 0 < S}
    (h : satisfiesAll assign (stateTransClauses tm S t hS0)) :
    satisfiesAll (mainAssign assign)
      (stateGadgetFor (readContC assign (Fin.castSucc t)) t hS0) := by
  set cont₀ := readContC assign (Fin.castSucc t) with hcont₀
  -- the active token's `contVar` is true (one-hot register: the read value's coordinate)
  have hregcons : RegConsistent (contAssign assign) := ((fullConsistent_iff assign).1 hcons).2
  have hvar : assign (contVar (V := ContTok tm) (Fin.castSucc t) cont₀) = true := by
    have hself := readReg_self_true hregcons (Fin.castSucc t)
    rw [contAssign_contVar] at hself
    rw [hcont₀, readContC]; exact hself
  -- pull the active token's guarded+lifted summand out of the `flatMap`
  rw [stateTransClauses] at h
  have hsummand : satisfiesAll assign
      (conditionOn (contVar (V := ContTok tm) (Fin.castSucc t) cont₀)
        (liftClausesL (stateGadgetFor cont₀ t hS0))) :=
    satisfiesAll_flatMap_of_mem
      (g := fun cont => conditionOn (contVar (V := ContTok tm) (Fin.castSucc t) cont)
        (liftClausesL (stateGadgetFor cont t hS0)))
      (Finset.mem_toList.2 (Finset.mem_univ cont₀)) h
  -- unguard (the guard variable is true), then drop to the main block
  have hlift := conditionOn_spec assign _ _ hsummand hvar
  rw [satisfiesAll_liftClausesL] at hlift
  exact hlift

/-! ## (4) `readState`-level correctness against `unifStep` -/

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **State-transition correctness.** Under full consistency and the per-stack stack-shape
hypothesis at the time-`t` cells, the state-transition clauses force `readState (t+1)` to be the
**state component** of one `unifStep` from the read continuation, state, and stacks at `t`. -/
theorem stateTransClauses_spec {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {t : Fin T} {hS0 : 0 < S}
    (h : satisfiesAll assign (stateTransClauses tm S t hS0))
    (hshape : ∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) (Fin.castSucc t) k i)
      (readStack (mainAssign assign) (Fin.castSucc t) k)) :
    readState (mainAssign assign) (Fin.succ t) =
      (unifStep tm.m (contToUnif (readContC assign (Fin.castSucc t)),
        readState (mainAssign assign) (Fin.castSucc t),
        fun k => readStack (mainAssign assign) (Fin.castSucc t) k)).2.1 := by
  -- the main block is consistent (from full consistency) and the active gadget holds on it
  have hmaincons : Consistent (mainAssign assign) := ((fullConsistent_iff assign).1 hcons).1
  have hgad := satisfiesAll_stateGadgetFor_active hcons h
  -- case on the active continuation token and its head statement; match `unifStep`'s `σ` arm
  set cont₀ := readContC assign (Fin.castSucc t) with hcont₀
  clear hcont₀
  match cont₀, hgad with
  | none, hgad =>
    rw [stateGadgetFor] at hgad
    rw [keepState_readState hmaincons hgad]; rfl
  | some ⟨push k f q', hq⟩, hgad =>
    rw [stateGadgetFor] at hgad
    rw [keepState_readState hmaincons hgad]; rfl
  | some ⟨branch g q₁ q₂, hq⟩, hgad =>
    rw [stateGadgetFor] at hgad
    rw [keepState_readState hmaincons hgad]; rfl
  | some ⟨goto g, hq⟩, hgad =>
    rw [stateGadgetFor] at hgad
    rw [keepState_readState hmaincons hgad]; rfl
  | some ⟨halt, hq⟩, hgad =>
    rw [stateGadgetFor] at hgad
    rw [keepState_readState hmaincons hgad]; rfl
  | some ⟨load a q', hq⟩, hgad =>
    rw [stateGadgetFor] at hgad
    rw [loadState_readState hmaincons hgad]; rfl
  | some ⟨peek k f q', hq⟩, hgad =>
    rw [stateGadgetFor] at hgad
    rw [peekState_readState_head hmaincons hgad (hshape k)]; rfl
  | some ⟨pop k f q', hq⟩, hgad =>
    rw [stateGadgetFor] at hgad
    rw [peekState_readState_head hmaincons hgad (hshape k)]; rfl

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The state-transition clauses force `readState (t+1)` to be `unifStep`'s state component.
example {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {t : Fin T} {hS0 : 0 < S}
    (h : satisfiesAll assign (stateTransClauses tm S t hS0))
    (hshape : ∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) (Fin.castSucc t) k i)
      (readStack (mainAssign assign) (Fin.castSucc t) k)) :
    readState (mainAssign assign) (Fin.succ t) =
      (unifStep tm.m (contToUnif (readContC assign (Fin.castSucc t)),
        readState (mainAssign assign) (Fin.castSucc t),
        fun k => readStack (mainAssign assign) (Fin.castSucc t) k)).2.1 :=
  stateTransClauses_spec hcons h hshape

end Examples

end CombinedTableau

end DeepWiki
