import DeepWiki.NetworkCalculus.CombinedTableau
import DeepWiki.NetworkCalculus.TableauCellTransition
import DeepWiki.NetworkCalculus.StateTransitionAssembly

/-!
# Cell-transition assembly for the Cook- and Levin-style tableau

Layer 3c-ii of a Cook- and Levin-style formalization: the **cell (stack) transition assembly**,
the stack parallel of `StateTransitionAssembly`.  The per-stack cell gadgets of
`TableauCellTransition` (`pushCellClauses`, `popCellClauses`, `keepCellClauses`) are dispatched
by the *continuation* at time `t` — the register value `cont : ReachableCont.ContTok tm` — via
`BooleanConstraints.conditionOn`, each lifted from the main tableau block into the combined space
with `BooleanConstraints.liftClausesL`.  The resulting `cellTransClauses t` is correct at the
`readStack` level: it forces `readStack (t+1) k'` to equal the **stack component** of one uniform
small-step `UnifSmallStep.unifStep` applied to the read continuation, state, and stacks — for
*every* stack `k'` (the one changed by a `push`/`pop` and the others left alone).

* `cellGadgetFor cont t` — picks the right per-stack main-space gadgets for the head of `cont`:
  for `push k f _` the `pushCellClauses … k f` on stack `k` plus `keepCellClauses` on every other
  stack; for `pop k f _` the `popCellClauses … k` on stack `k` plus `keepCellClauses` on the rest;
  for every other head (`none`/`peek`/`load`/`branch`/`goto`/`halt`) `keepCellClauses` on *all*
  stacks (no stack changes).
* `cellTransClauses t` — the combined-space assembly: over every continuation token, guard the
  lifted gadget by that token's `contVar` and append.
* `cellTransClauses_spec` — under `FullConsistent`, the per-stack stack-shape hypothesis, and the
  per-stack room hypothesis (`length < S`) at `t`, for every `k'`,
  `readStack (t+1) k' = (unifStep tm.m (contToUnif (cont@t), state@t, stacks@t)).2.2 k'`.

## Deferred

This chunk is **only** the cell-side assembly and its `readStack` correctness (taking
`IsStackShape@t` and `∀ k, length < S` as hypotheses, mirroring the state assembly's hypothesis
style).  The `IsStackShape` invariant *propagation* across time, the full
`readUnif (t+1) = unifStep (readUnif t)` combining the continuation-, state-, and cell- components
(the next layer), init- and accept- clauses, and reduction correctness are **later** layers.
-/

open Turing

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep
open Turing.TM2 Turing.TM2.Stmt
open Function (update)

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

open scoped Classical

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-! ## (1) Per-continuation cell gadget (main space) -/

/-- The **cell-update gadget for `cont`** over `t → t+1` (main tableau space): for a `push k f _`
head the `pushCellClauses … k f` on stack `k` with `keepCellClauses` on every other stack; for a
`pop k f _` head the `popCellClauses … k` on stack `k` with `keepCellClauses` on the rest; for
every other head (`none`/`peek`/`load`/`branch`/`goto`/`halt`) `keepCellClauses` on *all* stacks. -/
noncomputable def cellGadgetFor (cont : ContTok tm) (t : Fin T) :
    List (Clause (numVars tm T S)) :=
  match cont with
  | none => (Finset.univ : Finset tm.K).toList.flatMap (fun k' => keepCellClauses t k')
  | some ⟨q, _⟩ =>
    match q with
    | push k f _ =>
      pushCellClauses t k f ++
        ((Finset.univ : Finset tm.K).erase k).toList.flatMap (fun k' => keepCellClauses t k')
    | pop k _ _ =>
      popCellClauses t k ++
        ((Finset.univ : Finset tm.K).erase k).toList.flatMap (fun k' => keepCellClauses t k')
    | peek _ _ _ => (Finset.univ : Finset tm.K).toList.flatMap (fun k' => keepCellClauses t k')
    | load _ _ => (Finset.univ : Finset tm.K).toList.flatMap (fun k' => keepCellClauses t k')
    | branch _ _ _ => (Finset.univ : Finset tm.K).toList.flatMap (fun k' => keepCellClauses t k')
    | goto _ => (Finset.univ : Finset tm.K).toList.flatMap (fun k' => keepCellClauses t k')
    | halt => (Finset.univ : Finset tm.K).toList.flatMap (fun k' => keepCellClauses t k')

/-! ## (2) The combined-space cell-transition assembly -/

variable (tm S) in
/-- The **cell-transition clauses** over `t → t+1`: over every continuation token, guard the
left-lifted cell gadget by that token's `contVar` at `t`, and append. `conditionOn` selects the
active token's gadget; `liftClausesL` embeds the main-space gadget into the combined space. -/
noncomputable def cellTransClauses (t : Fin T) :
    List (Clause (fullNumVars tm T S (ContTok tm))) :=
  (Finset.univ : Finset (ContTok tm)).toList.flatMap
    (fun cont => conditionOn (contVar (V := ContTok tm) (Fin.castSucc t) cont)
      (liftClausesL (cellGadgetFor cont t)))

/-! ## (3) Dispatch extraction: drop to the active token's gadget on the main block -/

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Dispatch extraction.** Under full consistency, satisfying `cellTransClauses` forces the
**active** continuation's cell gadget (for `cont₀ = readContC assign (castSucc t)`) to be satisfied
on the main block `mainAssign assign`. -/
theorem satisfiesAll_cellGadgetFor_active {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {t : Fin T}
    (h : satisfiesAll assign (cellTransClauses tm S t)) :
    satisfiesAll (mainAssign assign)
      (cellGadgetFor (readContC assign (Fin.castSucc t)) t) := by
  set cont₀ := readContC assign (Fin.castSucc t) with hcont₀
  -- the active token's `contVar` is true (one-hot register: the read value's coordinate)
  have hregcons : RegConsistent (contAssign assign) := ((fullConsistent_iff assign).1 hcons).2
  have hvar : assign (contVar (V := ContTok tm) (Fin.castSucc t) cont₀) = true := by
    have hself := readReg_self_true hregcons (Fin.castSucc t)
    rw [contAssign_contVar] at hself
    rw [hcont₀, readContC]; exact hself
  -- pull the active token's guarded+lifted summand out of the `flatMap`
  rw [cellTransClauses] at h
  have hsummand : satisfiesAll assign
      (conditionOn (contVar (V := ContTok tm) (Fin.castSucc t) cont₀)
        (liftClausesL (cellGadgetFor cont₀ t))) :=
    satisfiesAll_flatMap_of_mem
      (g := fun cont => conditionOn (contVar (V := ContTok tm) (Fin.castSucc t) cont)
        (liftClausesL (cellGadgetFor cont t)))
      (Finset.mem_toList.2 (Finset.mem_univ cont₀)) h
  -- unguard (the guard variable is true), then drop to the main block
  have hlift := conditionOn_spec assign _ _ hsummand hvar
  rw [satisfiesAll_liftClausesL] at hlift
  exact hlift

/-! ## (4) `readStack`-level correctness against `unifStep` -/

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Keep-all extraction.** If the main block satisfies `univ.toList.flatMap (keepCellClauses t)`,
then it satisfies `keepCellClauses t k'` for every stack `k'`. -/
theorem satisfiesAll_keepCellClauses_of_univ {a : Fin (numVars tm T S) → Bool} {t : Fin T}
    (h : satisfiesAll a
      ((Finset.univ : Finset tm.K).toList.flatMap (fun k' => keepCellClauses t k'))) (k' : tm.K) :
    satisfiesAll a (keepCellClauses (S := S) t k') :=
  satisfiesAll_flatMap_of_mem (Finset.mem_toList.2 (Finset.mem_univ k')) h

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Erase extraction.** If the main block satisfies
`(univ.erase k).toList.flatMap (keepCellClauses t)`, then it satisfies `keepCellClauses t k'` for
every `k' ≠ k`. -/
theorem satisfiesAll_keepCellClauses_of_erase {a : Fin (numVars tm T S) → Bool} {t : Fin T}
    {k : tm.K}
    (h : satisfiesAll a
      (((Finset.univ : Finset tm.K).erase k).toList.flatMap (fun k' => keepCellClauses t k')))
    {k' : tm.K} (hk' : k' ≠ k) :
    satisfiesAll a (keepCellClauses (S := S) t k') :=
  satisfiesAll_flatMap_of_mem
    (Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hk', Finset.mem_univ k'⟩)) h

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Cell-transition correctness.** Under full consistency, the per-stack stack-shape hypothesis,
and the per-stack room hypothesis (`length < S`) at the time-`t` cells, the cell-transition clauses
force, for *every* stack `k'`, `readStack (t+1) k'` to be the **stack component** at `k'` of one
`unifStep` from the read continuation, state, and stacks at `t`. -/
theorem cellTransClauses_spec {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {t : Fin T}
    (h : satisfiesAll assign (cellTransClauses tm S t))
    (hshape : ∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) (Fin.castSucc t) k i)
      (readStack (mainAssign assign) (Fin.castSucc t) k))
    (hlen : ∀ k, (readStack (mainAssign assign) (Fin.castSucc t) k).length < S) (k' : tm.K) :
    readStack (mainAssign assign) (Fin.succ t) k' =
      (unifStep tm.m (contToUnif (readContC assign (Fin.castSucc t)),
        readState (mainAssign assign) (Fin.castSucc t),
        fun k => readStack (mainAssign assign) (Fin.castSucc t) k)).2.2 k' := by
  -- the main block is consistent (from full consistency) and the active gadget holds on it
  have hmaincons : Consistent (mainAssign assign) := ((fullConsistent_iff assign).1 hcons).1
  have hgad := satisfiesAll_cellGadgetFor_active hcons h
  -- case on the active continuation token and its head statement; match `unifStep`'s stack arm
  set cont₀ := readContC assign (Fin.castSucc t) with hcont₀
  clear hcont₀
  match cont₀, hgad with
  | none, hgad =>
    rw [cellGadgetFor] at hgad
    rw [keepCell_readStack hmaincons (satisfiesAll_keepCellClauses_of_univ hgad k')]; rfl
  | some ⟨push k f q', hq⟩, hgad =>
    rw [cellGadgetFor, satisfiesAll_append] at hgad
    by_cases hk : k' = k
    · subst hk
      rw [pushCell_readStack hmaincons hgad.1 (hshape k') (hlen k')]
      simp only [contToUnif_some, unifStep_push, Function.update_self]
    · rw [keepCell_readStack hmaincons (satisfiesAll_keepCellClauses_of_erase hgad.2 hk)]
      simp only [contToUnif_some, unifStep_push, Function.update_of_ne hk]
  | some ⟨pop k f q', hq⟩, hgad =>
    rw [cellGadgetFor, satisfiesAll_append] at hgad
    by_cases hk : k' = k
    · subst hk
      rw [popCell_readStack hmaincons hgad.1 (hshape k')]
      simp only [contToUnif_some, unifStep_pop, Function.update_self]
    · rw [keepCell_readStack hmaincons (satisfiesAll_keepCellClauses_of_erase hgad.2 hk)]
      simp only [contToUnif_some, unifStep_pop, Function.update_of_ne hk]
  | some ⟨peek k f q', hq⟩, hgad =>
    rw [cellGadgetFor] at hgad
    rw [keepCell_readStack hmaincons (satisfiesAll_keepCellClauses_of_univ hgad k')]; rfl
  | some ⟨load a q', hq⟩, hgad =>
    rw [cellGadgetFor] at hgad
    rw [keepCell_readStack hmaincons (satisfiesAll_keepCellClauses_of_univ hgad k')]; rfl
  | some ⟨branch g q₁ q₂, hq⟩, hgad =>
    rw [cellGadgetFor] at hgad
    rw [keepCell_readStack hmaincons (satisfiesAll_keepCellClauses_of_univ hgad k')]; rfl
  | some ⟨goto g, hq⟩, hgad =>
    rw [cellGadgetFor] at hgad
    rw [keepCell_readStack hmaincons (satisfiesAll_keepCellClauses_of_univ hgad k')]; rfl
  | some ⟨halt, hq⟩, hgad =>
    rw [cellGadgetFor] at hgad
    rw [keepCell_readStack hmaincons (satisfiesAll_keepCellClauses_of_univ hgad k')]; rfl

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The cell-transition clauses force `readStack (t+1) k'` to be `unifStep`'s stack component at `k'`.
example {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {t : Fin T}
    (h : satisfiesAll assign (cellTransClauses tm S t))
    (hshape : ∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) (Fin.castSucc t) k i)
      (readStack (mainAssign assign) (Fin.castSucc t) k))
    (hlen : ∀ k, (readStack (mainAssign assign) (Fin.castSucc t) k).length < S) (k' : tm.K) :
    readStack (mainAssign assign) (Fin.succ t) k' =
      (unifStep tm.m (contToUnif (readContC assign (Fin.castSucc t)),
        readState (mainAssign assign) (Fin.castSucc t),
        fun k => readStack (mainAssign assign) (Fin.castSucc t) k)).2.2 k' :=
  cellTransClauses_spec hcons h hshape hlen k'

end Examples

end CombinedTableau

end DeepWiki
