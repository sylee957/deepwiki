import DeepWiki.NetworkCalculus.UnifTransition
import DeepWiki.NetworkCalculus.UnifSimulation

/-!
# Combined accept-configuration clause for the unified (main ⊕ continuation) tableau

Layer 3c-v: the **final-time accept clauses** of the combined variable space
`CombinedTableau`, the exact mirror of the init clauses (`CombinedInit.lean`) but at
`Fin.last T` for the canonical halt config `haltList tm acceptOutput`.

* `TableauSchema.haltClauses tm T S acceptOutput` — the main-block unit clauses pinning the
  time-`last` configuration to `haltList tm acceptOutput`: label `none` (halted), state
  `tm.initialState`, every cell `((haltList tm acceptOutput).stk k)[i]?` (so the output stack
  `k₁` is loaded, every other stack empty); `haltClauses_spec` reads it back.
* `acceptClausesC tm T S acceptOutput` — the lifted main accept clauses appended to ONE unit
  clause pinning the continuation register at time `last` to the halted token `none`.
* `acceptClausesC_readUnif` — the **payoff**: `readUnif assign last = unifOfCfg tm (haltList tm
  acceptOutput)`, composing the continuation read (`= contOfLabel tm.m none = none`, the halted
  token) with the main configuration read (`= haltList tm acceptOutput`).

Pure **composition / mirroring** of the init clauses: `satisfiesAll_append`,
`satisfiesAll_liftClausesL`, `fullConsistent_iff`, `readReg_eq`, and the readback API; the one
genuinely-different bit is `(haltList …).l = none`, so the continuation is the halted token and
`contOfLabel tm.m none = none`.

## Deferred

The full formula assembly, `Satisfiable ⟺ accepts`, the poly-size bound, the verifier-input /
certificate encoding, and the final `cookLevin` reduction discharge are **later** layers.
-/

open Turing

namespace DeepWiki

namespace TableauSchema

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

open BooleanConstraints

variable {tm : FinTM2} {T S : ℕ} [∀ k, Fintype (tm.Γ k)]

/-! ## (1) The halt-config main clauses (mirror of `initClauses`) -/

variable (tm T S) in
/-- The **halt clauses**: unit clauses pinning the time-`last` configuration to
`haltList tm acceptOutput` — label `none`, state `tm.initialState`, and every cell
`((haltList tm acceptOutput).stk k)[i]?`. Mirror of `initClauses` at `Fin.last T`. -/
noncomputable def haltClauses (acceptOutput : List (tm.Γ tm.k₁)) :
    List (Clause (numVars tm T S)) :=
  [(coordVar (labelCoord (Fin.last T) (none : Option tm.Λ)), true)]
    :: [(coordVar (stateCoord (Fin.last T) tm.initialState), true)]
    :: ((Finset.univ : Finset tm.K).toList.flatMap
        (fun k => (Finset.univ : Finset (Fin S)).toList.map
          (fun i => [(coordVar
            (cellCoord (Fin.last T) k i (((haltList tm acceptOutput).stk k)[(i : ℕ)]?)),
              true)])))

/-- A satisfying assignment forces each cell coordinate of the halt clauses to the `haltList`
value at `(last, k, i)`. -/
theorem haltClauses_cell_true {assign : Fin (numVars tm T S) → Bool}
    {acceptOutput : List (tm.Γ tm.k₁)}
    (h : satisfiesAll assign (haltClauses tm T S acceptOutput)) (k : tm.K) (i : Fin S) :
    assign (coordVar
        (cellCoord (Fin.last T) k i (((haltList tm acceptOutput).stk k)[(i : ℕ)]?)))
      = true := by
  rw [haltClauses, satisfiesAll_cons, satisfiesAll_cons] at h
  obtain ⟨_, _, hcells⟩ := h
  rw [List.flatMap_def, satisfiesAll_flatten] at hcells
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index] at hcells
  have hk := hcells _ k rfl
  simp only [satisfiesAll, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index] at hk
  have hi := hk _ i rfl
  exact unitClause_sat (by
    rw [satisfiesAll]; intro c hc; rw [List.mem_singleton] at hc; subst hc; exact hi)

section Encode

variable [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Halt-clause correctness.** A consistent satisfying assignment reads its time-`last`
configuration back as `haltList tm acceptOutput`, provided the output fits in `S`. Mirror of
`initClauses_spec`. -/
theorem haltClauses_spec {assign : Fin (numVars tm T S) → Bool}
    {acceptOutput : List (tm.Γ tm.k₁)}
    (hsat : satisfiesAll assign (haltClauses tm T S acceptOutput)) (hcons : Consistent assign)
    (hSout : acceptOutput.length ≤ S) :
    readConfig assign (Fin.last T) = haltList tm acceptOutput := by
  -- the label and state unit clauses
  rw [haltClauses, satisfiesAll_cons, satisfiesAll_cons] at hsat
  obtain ⟨hlabel, hstate, _⟩ := hsat
  have hl : assign (coordVar (labelCoord (Fin.last T) (none : Option tm.Λ))) = true :=
    unitClause_sat (by rw [satisfiesAll]; intro c hc; rw [List.mem_singleton] at hc; subst hc
                       exact hlabel)
  have hs : assign (coordVar (stateCoord (Fin.last T) tm.initialState)) = true :=
    unitClause_sat (by rw [satisfiesAll]; intro c hc; rw [List.mem_singleton] at hc; subst hc
                       exact hstate)
  -- restore the full satisfaction for the cell extraction
  have hsat' : satisfiesAll assign (haltClauses tm T S acceptOutput) := by
    rw [haltClauses, satisfiesAll_cons, satisfiesAll_cons]; exact ⟨hlabel, hstate, by assumption⟩
  -- per-stack length bound from the output bound (`haltList` loads `acceptOutput` on `k₁`,
  -- `[]` elsewhere)
  have hSk : ∀ k, ((haltList tm acceptOutput).stk k).length ≤ S := by
    intro k
    unfold haltList
    dsimp only
    by_cases hk : k = tm.k₁
    · subst hk; simpa using hSout
    · rw [dif_neg hk]; simp
  -- assemble the three readbacks: equate the three fields of the (structure-`mk`) `readConfig`
  show Turing.TM2.Cfg.mk (readLabel assign (Fin.last T)) (readState assign (Fin.last T))
      (fun k => readStack assign (Fin.last T) k) = haltList tm acceptOutput
  rw [readLabel_eq hcons hl, readState_eq hcons hs]
  have hstk : (fun k => readStack (S := S) assign (Fin.last T) k)
      = (haltList tm acceptOutput).stk := by
    funext k
    -- reconstruct stack `k` from the per-cell readbacks forced by the halt clauses
    have hcellread : (fun i : Fin S => readCell assign (Fin.last T) k i)
        = (fun i : Fin S => ((haltList tm acceptOutput).stk k)[(i : ℕ)]?) := by
      funext i
      exact readCell_eq hcons (haltClauses_cell_true hsat' k i)
    rw [readStack, hcellread, ofFn_getElem?_eq _ S (hSk k),
      reduceOption_map_some_append_replicate]
  rw [hstk]
  -- the label and state fields of `haltList` are `none` and `tm.initialState`
  rfl

end Encode

end TableauSchema

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-! ## (2) The combined accept clauses (mirror of `initClausesC`) -/

variable (tm T S) in
/-- The **combined accept clauses**: the left-lifted main halt clauses (pinning the time-`last`
configuration to `haltList tm acceptOutput`) appended to ONE unit clause pinning the
continuation register at time `last` to the halted token `none`. Mirror of `initClausesC`. -/
noncomputable def acceptClausesC (acceptOutput : List (tm.Γ tm.k₁)) :
    List (Clause (fullNumVars tm T S (ContTok tm))) :=
  liftClausesL (haltClauses tm T S acceptOutput) ++
    [[(contVar (tm := tm) (S := S) (Fin.last T) (none : ContTok tm), true)]]

/-! ## (3) The continuation read at time `last` -/

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Continuation at `last`.** Under full consistency, the cont unit clause forces the
time-`last` continuation read to the halted token `none`. Mirror of `initClausesC_readContC`. -/
theorem acceptClausesC_readContC {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign)
    {acceptOutput : List (tm.Γ tm.k₁)}
    (hsat : satisfiesAll assign (acceptClausesC tm T S acceptOutput)) :
    readContC assign (Fin.last T) = (none : ContTok tm) := by
  -- the register block is consistent on the continuation restriction
  have hreg : RegConsistent (contAssign assign) := ((fullConsistent_iff assign).1 hcons).2
  -- split off the cont unit clause
  have hsplit := (satisfiesAll_append assign _ _).mp hsat
  -- the cont coordinate variable is forced true
  have hv : assign (contVar (tm := tm) (S := S) (Fin.last T) (none : ContTok tm)) = true :=
    unitClause_sat hsplit.2
  -- read it back through the register restriction
  rw [readContC]
  refine readReg_eq hreg ?_
  rw [contAssign_contVar]
  exact hv

/-! ## (4) The main configuration read at time `last` -/

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Configuration at `last`.** Under full consistency, the lifted main halt clauses force the
time-`last` main configuration read to `haltList tm acceptOutput` (output fitting in `S`). Mirror
of `initClausesC_readConfig`. -/
theorem acceptClausesC_readConfig {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign)
    {acceptOutput : List (tm.Γ tm.k₁)} (hSout : acceptOutput.length ≤ S)
    (hsat : satisfiesAll assign (acceptClausesC tm T S acceptOutput)) :
    readConfig (mainAssign assign) (Fin.last T) = haltList tm acceptOutput := by
  -- the main block is consistent on the main restriction
  have hmcons : Consistent (mainAssign assign) := ((fullConsistent_iff assign).1 hcons).1
  -- split off the lifted main halt clauses and drop them to the main restriction
  have hsplit := (satisfiesAll_append assign _ _).mp hsat
  have hmain : satisfiesAll (mainAssign assign) (haltClauses tm T S acceptOutput) :=
    (satisfiesAll_liftClausesL assign (haltClauses tm T S acceptOutput)).1 hsplit.1
  exact haltClauses_spec hmain hmcons hSout

/-! ## (5) The unified read at time `last` -/

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Accept at `last` (the payoff).** Under full consistency, a satisfying assignment to the
combined accept clauses reads back the unified halt state: `readUnif assign last = unifOfCfg tm
(haltList tm acceptOutput)`. Composes the continuation read (`= contOfLabel tm.m none = none`,
the halted token) with the main configuration read (`= haltList tm acceptOutput`). Mirror of
`initClausesC_readUnif`. -/
theorem acceptClausesC_readUnif {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign)
    {acceptOutput : List (tm.Γ tm.k₁)} (hSout : acceptOutput.length ≤ S)
    (hsat : satisfiesAll assign (acceptClausesC tm T S acceptOutput)) :
    readUnif assign (Fin.last T) = unifOfCfg tm (haltList tm acceptOutput) := by
  have hcont := acceptClausesC_readContC hcons hsat
  have hcfg := acceptClausesC_readConfig hcons hSout hsat
  -- reassemble the `UnifState` triple componentwise
  rw [unifOfCfg_eq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- continuation: read = none (halted token) = contOfLabel tm.m (haltList …).l
    rw [readUnif_fst, hcont, contToUnif_none]
    show (none : Option _) = contOfLabel tm.m (haltList tm acceptOutput).l
    have hl : (haltList tm acceptOutput).l = none := rfl
    rw [hl, contOfLabel_none]
  · -- state: from the main configuration read
    rw [readUnif_snd_fst]
    show readState (mainAssign assign) (Fin.last T) = (haltList tm acceptOutput).var
    rw [show readState (mainAssign assign) (Fin.last T)
          = (readConfig (mainAssign assign) (Fin.last T)).var from rfl, hcfg]
  · -- stacks: from the main configuration read
    rw [readUnif_snd_snd]
    show (fun k => readStack (mainAssign assign) (Fin.last T) k) = (haltList tm acceptOutput).stk
    funext k
    rw [show readStack (mainAssign assign) (Fin.last T) k
          = (readConfig (mainAssign assign) (Fin.last T)).stk k from rfl, hcfg]

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The combined accept clauses read back the unified halt state at time `last`.
example {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign)
    {acceptOutput : List (tm.Γ tm.k₁)} (hSout : acceptOutput.length ≤ S)
    (hsat : satisfiesAll assign (acceptClausesC tm T S acceptOutput)) :
    readUnif assign (Fin.last T) = unifOfCfg tm (haltList tm acceptOutput) :=
  acceptClausesC_readUnif hcons hSout hsat

-- The continuation read at `last` is the halted token `none`.
example {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign)
    {acceptOutput : List (tm.Γ tm.k₁)}
    (hsat : satisfiesAll assign (acceptClausesC tm T S acceptOutput)) :
    contToUnif (readContC assign (Fin.last T))
      = (none : Option (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)) := by
  rw [acceptClausesC_readContC hcons hsat, contToUnif_none]

end Examples

end CombinedTableau

end DeepWiki
