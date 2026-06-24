import DeepWiki.NetworkCalculus.UnifTransition
import DeepWiki.NetworkCalculus.UnifSimulation

/-!
# Combined initial-configuration clause for the unified (main ⊕ continuation) tableau

Layer 3c-iv: the **time-`0` init clauses** of the combined variable space `CombinedTableau`,
pinning the start configuration of the unified small-step reading.

* `initClausesC tm T S input` — the lifted main-block init clauses (`TableauSchema.initClauses`,
  via `liftClausesL`) appended to ONE unit clause pinning the continuation register at time `0`
  to `some (tm.m tm.main)` (the program of the start label).
* `initClausesC_readContC` — the unit clause forces `readContC assign 0 = some ⟨tm.m tm.main, _⟩`.
* `initClausesC_readConfig` — the lifted part forces `readConfig (mainAssign assign) 0 =
  initList tm input` (via `TableauSchema.initClauses_spec`).
* `initClausesC_readUnif` — the **payoff**: `readUnif assign 0 = unifOfCfg tm (initList tm input)`,
  composing the two: the continuation matches `contOfLabel tm.m (some tm.main)`, and the
  state/stacks match `initList`'s.
* `initClausesC_isStackShape` — at time `0` the cells are in stack shape for the read stacks
  (the init cells are pinned to a genuine list's `getElem?`, a none-terminated prefix).

Pure **composition** of `satisfiesAll_append`, `satisfiesAll_liftClausesL`, `fullConsistent_iff`,
`initClauses_spec`, and `readReg_eq`.

## Deferred

The accept clauses, the space bound (`lenOk`), the full formula assembly, the verifier-input /
certificate encoding, and the final reduction correctness are **later** layers.
-/

open Turing

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-! ## (1) The combined init clauses -/

variable (tm T S) in
/-- The **combined init clauses**: the left-lifted main init clauses (pinning the time-`0`
configuration to `initList tm input`) appended to ONE unit clause pinning the continuation
register at time `0` to `some (tm.m tm.main)` (the program of the start label). -/
noncomputable def initClausesC (input : List (tm.Γ tm.k₀)) :
    List (Clause (fullNumVars tm T S (ContTok tm))) :=
  liftClausesL (initClauses tm T S input) ++
    [[(contVar (tm := tm) (S := S) (0 : Fin (T + 1))
        (some ⟨tm.m tm.main, program_mem_relevant tm tm.main⟩ : ContTok tm), true)]]

/-! ## (2) The continuation read at time `0` -/

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Continuation at `0`.** Under full consistency, the cont unit clause forces the time-`0`
continuation read to `some ⟨tm.m tm.main, _⟩` (the program of the start label). -/
theorem initClausesC_readContC {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign)
    {input : List (tm.Γ tm.k₀)}
    (hsat : satisfiesAll assign (initClausesC tm T S input)) :
    readContC assign (0 : Fin (T + 1)) =
      (some ⟨tm.m tm.main, program_mem_relevant tm tm.main⟩ : ContTok tm) := by
  -- the register block is consistent on the continuation restriction
  have hreg : RegConsistent (contAssign assign) := ((fullConsistent_iff assign).1 hcons).2
  -- split off the cont unit clause
  have hsplit := (satisfiesAll_append assign _ _).mp hsat
  -- the cont coordinate variable is forced true
  have hv : assign (contVar (tm := tm) (S := S) (0 : Fin (T + 1))
      (some ⟨tm.m tm.main, program_mem_relevant tm tm.main⟩ : ContTok tm)) = true :=
    unitClause_sat hsplit.2
  -- read it back through the register restriction
  rw [readContC]
  refine readReg_eq hreg ?_
  rw [contAssign_contVar]
  exact hv

/-! ## (3) The main configuration read at time `0` -/

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Configuration at `0`.** Under full consistency, the lifted main init clauses force the
time-`0` main configuration read to `initList tm input` (input fitting in `S`). -/
theorem initClausesC_readConfig {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign)
    {input : List (tm.Γ tm.k₀)} (hSinit : input.length ≤ S)
    (hsat : satisfiesAll assign (initClausesC tm T S input)) :
    readConfig (mainAssign assign) (0 : Fin (T + 1)) = initList tm input := by
  -- the main block is consistent on the main restriction
  have hmcons : Consistent (mainAssign assign) := ((fullConsistent_iff assign).1 hcons).1
  -- split off the lifted main init clauses and drop them to the main restriction
  have hsplit := (satisfiesAll_append assign _ _).mp hsat
  have hmain : satisfiesAll (mainAssign assign) (initClauses tm T S input) :=
    (satisfiesAll_liftClausesL assign (initClauses tm T S input)).1 hsplit.1
  exact initClauses_spec hmain hmcons hSinit

/-! ## (4) The unified read at time `0` -/

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Init at `0` (the payoff).** Under full consistency, a satisfying assignment to the combined
init clauses reads back the unified start state: `readUnif assign 0 = unifOfCfg tm (initList tm
input)`.  Composes the continuation read (`= contOfLabel tm.m (some tm.main)`) with the main
configuration read (`= initList tm input`). -/
theorem initClausesC_readUnif {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign)
    {input : List (tm.Γ tm.k₀)} (hSinit : input.length ≤ S)
    (hsat : satisfiesAll assign (initClausesC tm T S input)) :
    readUnif assign (0 : Fin (T + 1)) = unifOfCfg tm (initList tm input) := by
  have hcont := initClausesC_readContC hcons hsat
  have hcfg := initClausesC_readConfig hcons hSinit hsat
  -- reassemble the `UnifState` triple componentwise
  rw [unifOfCfg_eq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- continuation: read = some (tm.m main) = contOfLabel tm.m (initList …).l
    rw [readUnif_fst, hcont, contToUnif_some]
    show (some (tm.m tm.main) : Option _) = contOfLabel tm.m (initList tm input).l
    have hl : (initList tm input).l = some tm.main := rfl
    rw [hl, contOfLabel_some]
  · -- state: from the main configuration read
    rw [readUnif_snd_fst]
    show readState (mainAssign assign) (0 : Fin (T + 1)) = (initList tm input).var
    rw [show readState (mainAssign assign) (0 : Fin (T + 1))
          = (readConfig (mainAssign assign) (0 : Fin (T + 1))).var from rfl, hcfg]
  · -- stacks: from the main configuration read
    rw [readUnif_snd_snd]
    show (fun k => readStack (mainAssign assign) (0 : Fin (T + 1)) k) = (initList tm input).stk
    funext k
    rw [show readStack (mainAssign assign) (0 : Fin (T + 1)) k
          = (readConfig (mainAssign assign) (0 : Fin (T + 1))).stk k from rfl, hcfg]

/-! ## (5) Stack shape at time `0` -/

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Stack shape at `0`.** Under full consistency, the time-`0` cells are in stack shape for the
read stacks: the init clauses pin each cell to `initList`'s stack value (a genuine list of length
`≤ S`), so the cells are a none-terminated prefix. -/
theorem initClausesC_isStackShape {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign)
    {input : List (tm.Γ tm.k₀)} (hSinit : input.length ≤ S)
    (hsat : satisfiesAll assign (initClausesC tm T S input)) (k : tm.K) :
    IsStackShape (fun i : Fin S => readCell (mainAssign assign) (0 : Fin (T + 1)) k i)
      (readStack (mainAssign assign) (0 : Fin (T + 1)) k) := by
  -- the main block is consistent on the main restriction
  have hmcons : Consistent (mainAssign assign) := ((fullConsistent_iff assign).1 hcons).1
  -- drop the lifted main init clauses to the main restriction
  have hsplit := (satisfiesAll_append assign _ _).mp hsat
  have hmain : satisfiesAll (mainAssign assign) (initClauses tm T S input) :=
    (satisfiesAll_liftClausesL assign (initClauses tm T S input)).1 hsplit.1
  -- per-stack length bound from the input bound
  have hSk : ((initList tm input).stk k).length ≤ S := by
    unfold initList
    dsimp only
    by_cases hk : k = tm.k₀
    · subst hk; simpa using hSinit
    · rw [dif_neg hk]; simp
  -- each cell@0 reads back `initList`'s stack `getElem?`
  have hcell : (fun i : Fin S => readCell (mainAssign assign) (0 : Fin (T + 1)) k i)
      = (fun i : Fin S => ((initList tm input).stk k)[(i : ℕ)]?) := by
    funext i
    exact readCell_eq hmcons (initClauses_cell_true hmain k i)
  -- the read stack@0 equals `initList`'s stack `k`
  have hstk : readStack (mainAssign assign) (0 : Fin (T + 1)) k = (initList tm input).stk k := by
    rw [readStack, hcell, ofFn_getElem?_eq _ S hSk, reduceOption_map_some_append_replicate]
  -- `IsStackShape` is exactly `ofFn_getElem?_eq` of a list of length `≤ S`
  rw [IsStackShape, hcell, hstk]
  exact ofFn_getElem?_eq _ S hSk

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The combined init clauses read back the unified start state at time `0`.
example {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign)
    {input : List (tm.Γ tm.k₀)} (hSinit : input.length ≤ S)
    (hsat : satisfiesAll assign (initClausesC tm T S input)) :
    readUnif assign (0 : Fin (T + 1)) = unifOfCfg tm (initList tm input) :=
  initClausesC_readUnif hcons hSinit hsat

-- The continuation read at `0` is the program of the start label.
example {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign)
    {input : List (tm.Γ tm.k₀)}
    (hsat : satisfiesAll assign (initClausesC tm T S input)) :
    contToUnif (readContC assign (0 : Fin (T + 1))) = some (tm.m tm.main) := by
  rw [initClausesC_readContC hcons hsat, contToUnif_some]

end Examples

end CombinedTableau

end DeepWiki
