import DeepWiki.NetworkCalculus.UnifTransition

/-!
# Encode direction for the Cook- and Levin-style transition clauses

Layer 3c-iv: the **encode (converse) direction** of the unified-tableau transition clauses — the
counterpart of the `readState`/`readStack`/`readContC`-level `_spec` decode lemmas of
`StateTransitionAssembly`/`CellTransitionAssembly`/`UnifTransition`.  Given a configuration trace
`cfgs` and a continuation trace `conts` that follow one `UnifSmallStep.unifStep` at `t`, the
combined encoding `CombinedTableau.encodeC cfgs conts` **satisfies** the transition clauses.

Mirrors `ContTransition.contTransClauses_satisfies` (the continuation encode direction) for the
state and cell sides:

* per-gadget (main space, `TableauReadback.encodeSeq cfgs`): `keepState_satisfies`,
  `loadState_satisfies`, `peekState_satisfies`; `keepCell_satisfies`, `pushCell_satisfies`,
  `popCell_satisfies` — each runs `BooleanConstraints.funClauses_satisfies`/`funClauses₂_satisfies`
  on the matching `encodeSeq_*Coord` eval lemmas (the converse of each `_readState`/`_readStack`
  decode proof);
* assembly (combined space, `encodeC cfgs conts`): `stateTransClauses_satisfies`,
  `cellTransClauses_satisfies` — `satisfiesAll` over the per-continuation `flatMap`, with the
  real continuation `conts t.castSucc` discharged by `conditionOn_of_satisfiesAll` +
  `satisfiesAll_liftClausesL` + the per-gadget `_satisfies`, and every other continuation token
  discharged vacuously by `conditionOn_of_false` (one-hot register: its `contVar` is `false`);
* combined: `unifTransClauses_satisfies` — `satisfiesAll_append` of `contTransClauses_satisfies`
  and the two assemblies.

The `hstep` hypotheses are the components of one `unifStep` read against `cfgs`/`conts`, matching
how `unifTransClauses_spec` reads `unifStep`'s components in the decode direction.

## Deferred

Only the transition encode-satisfies (per-gadget, assembly, combined).  Init- and accept- clause
encode-satisfies, the full per-time formula assembly, `Satisfiable ↔ accepts`, polynomial size,
and the `cookLevin` discharge are **later** layers.
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

/-! ## (1a) Per-gadget state encode-satisfies (main space, `encodeSeq cfgs`)

The converses of `keepState_readState`/`loadState_readState`/`peekState_readState`: each runs
`funClauses_satisfies`/`funClauses₂_satisfies` with the functional-consistency obligation
discharged by the `encodeSeq_stateCoord`/`encodeSeq_cellCoord` evaluation of `encodeSeq cfgs`. -/

/-- **Keep state, encode.** If the state is unchanged across the step
(`(cfgs t.succ).var = (cfgs t.castSucc).var`), `encodeSeq cfgs` satisfies `keepStateClauses`. -/
theorem keepState_satisfies (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin T)
    (hstate : (cfgs t.succ).var = (cfgs t.castSucc).var) :
    satisfiesAll (encodeSeq (S := S) cfgs) (keepStateClauses (T := T) (S := S) t) := by
  refine funClauses_satisfies _ _ _ _ (fun s hs => ?_)
  -- a true input pins `s = (cfgs t.castSucc).var`
  simp only [stateVar, encodeSeq_stateCoord, beq_iff_eq] at hs
  -- the output `state(succ, id s)` is true since the state is unchanged
  simp only [stateVar, id, encodeSeq_stateCoord, beq_iff_eq, hstate, hs]

/-- **Load state, encode.** If the state at `t+1` is `a` of the state at `t`
(`(cfgs t.succ).var = a (cfgs t.castSucc).var`), `encodeSeq cfgs` satisfies `loadStateClauses`. -/
theorem loadState_satisfies (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin T) (a : tm.σ → tm.σ)
    (hstate : (cfgs t.succ).var = a (cfgs t.castSucc).var) :
    satisfiesAll (encodeSeq (S := S) cfgs) (loadStateClauses (T := T) (S := S) t a) := by
  refine funClauses_satisfies _ _ _ _ (fun s hs => ?_)
  simp only [stateVar, encodeSeq_stateCoord, beq_iff_eq] at hs
  simp only [stateVar, encodeSeq_stateCoord, beq_iff_eq, hstate, hs]

/-- **Peek/pop state, encode.** If the state at `t+1` is `f` of the state at `t` and the top cell
of stack `k` (`(cfgs t.succ).var = f (cfgs t.castSucc).var (((cfgs t.castSucc).stk k)[0]?)`),
`encodeSeq cfgs` satisfies `peekStateClauses`. -/
theorem peekState_satisfies (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin T) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) (hS0 : 0 < S)
    (hstate : (cfgs t.succ).var
      = f (cfgs t.castSucc).var (((cfgs t.castSucc).stk k)[(0 : ℕ)]?)) :
    satisfiesAll (encodeSeq (S := S) cfgs) (peekStateClauses (T := T) (S := S) t k f hS0) := by
  refine funClauses₂_satisfies _ _ _ _ _ (fun s c hs hc => ?_)
  -- a true state input pins `s = (cfgs t.castSucc).var`
  simp only [stateVar, encodeSeq_stateCoord, beq_iff_eq] at hs
  -- a true cell input pins `c = ((cfgs t.castSucc).stk k)[0]?`
  simp only [encodeSeq_cellCoord, beq_iff_eq] at hc
  -- the output `state(succ, f s c)` is true via the peek/pop update
  simp only [stateVar, encodeSeq_stateCoord, beq_iff_eq, hstate, hs, hc]

/-! ## (1b) Per-gadget cell encode-satisfies (main space, `encodeSeq cfgs`)

The converses of `keepCell_readStack`/`pushCell_readStack`/`popCell_readStack` at the cell level:
each gadget's per-position `funClauses` is discharged from `encodeSeq_cellCoord`, given the matching
component of one stack step on `cfgs`. -/

/-- **Keep cell, encode.** If stack `k` is unchanged across the step (cell-for-cell:
`((cfgs t.succ).stk k)[i]? = ((cfgs t.castSucc).stk k)[i]?`), `encodeSeq cfgs` satisfies
`keepCellClauses`. -/
theorem keepCell_satisfies (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin T) (k : tm.K)
    (hcell : ∀ i : Fin S, ((cfgs t.succ).stk k)[(i : ℕ)]? = ((cfgs t.castSucc).stk k)[(i : ℕ)]?) :
    satisfiesAll (encodeSeq (S := S) cfgs) (keepCellClauses (S := S) t k) := by
  rw [keepCellClauses, List.flatMap_def, satisfiesAll_flatten]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
  rintro cs i rfl
  refine funClauses_satisfies _ _ _ _ (fun c hc => ?_)
  simp only [encodeSeq_cellCoord, beq_iff_eq] at hc
  simp only [id, encodeSeq_cellCoord, beq_iff_eq, hcell i, hc]

/-- **Pop cell, encode.** If stack `k` at `t+1` is shifted down (`((cfgs t.succ).stk k)[i]? =
((cfgs t.castSucc).stk k)[i+1]?` for `i+1 < S`) and emptied at the top (`= none` when `i+1 = S`),
`encodeSeq cfgs` satisfies `popCellClauses`. -/
theorem popCell_satisfies (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin T) (k : tm.K)
    (hshift : ∀ (i : Fin S), (i : ℕ) + 1 < S →
      ((cfgs t.succ).stk k)[(i : ℕ)]? = ((cfgs t.castSucc).stk k)[(i : ℕ) + 1]?)
    (htop : ∀ i : Fin S, (i : ℕ) + 1 = S → ((cfgs t.succ).stk k)[(i : ℕ)]? = none) :
    satisfiesAll (encodeSeq (S := S) cfgs) (popCellClauses (S := S) t k) := by
  rw [popCellClauses, List.flatMap_def, satisfiesAll_flatten]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
  rintro cs i rfl
  by_cases hi : (i : ℕ) + 1 < S
  · -- non-top position: a shift-down `funClauses`
    rw [dif_pos hi, popShiftClauses]
    refine funClauses_satisfies _ _ _ _ (fun c hc => ?_)
    simp only [encodeSeq_cellCoord, beq_iff_eq] at hc
    simp only [id, encodeSeq_cellCoord, beq_iff_eq, ← hshift i hi, hc]
  · -- top position: the unit clause forcing `cell(succ, i, none)` true
    rw [dif_neg hi]
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    -- the single literal `(cell(succ, i, none), true)` is satisfied since the slot is empty there
    have hnone : encodeSeq (S := S) cfgs (coordVar (cellCoord (Fin.succ t) k i none)) = true := by
      rw [encodeSeq_cellCoord, beq_iff_eq]; exact htop i (by omega)
    simpa only [CnfFormula.clauseSat, List.any_cons, List.any_nil, CnfFormula.litSat,
      Bool.or_false, beq_iff_eq] using hnone

/-- **Push cell, encode.** If stack `k` at `t+1` has new bottom `some (f (cfgs t.castSucc).var)`
(`((cfgs t.succ).stk k)[0]? = some (f (cfgs t.castSucc).var)` when `0 < S`) and is shifted up
(`((cfgs t.succ).stk k)[i+1]? = ((cfgs t.castSucc).stk k)[i]?` for `i+1 < S`), `encodeSeq cfgs`
satisfies `pushCellClauses`. -/
theorem pushCell_satisfies (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin T) (k : tm.K) (f : tm.σ → tm.Γ k)
    (hbot : 0 < S →
      ((cfgs t.succ).stk k)[(0 : ℕ)]? = some (f (cfgs t.castSucc).var))
    (hshift : ∀ (i : Fin S), (i : ℕ) + 1 < S →
      ((cfgs t.succ).stk k)[(i : ℕ) + 1]? = ((cfgs t.castSucc).stk k)[(i : ℕ)]?) :
    satisfiesAll (encodeSeq (S := S) cfgs) (pushCellClauses (S := S) t k f) := by
  rw [pushCellClauses, satisfiesAll_append]
  refine ⟨?_, ?_⟩
  · -- the new-bottom group (when `0 < S`)
    by_cases h0 : 0 < S
    · rw [dif_pos h0, pushBottomClauses]
      refine funClauses_satisfies _ _ _ _ (fun s hs => ?_)
      simp only [encodeSeq_stateCoord, beq_iff_eq] at hs
      simp only [encodeSeq_cellCoord, beq_iff_eq, hs, hbot h0]
    · rw [dif_neg h0]; exact satisfiesAll_nil _
  · -- the per-position shift-up groups
    rw [List.flatMap_def, satisfiesAll_flatten]
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
    rintro cs i rfl
    by_cases hi : (i : ℕ) + 1 < S
    · rw [dif_pos hi, pushShiftClauses]
      refine funClauses_satisfies _ _ _ _ (fun c hc => ?_)
      simp only [encodeSeq_cellCoord, beq_iff_eq] at hc
      simp only [id, encodeSeq_cellCoord, beq_iff_eq, hshift i hi, hc]
    · rw [dif_neg hi]; exact satisfiesAll_nil _

/-! ## (2a) One-hot dispatch helpers (combined space)

The combined encoding's `contVar` evaluates by the one-hot register: it is true exactly at the real
continuation `conts t.castSucc`.  This is what makes every off-continuation `conditionOn` summand
vacuous (`conditionOn_of_false`). -/

/-- **One-hot `contVar` evaluation.** `encodeC cfgs conts` at `contVar t.castSucc cont` is
`decide (cont = conts t.castSucc)`: it is `true` exactly on the real continuation. -/
theorem encodeC_contVar (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → ContTok tm)
    (t : Fin T) (cont : ContTok tm) :
    encodeC (S := S) cfgs conts (contVar (V := ContTok tm) (Fin.castSucc t) cont)
      = decide (cont = conts (Fin.castSucc t)) := by
  simp only [← contAssign_contVar, contAssign_encodeC, encodeReg_regVar]

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Per-continuation `flatMap` intro.** A combined assignment satisfies a per-continuation
`flatMap` of clause groups iff it satisfies the group for every continuation token. -/
theorem satisfiesAll_contFlatMap {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    {g : ContTok tm → List (Clause (fullNumVars tm T S (ContTok tm)))}
    (h : ∀ cont : ContTok tm, satisfiesAll assign (g cont)) :
    satisfiesAll assign ((Finset.univ : Finset (ContTok tm)).toList.flatMap g) := by
  rw [List.flatMap_def, satisfiesAll_flatten]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
  rintro cs cont rfl
  exact h cont

/-! ## (2b) The state-transition assembly encode-satisfies (combined space) -/

/-- **State-transition assembly, encode.** If the state at `t+1` is the state component of one
`unifStep` from the continuation, state, and stacks at `t` (read against `cfgs`/`conts`), then
`encodeC cfgs conts` satisfies `stateTransClauses`. -/
theorem stateTransClauses_satisfies (cfgs : Fin (T + 1) → tm.Cfg)
    (conts : Fin (T + 1) → ContTok tm) (t : Fin T) (hS0 : 0 < S)
    (hstate : (cfgs t.succ).var =
      (unifStep tm.m (contToUnif (conts t.castSucc), (cfgs t.castSucc).var,
        fun k => (cfgs t.castSucc).stk k)).2.1) :
    satisfiesAll (encodeC (S := S) cfgs conts) (stateTransClauses tm S t hS0) := by
  rw [stateTransClauses]
  refine satisfiesAll_contFlatMap (fun cont => ?_)
  by_cases hcont : cont = conts (Fin.castSucc t)
  · -- the real continuation: unguard, drop to the main block, apply the per-gadget `_satisfies`
    refine conditionOn_of_satisfiesAll _ _ _ ?_
    rw [satisfiesAll_liftClausesL]
    show satisfiesAll (mainAssign (encodeC (S := S) cfgs conts)) (stateGadgetFor cont t hS0)
    rw [mainAssign_encodeC, hcont]
    -- the gadget for the active token's constructor matches `unifStep`'s `σ` arm of `hstate`
    set cont₀ := conts (Fin.castSucc t) with hcont₀
    clear hcont₀ hcont
    match cont₀, hstate with
    | none, hstate =>
      rw [stateGadgetFor]
      exact keepState_satisfies cfgs t (by simpa [contToUnif] using hstate)
    | some ⟨push k f q', hq⟩, hstate =>
      rw [stateGadgetFor]
      exact keepState_satisfies cfgs t (by simpa using hstate)
    | some ⟨branch g q₁ q₂, hq⟩, hstate =>
      rw [stateGadgetFor]
      exact keepState_satisfies cfgs t (by simpa using hstate)
    | some ⟨goto g, hq⟩, hstate =>
      rw [stateGadgetFor]
      exact keepState_satisfies cfgs t (by simpa using hstate)
    | some ⟨halt, hq⟩, hstate =>
      rw [stateGadgetFor]
      exact keepState_satisfies cfgs t (by simpa using hstate)
    | some ⟨load a q', hq⟩, hstate =>
      rw [stateGadgetFor]
      exact loadState_satisfies cfgs t a (by simpa using hstate)
    | some ⟨peek k f q', hq⟩, hstate =>
      rw [stateGadgetFor]
      refine peekState_satisfies cfgs t k f hS0 ?_
      simpa [List.head?_eq_getElem?] using hstate
    | some ⟨pop k f q', hq⟩, hstate =>
      rw [stateGadgetFor]
      refine peekState_satisfies cfgs t k f hS0 ?_
      simpa [List.head?_eq_getElem?] using hstate
  · -- every other token: its `contVar` is `false`, so the guarded summand is vacuous
    refine conditionOn_of_false _ _ _ ?_
    rw [encodeC_contVar, decide_eq_false_iff_not]
    exact hcont

/-! ## (2c) The cell-transition assembly encode-satisfies (combined space)

The cell parallel of `stateTransClauses_satisfies`.  Per stack `k'` the gadget is either a
`keepCellClauses` (unchanged stacks), a `pushCellClauses` (the pushed stack), or a
`popCellClauses` (the popped stack).  The per-position `[i]?` facts each gadget needs are read off
the per-stack list equality `(cfgs t.succ).stk k' = (unifStep …).2.2 k'`. -/

/-- **Keep-all, encode helper.** If every stack `k'` is unchanged cell-for-cell, `encodeSeq cfgs`
satisfies `univ.toList.flatMap keepCellClauses`. -/
theorem satisfies_keepCellClauses_univ (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin T)
    (hcell : ∀ (k' : tm.K) (i : Fin S),
      ((cfgs t.succ).stk k')[(i : ℕ)]? = ((cfgs t.castSucc).stk k')[(i : ℕ)]?) :
    satisfiesAll (encodeSeq (S := S) cfgs)
      ((Finset.univ : Finset tm.K).toList.flatMap (fun k' => keepCellClauses t k')) := by
  rw [List.flatMap_def, satisfiesAll_flatten]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
  rintro cs k' rfl
  exact keepCell_satisfies cfgs t k' (hcell k')

/-- **Keep-erase, encode helper.** If every stack `k' ≠ k` is unchanged cell-for-cell,
`encodeSeq cfgs` satisfies `(univ.erase k).toList.flatMap keepCellClauses`. -/
theorem satisfies_keepCellClauses_erase (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin T) (k : tm.K)
    (hcell : ∀ (k' : tm.K), k' ≠ k → ∀ i : Fin S,
      ((cfgs t.succ).stk k')[(i : ℕ)]? = ((cfgs t.castSucc).stk k')[(i : ℕ)]?) :
    satisfiesAll (encodeSeq (S := S) cfgs)
      (((Finset.univ : Finset tm.K).erase k).toList.flatMap (fun k' => keepCellClauses t k')) := by
  rw [List.flatMap_def, satisfiesAll_flatten]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_erase, Finset.mem_univ, and_true,
    forall_exists_index, and_imp]
  rintro cs k' hk' rfl
  exact keepCell_satisfies cfgs t k' (hcell k' hk')

/-- **Cell-transition assembly, encode.** If every stack at `t+1` is the stack component of one
`unifStep` from the continuation, state, and stacks at `t` (read against `cfgs`/`conts`) and each
stack at `t` fits (`length < S`), then `encodeC cfgs conts` satisfies `cellTransClauses`. -/
theorem cellTransClauses_satisfies (cfgs : Fin (T + 1) → tm.Cfg)
    (conts : Fin (T + 1) → ContTok tm) (t : Fin T)
    (hcell : ∀ k', (cfgs t.succ).stk k' =
      (unifStep tm.m (contToUnif (conts t.castSucc), (cfgs t.castSucc).var,
        fun k => (cfgs t.castSucc).stk k)).2.2 k')
    (hlen : ∀ k, ((cfgs t.castSucc).stk k).length < S) :
    satisfiesAll (encodeC (S := S) cfgs conts) (cellTransClauses tm S t) := by
  rw [cellTransClauses]
  refine satisfiesAll_contFlatMap (fun cont => ?_)
  by_cases hcont : cont = conts (Fin.castSucc t)
  · -- the real continuation: unguard, drop to the main block, apply the per-gadget `_satisfies`
    refine conditionOn_of_satisfiesAll _ _ _ ?_
    rw [satisfiesAll_liftClausesL]
    show satisfiesAll (mainAssign (encodeC (S := S) cfgs conts)) (cellGadgetFor cont t)
    rw [mainAssign_encodeC, hcont]
    -- the gadget for the active token's constructor matches `unifStep`'s stack arm of `hcell`
    set cont₀ := conts (Fin.castSucc t) with hcont₀
    clear hcont₀ hcont
    match cont₀, hcell with
    | none, hcell =>
      rw [cellGadgetFor]
      exact satisfies_keepCellClauses_univ cfgs t (fun k' i => by
        have := hcell k'; simp only [contToUnif_none, unifStep_none] at this; rw [this])
    | some ⟨peek k f q', hq⟩, hcell =>
      rw [cellGadgetFor]
      exact satisfies_keepCellClauses_univ cfgs t (fun k' i => by
        have := hcell k'; simp only [contToUnif_some, unifStep_peek] at this; rw [this])
    | some ⟨load a q', hq⟩, hcell =>
      rw [cellGadgetFor]
      exact satisfies_keepCellClauses_univ cfgs t (fun k' i => by
        have := hcell k'; simp only [contToUnif_some, unifStep_load] at this; rw [this])
    | some ⟨branch g q₁ q₂, hq⟩, hcell =>
      rw [cellGadgetFor]
      exact satisfies_keepCellClauses_univ cfgs t (fun k' i => by
        have := hcell k'; simp only [contToUnif_some, unifStep_branch] at this; rw [this])
    | some ⟨goto g, hq⟩, hcell =>
      rw [cellGadgetFor]
      exact satisfies_keepCellClauses_univ cfgs t (fun k' i => by
        have := hcell k'; simp only [contToUnif_some, unifStep_goto] at this; rw [this])
    | some ⟨halt, hq⟩, hcell =>
      rw [cellGadgetFor]
      exact satisfies_keepCellClauses_univ cfgs t (fun k' i => by
        have := hcell k'; simp only [contToUnif_some, unifStep_halt] at this; rw [this])
    | some ⟨push k f q', hq⟩, hcell =>
      rw [cellGadgetFor, satisfiesAll_append]
      -- the pushed stack at `k`, then keep on every other stack
      have hk := hcell k
      simp only [contToUnif_some, unifStep_push, Function.update_self] at hk
      refine ⟨pushCell_satisfies cfgs t k f (fun _ => by rw [hk]; simp)
        (fun i hi => by rw [hk, List.getElem?_cons_succ]), ?_⟩
      refine satisfies_keepCellClauses_erase cfgs t k (fun k' hk' i => ?_)
      have := hcell k'
      simp only [contToUnif_some, unifStep_push, Function.update_of_ne hk'] at this
      rw [this]
    | some ⟨pop k f q', hq⟩, hcell =>
      rw [cellGadgetFor, satisfiesAll_append]
      -- the popped stack at `k`, then keep on every other stack
      have hk := hcell k
      simp only [contToUnif_some, unifStep_pop, Function.update_self] at hk
      refine ⟨popCell_satisfies cfgs t k
        (fun i _ => by rw [hk]; cases h : (cfgs t.castSucc).stk k with
          | nil => simp | cons x xs => simp [List.getElem?_cons_succ])
        (fun i hi => by
          rw [hk]
          have hfit := hlen k
          have : ((cfgs t.castSucc).stk k).tail.length < S := lt_of_le_of_lt
            (by rw [List.length_tail]; omega) hfit
          rw [List.getElem?_eq_none_iff.2 (by omega)]), ?_⟩
      refine satisfies_keepCellClauses_erase cfgs t k (fun k' hk' i => ?_)
      have := hcell k'
      simp only [contToUnif_some, unifStep_pop, Function.update_of_ne hk'] at this
      rw [this]
  · -- every other token: its `contVar` is `false`, so the guarded summand is vacuous
    refine conditionOn_of_false _ _ _ ?_
    rw [encodeC_contVar, decide_eq_false_iff_not]
    exact hcont

/-! ## (3) The combined transition encode-satisfies

`unifTransClauses = contTransClauses ++ stateTransClauses ++ cellTransClauses`, so a single
`unifStep`-consistency hypothesis `hstep` (the unified readback of `cfgs`/`conts` at `t.succ` is one
`unifStep` from that at `t.castSucc`) feeds all three component encode-satisfies through
`satisfiesAll_append`.  The continuation component is recovered from `hstep.1` by
`contToUnif`-injectivity and the bridge `contToUnif_unifNextCont`. -/

omit [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- `contToUnif` (`Option.map Subtype.val`) is injective. -/
theorem contToUnif_injective : Function.Injective (contToUnif (tm := tm)) :=
  Option.map_injective Subtype.val_injective

/-- **Combined transition, encode.** If the unified readback of `cfgs`/`conts` at `t.succ` is one
`unifStep` from that at `t.castSucc` (`hstep`) and each stack at `t.castSucc` fits (`length < S`),
then `encodeC cfgs conts` satisfies the unified transition clauses `unifTransClauses`. -/
theorem unifTransClauses_satisfies (cfgs : Fin (T + 1) → tm.Cfg)
    (conts : Fin (T + 1) → ContTok tm) (t : Fin T) (hS0 : 0 < S)
    (hstep : (contToUnif (conts t.succ), (cfgs t.succ).var, fun k => (cfgs t.succ).stk k) =
      unifStep tm.m (contToUnif (conts t.castSucc), (cfgs t.castSucc).var,
        fun k => (cfgs t.castSucc).stk k))
    (hlen : ∀ k, ((cfgs t.castSucc).stk k).length < S) :
    satisfiesAll (encodeC (S := S) cfgs conts) (unifTransClauses tm S t hS0) := by
  -- the three `unifStep` components, read off `hstep`
  have hcontU : contToUnif (conts t.succ) =
      (unifStep tm.m (contToUnif (conts t.castSucc), (cfgs t.castSucc).var,
        fun k => (cfgs t.castSucc).stk k)).1 := congrArg Prod.fst hstep
  have hstate : (cfgs t.succ).var =
      (unifStep tm.m (contToUnif (conts t.castSucc), (cfgs t.castSucc).var,
        fun k => (cfgs t.castSucc).stk k)).2.1 := congrArg (Prod.fst ∘ Prod.snd) hstep
  have hcell : ∀ k', (cfgs t.succ).stk k' =
      (unifStep tm.m (contToUnif (conts t.castSucc), (cfgs t.castSucc).var,
        fun k => (cfgs t.castSucc).stk k)).2.2 k' :=
    fun k' => congrFun (congrArg (Prod.snd ∘ Prod.snd) hstep) k'
  -- the continuation component as `unifNextCont`, via `contToUnif`-injectivity + the bridge
  have hcont : conts t.succ = unifNextCont tm (conts t.castSucc) (cfgs t.castSucc).var := by
    apply contToUnif_injective
    rw [hcontU, contToUnif_unifNextCont]
  -- split the concatenation and discharge each family by its encode-satisfies
  rw [unifTransClauses, satisfiesAll_append, satisfiesAll_append]
  exact ⟨⟨contTransClauses_satisfies cfgs conts t hcont,
      stateTransClauses_satisfies cfgs conts t hS0 hstate⟩,
    cellTransClauses_satisfies cfgs conts t hcell hlen⟩

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The combined encoding of a `unifStep`-consistent trace satisfies the unified transition clauses.
example (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → ContTok tm) (t : Fin T) (hS0 : 0 < S)
    (hstep : (contToUnif (conts t.succ), (cfgs t.succ).var, fun k => (cfgs t.succ).stk k) =
      unifStep tm.m (contToUnif (conts t.castSucc), (cfgs t.castSucc).var,
        fun k => (cfgs t.castSucc).stk k))
    (hlen : ∀ k, ((cfgs t.castSucc).stk k).length < S) :
    satisfiesAll (encodeC (S := S) cfgs conts) (unifTransClauses tm S t hS0) :=
  unifTransClauses_satisfies cfgs conts t hS0 hstep hlen

-- The state assembly: the encoding of a `unifStep`-state-consistent trace satisfies it.
example (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → ContTok tm) (t : Fin T) (hS0 : 0 < S)
    (hstate : (cfgs t.succ).var =
      (unifStep tm.m (contToUnif (conts t.castSucc), (cfgs t.castSucc).var,
        fun k => (cfgs t.castSucc).stk k)).2.1) :
    satisfiesAll (encodeC (S := S) cfgs conts) (stateTransClauses tm S t hS0) :=
  stateTransClauses_satisfies cfgs conts t hS0 hstate

end Examples

end CombinedTableau

end DeepWiki
