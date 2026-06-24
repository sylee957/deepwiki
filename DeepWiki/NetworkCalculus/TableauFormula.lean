import DeepWiki.NetworkCalculus.SpaceBound
import DeepWiki.NetworkCalculus.CombinedAccept
import DeepWiki.NetworkCalculus.UnifSimulationConverse

/-!
# The full Cook- and Levin-style tableau formula and its decode direction

Layer 3d: assemble the four already-proved clause families — consistency
(`fullConsistencyClauses`), init (`initClausesC`), per-time transitions (`unifTransClauses`,
flat-mapped over `Fin T`), and accept (`acceptClausesC`) — into one `CnfFormula`
`tableauFormula`, and prove the **decode direction**: a satisfying assignment forces the
machine to accept.

* `tableauFormula tm T S input acceptOutput hS0` — the combined CNF formula.
* `tm2Trace_halt_le` — the halt time of a uniform `T`-step halt is `≤ T` (the bound the bare
  converse `unifStep_halts_imp_tm2_halts` does not carry).
* `tableauFormula_sat_imp_accepts` — `Satisfiable (tableauFormula …) → AcceptsWithin tm input
  (some acceptOutput) T`. Pure composition: `eval_iff_satisfiesAll` + `satisfiesAll_append`
  split the formula, `initClausesC_readUnif`/`initClausesC_isStackShape`/
  `readUnif_last_spaceBounded`/`acceptClausesC_readUnif` decode the readback chain, and
  `tm2Trace_halt_le ∘ unifStep_halts_imp_tm2_halts` lands the bounded trace.

## Deferred

The **encode** direction (`AcceptsWithin → Satisfiable`, the witness-trace construction), the
full `⟺`, the poly-size bound, and the final `cookLevin` discharge are **later** layers.
-/

open Turing

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep CnfFormula

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-! ## (1) The combined tableau formula -/

variable (tm T S) in
/-- The **full tableau formula**: consistency, init, the flat-mapped per-time transition, and
accept clause families concatenated into one `CnfFormula` over the combined variable space. -/
noncomputable def tableauFormula (input : List (tm.Γ tm.k₀))
    (acceptOutput : List (tm.Γ tm.k₁)) (hS0 : 0 < S) : CnfFormula :=
  ⟨fullNumVars tm T S (ContTok tm),
    fullConsistencyClauses tm T S (ContTok tm)
      ++ initClausesC tm T S input
      ++ ((Finset.univ : Finset (Fin T)).toList.flatMap (fun t => unifTransClauses tm S t hS0))
      ++ acceptClausesC tm T S acceptOutput⟩

/-! ## (2) The halt-time bound for a uniform `T`-step halt -/

omit [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Halt-time bound.** If iterating `unifStep` for exactly `T` steps from `initUnif tm input`
reaches the encoding of a halt config `c` (`c.l = none`), then any trace step `k` landing on
`c` satisfies `k ≤ T`: were `T < k`, the trace would still be running at step `T` (a `some`
labelled config), but the uniform readback at any time `≥ T` is the halted fixed point
(`.1 = none`), contradicting `contOfLabel (some _) = some _`. -/
theorem tm2Trace_halt_le {input : List (tm.Γ tm.k₀)} {c : tm.Cfg}
    (hhalt : (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm c) (hc : c.l = none)
    {k : ℕ} (hk : tm2Trace tm input k = some c) : k ≤ T := by
  by_contra hlt
  push Not at hlt
  -- The reached uniform state is halted at time `T`.
  have hhaltT : (unifStep tm.m)^[T] (initUnif tm input) = (none, c.var, c.stk) := by
    rw [hhalt, unifOfCfg_eq, hc, contOfLabel_none]
  -- Since `T < k` and the trace is `some c` at `k`, it is `some (running config)` at `T`.
  have hT : ∃ cT, tm2Trace tm input T = some cT ∧ cT.l ≠ none := by
    by_contra hcon
    push Not at hcon
    -- Either the trace is `none` at `T`, or it is `some cT` with `cT.l = none`.
    cases hTval : tm2Trace tm input T with
    | none =>
      -- A `none` at `T` stays `none`, contradicting `some c` at `k > T`.
      have := traceFrom_none_of_le (f := tm.step) (c₀ := initList tm input) hTval k (le_of_lt hlt)
      rw [← tm2Trace] at this
      rw [this] at hk; exact absurd hk.symm (Option.some_ne_none c)
    | some cT =>
      -- A halted `some cT` (`cT.l = none`) dies at `T+1` and stays `none`, contradiction.
      have hcTl : cT.l = none := hcon cT hTval
      have hstep : tm.step cT = none := by
        by_contra hsn
        obtain ⟨c', hc'⟩ := Option.ne_none_iff_exists'.mp hsn
        obtain ⟨l, hl, _⟩ := exists_label_of_step cT c' hc'
        rw [hcTl] at hl; exact absurd hl.symm (Option.some_ne_none l)
      have hnone : tm2Trace tm input (T + 1) = none := by
        rw [tm2Trace, traceFrom_halt (by rw [← tm2Trace]; exact hTval) hstep]
      have := traceFrom_none_of_le (f := tm.step) (c₀ := initList tm input)
        (by rw [← tm2Trace]; exact hnone) k (by omega)
      rw [← tm2Trace] at this
      rw [this] at hk; exact absurd hk.symm (Option.some_ne_none c)
  -- The running config at `T` needs `≥ T` unif fuel, but the readback at `≥ T` is halted.
  obtain ⟨cT, hTval, hcTl⟩ := hT
  obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp hcTl
  obtain ⟨n, hnT, hn⟩ := exists_unifStep_iterate_tm2Trace_ge input T cT hTval
  have hnhalt : (unifStep tm.m)^[n] (initUnif tm input) = (none, c.var, c.stk) :=
    unifStep_iterate_eq_of_ge tm.m hhaltT hnT
  rw [hn, unifOfCfg_eq, hl, contOfLabel_some] at hnhalt
  exact absurd (congrArg Prod.fst hnhalt) (Option.some_ne_none _)

/-! ## (3) The decode direction: satisfiability forces acceptance -/

/-- **Decode direction.** Under the structural space bound `hSpace` and the input/output size
bounds, a satisfying assignment of `tableauFormula` forces the machine to accept `input` with
`acceptOutput` within `T` steps. Pure composition: split the formula with
`eval_iff_satisfiesAll` + `satisfiesAll_append`, decode the readback chain with
`initClausesC_readUnif`/`initClausesC_isStackShape`/`readUnif_last_spaceBounded`/
`acceptClausesC_readUnif`, then land the bounded trace with `unifStep_halts_imp_tm2_halts`
and `tm2Trace_halt_le`. -/
theorem tableauFormula_sat_imp_accepts {input : List (tm.Γ tm.k₀)}
    {acceptOutput : List (tm.Γ tm.k₁)} {hS0 : 0 < S}
    (hSpace : ∀ k, ((initList tm input).stk k).length + T < S)
    (hSout : acceptOutput.length ≤ S) (hSin : input.length ≤ S)
    (hsat : Satisfiable (tableauFormula tm T S input acceptOutput hS0)) :
    AcceptsWithin tm input (some acceptOutput) T := by
  -- A satisfying assignment to the four concatenated clause families.
  obtain ⟨assign, hassign⟩ := hsat
  have hsa : satisfiesAll assign (tableauFormula tm T S input acceptOutput hS0).clauses :=
    (eval_iff_satisfiesAll assign _).mp hassign
  -- Peel `((consistency ++ init) ++ transitions) ++ accept`.
  simp only [tableauFormula] at hsa
  rw [satisfiesAll_append, satisfiesAll_append, satisfiesAll_append] at hsa
  obtain ⟨⟨⟨hcons, hinit⟩, htransFlat⟩, haccept⟩ := hsa
  -- `hcons` is full consistency.
  have hfc : FullConsistent assign := hcons
  -- The per-time transition satisfaction, indexed by `t : Fin T`.
  have htrans : ∀ t : Fin T, satisfiesAll assign (unifTransClauses tm S t hS0) := by
    intro t
    rw [List.flatMap_def, satisfiesAll_flatten] at htransFlat
    refine htransFlat (unifTransClauses tm S t hS0) ?_
    rw [List.mem_map]
    exact ⟨t, Finset.mem_toList.mpr (Finset.mem_univ t), rfl⟩
  -- Decode time `0`: the readback is the initial unified state.
  have hinit_unif : readUnif assign (0 : Fin (T + 1)) = unifOfCfg tm (initList tm input) :=
    initClausesC_readUnif hfc hSin hinit
  -- Decode the stack shape at time `0` (in the `⟨0, _⟩` form `readUnif_last_spaceBounded` wants).
  have hinit_shape : ∀ k, IsStackShape
      (fun i : Fin S => readCell (mainAssign assign) (⟨0, by omega⟩ : Fin (T + 1)) k i)
      (readStack (mainAssign assign) (⟨0, by omega⟩ : Fin (T + 1)) k) := by
    intro k
    have h := initClausesC_isStackShape hfc hSin hinit k
    -- `(0 : Fin (T+1)) = ⟨0, _⟩` definitionally.
    exact h
  -- Decode the final time: the readback is the `T`-fold uniform step of the initial readback.
  have hlast : readUnif assign (Fin.last T) = (unifStep tm.m)^[T] (readUnif assign 0) :=
    readUnif_last_spaceBounded hfc (hS0 := hS0) htrans hinit_unif hinit_shape hSpace
  -- Decode the accept clauses: the final readback is the unified halt state.
  have haccept_unif : readUnif assign (Fin.last T) = unifOfCfg tm (haltList tm acceptOutput) :=
    acceptClausesC_readUnif hfc hSout haccept
  -- Combine into a `T`-step uniform halt from the initial uniform state.
  have hhalt : (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm (haltList tm acceptOutput) := by
    rw [initUnif, ← hinit_unif, ← hlast, haccept_unif]
  -- The halt config is genuinely halted (`l = none`).
  have hcl : (haltList tm acceptOutput).l = none := rfl
  -- Converse simulation: the TM2 trace reaches the halt config at some step `k`.
  obtain ⟨k, hk⟩ := unifStep_halts_imp_tm2_halts tm input T
    (haltList tm acceptOutput) hhalt hcl
  -- That step is `≤ T` by the halt-time bound.
  refine ⟨k, tm2Trace_halt_le hhalt hcl hk, ?_⟩
  rw [hk]; rfl

/-! ## Sanity restatement (intent check against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- A satisfying assignment of the full tableau formula makes the machine accept within `T` steps.
example {input : List (tm.Γ tm.k₀)} {acceptOutput : List (tm.Γ tm.k₁)} {hS0 : 0 < S}
    (hSpace : ∀ k, ((initList tm input).stk k).length + T < S)
    (hSout : acceptOutput.length ≤ S) (hSin : input.length ≤ S)
    (hsat : Satisfiable (tableauFormula tm T S input acceptOutput hS0)) :
    AcceptsWithin tm input (some acceptOutput) T :=
  tableauFormula_sat_imp_accepts hSpace hSout hSin hsat

end Examples

end CombinedTableau

end DeepWiki
