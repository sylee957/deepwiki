import DeepWiki.NetworkCalculus.TableauFormulaEncode

/-!
# The structural `⟺` of the Cook- and Levin-style tableau formula

Layer 3f: the **structural biconditional** between satisfiability of `tableauFormula` and the
uniform `T`-step halt equality.

* `tableauFormula_sat_imp_halt` — the decode side stopped at the halt equality:
  `Satisfiable (tableauFormula …) → (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm
  (haltList tm acceptOutput)`.  This is `tableauFormula_sat_imp_accepts` *minus* its final
  converse-simulation step (`unifStep_halts_imp_tm2_halts` + `tm2Trace_halt_le`): the same
  `eval_iff_satisfiesAll`/`satisfiesAll_append`/`satisfiesAll_flatten` peel plus
  `initClausesC_readUnif`/`initClausesC_isStackShape`/`readUnif_last_spaceBounded`/
  `acceptClausesC_readUnif`, landing the halt equality directly.
* `tableauFormula_sat_iff_halt` — the headline `⟺`: forward is `tableauFormula_sat_imp_halt`,
  backward is `tableauFormula_accepts_imp_sat`.

## Deferred

Connecting the halt equality to `AcceptsWithin` (the small-step and big-step time-axis
relationship), the polynomial-size bound, and the final `cookLevin` reduction discharge
(verifier and certificate encoding) are **later** layers.
-/

open Turing

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep CnfFormula

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-! ## (1) The decode direction, stopped at the halt equality -/

/-- **Decode to halt.** Under the structural space bound `hSpace` and the input/output size
bounds, a satisfying assignment of `tableauFormula` forces the `T`-fold uniform step from
`initUnif tm input` to land on the encoded halt config.  This is the decode chain of
`tableauFormula_sat_imp_accepts` without the converse-simulation final step: split the formula
with `eval_iff_satisfiesAll` + `satisfiesAll_append`, decode the readback chain with
`initClausesC_readUnif`/`initClausesC_isStackShape`/`readUnif_last_spaceBounded`/
`acceptClausesC_readUnif`, and land the halt equality. -/
theorem tableauFormula_sat_imp_halt {input : List (tm.Γ tm.k₀)}
    {acceptOutput : List (tm.Γ tm.k₁)} {hS0 : 0 < S}
    (hSpace : ∀ k, ((initList tm input).stk k).length + T < S)
    (hSout : acceptOutput.length ≤ S) (hSin : input.length ≤ S)
    (hsat : Satisfiable (tableauFormula tm T S input acceptOutput hS0)) :
    (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm (haltList tm acceptOutput) := by
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
  rw [initUnif, ← hinit_unif, ← hlast, haccept_unif]

/-! ## (2) The structural biconditional -/

/-- **Structural `⟺`.** Under `0 < T`, the structural space bound `hSpace`, and the input/output
size bounds, `tableauFormula` is satisfiable iff the `T`-fold uniform step from `initUnif tm input`
lands on the encoded halt config.  Forward is `tableauFormula_sat_imp_halt`; backward is
`tableauFormula_accepts_imp_sat`. -/
theorem tableauFormula_sat_iff_halt {input : List (tm.Γ tm.k₀)}
    {acceptOutput : List (tm.Γ tm.k₁)} {hS0 : 0 < S} (hT : 0 < T)
    (hSpace : ∀ k, ((initList tm input).stk k).length + T < S)
    (hSout : acceptOutput.length ≤ S) (hSin : input.length ≤ S) :
    Satisfiable (tableauFormula tm T S input acceptOutput hS0) ↔
      (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm (haltList tm acceptOutput) :=
  ⟨tableauFormula_sat_imp_halt hSpace hSout hSin,
    tableauFormula_accepts_imp_sat hT hSpace⟩

/-! ## Sanity restatement (intent check against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The structural biconditional: satisfiability of the tableau formula matches the uniform halt.
example {input : List (tm.Γ tm.k₀)} {acceptOutput : List (tm.Γ tm.k₁)} {hS0 : 0 < S} (hT : 0 < T)
    (hSpace : ∀ k, ((initList tm input).stk k).length + T < S)
    (hSout : acceptOutput.length ≤ S) (hSin : input.length ≤ S) :
    Satisfiable (tableauFormula tm T S input acceptOutput hS0) ↔
      (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm (haltList tm acceptOutput) :=
  tableauFormula_sat_iff_halt hT hSpace hSout hSin

end Examples

end CombinedTableau

end DeepWiki
