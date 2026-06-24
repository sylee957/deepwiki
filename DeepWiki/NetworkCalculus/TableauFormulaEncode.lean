import DeepWiki.NetworkCalculus.TableauFormula
import DeepWiki.NetworkCalculus.BoundaryEncode

/-!
# Encode direction of the Cook- and Levin-style tableau formula

Layer 3e (encode side): the **converse** of `tableauFormula_sat_imp_accepts`.  If iterating the
uniform small-step `UnifSmallStep.unifStep` for `T` steps from the initial uniform state reaches the
encoding of the halt config (the `hhalt` hypothesis the decode side *produces*), then the tableau
formula is `Satisfiable` — witnessed by `CombinedTableau.encodeC` of the real run.

* `traceState`/`contRun` — the witness run: the iterated uniform state, and the finite-token
  continuation trace mirroring it (`contRun_map`).
* `traceState_len` — the per-step stack-length bound feeding the space hypothesis.
* `cfgsW`/`contsW` — the configuration- and continuation- traces over `Fin (T + 1)`, with their
  boundary facts at `0` and `Fin.last T`.
* `tableauFormula_accepts_imp_sat` — the headline: `encodeC cfgsW contsW` satisfies the formula.

## Deferred

The full `⟺` (combining with `tableauFormula_sat_imp_accepts`), connecting `hhalt` to
`AcceptsWithin` (the small-step/big-step bound, already available via
`UnifSimulation.exists_unifStep_iterate_halt`), the polynomial-size bound, and the final
`cookLevin` reduction discharge are **later** layers.
-/

open Turing

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep CnfFormula
open Turing.TM2 Turing.TM2.Stmt

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

open scoped Classical

variable {tm : FinTM2} {T S : ℕ}

/-! ## (1) The witness run

These declarations build only on `unifStep`/`unifNextCont`/`initUnif` (which need just
`FinTM2.decidableEqK`, the local instance), so they are stated *without* the stack-alphabet
typeclass arguments; those re-enter at the assembly step (4), where the `_satisfies` lemmas need
them. -/

variable (tm) in
/-- The iterated uniform state at time `t`: `(unifStep tm.m)^[t] (initUnif tm input)`. -/
noncomputable def traceState (input : List (tm.Γ tm.k₀)) (t : ℕ) :
    UnifState tm.Γ tm.Λ tm.σ :=
  (unifStep tm.m)^[t] (initUnif tm input)

variable (tm) in
/-- The finite-token continuation run mirroring `traceState`: starts at the program of `tm.main`,
and steps by `unifNextCont` on the read state. -/
noncomputable def contRun (input : List (tm.Γ tm.k₀)) : ℕ → ContTok tm
  | 0 => some ⟨tm.m tm.main, program_mem_relevant tm tm.main⟩
  | t + 1 => unifNextCont tm (contRun input t) (traceState tm input t).2.1

/-- `traceState` at `t + 1` is one `unifStep` of `traceState` at `t`. -/
theorem traceState_succ (input : List (tm.Γ tm.k₀)) (t : ℕ) :
    traceState tm input (t + 1) = unifStep tm.m (traceState tm input t) := by
  rw [traceState, traceState, Function.iterate_succ_apply']

/-- `traceState` at `0` is the initial uniform state. -/
@[simp] theorem traceState_zero (input : List (tm.Γ tm.k₀)) :
    traceState tm input 0 = initUnif tm input := rfl

/-- **The mirror lemma.** Forgetting the token's relevance proof, `contRun` equals the continuation
component of `traceState`: `(contRun t).map Subtype.val = (traceState t).1`.  Induction on `t`:
the base is `initUnif`'s loaded `some (tm.m tm.main)`; the step combines `unifNextCont_eq_unifStep`
with the IH, casing on whether `traceState t` is already halted (`.1 = none`). -/
theorem contRun_map (input : List (tm.Γ tm.k₀)) (t : ℕ) :
    (contRun tm input t).map Subtype.val = (traceState tm input t).1 := by
  induction t with
  | zero =>
    -- `initUnif`'s continuation is `some (tm.m tm.main)` (label `some tm.main`).
    rw [contRun, traceState_zero, initUnif_eq]
    rfl
  | succ t ih =>
    rw [contRun, traceState_succ]
    -- Generalize `traceState t` to an honest `UnifState` triple (so `unifStep` typechecks after
    -- destructuring), carrying the IH and the `contRun`-step's state argument along.
    revert ih
    generalize traceState tm input t = st
    obtain ⟨c, v, Stk⟩ := st
    intro ih
    -- `(c, v, Stk).1` reduces to `c`; restate the IH.
    simp only at ih
    -- Case on the continuation token `contRun t` (= `c` by IH, since its `map val = c`).
    rcases hc : contRun tm input t with _ | ⟨q, hq⟩
    · -- halted token: `c = none`, so the step stays halted on both sides.
      rw [hc] at ih
      have hnone : c = none := by simpa using ih.symm
      rw [unifNextCont_none, hnone, unifStep_none, Option.map_none]
    · -- live token `some ⟨q, hq⟩`: use the `unifNextCont`/`unifStep` bridge, then read off `c`.
      rw [hc] at ih
      have hsome : c = some q := by simpa using ih.symm
      rw [unifNextCont_eq_unifStep q hq v Stk, hsome]

variable (tm) in
/-- The configuration trace over `Fin (T + 1)`: label `some tm.main` at time `0` (else `none`),
with `var`/`stk` read off `traceState`.  (Only the time-`0` and time-`last` labels are
boundary-relevant; intermediate labels are irrelevant to the transition clauses.) -/
noncomputable def cfgsW (input : List (tm.Γ tm.k₀)) (t : Fin (T + 1)) : tm.Cfg :=
  ⟨if (t : ℕ) = 0 then some tm.main else none,
    (traceState tm input (t : ℕ)).2.1, (traceState tm input (t : ℕ)).2.2⟩

variable (tm) in
/-- The continuation trace over `Fin (T + 1)`: `contRun` at the coerced time. -/
noncomputable def contsW (input : List (tm.Γ tm.k₀)) (t : Fin (T + 1)) : ContTok tm :=
  contRun tm input (t : ℕ)

/-! ## (1b) Pointwise readouts of `cfgsW`/`contsW` -/

/-- `(cfgsW t).var` is `traceState`'s state at the coerced time. -/
@[simp] theorem cfgsW_var (input : List (tm.Γ tm.k₀)) (t : Fin (T + 1)) :
    (cfgsW tm input t).var = (traceState tm input (t : ℕ)).2.1 := rfl

/-- `(cfgsW t).stk` is `traceState`'s stacks at the coerced time. -/
@[simp] theorem cfgsW_stk (input : List (tm.Γ tm.k₀)) (t : Fin (T + 1)) :
    (cfgsW tm input t).stk = (traceState tm input (t : ℕ)).2.2 := rfl

/-- `contToUnif (contsW t)` is `traceState`'s continuation at the coerced time (via `contRun_map`). -/
theorem contToUnif_contsW (input : List (tm.Γ tm.k₀)) (t : Fin (T + 1)) :
    contToUnif (contsW tm input t) = (traceState tm input (t : ℕ)).1 := by
  rw [contsW, contToUnif, contRun_map]

/-! ## (2) Boundary facts -/

/-- Config extensionality: two `tm.Cfg` agreeing on `l`/`var`/`stk` are equal (`Cfg` has no
auto-`ext` lemma in Mathlib, so destructure both and `simp_all`). -/
theorem cfg_ext {c d : tm.Cfg} (hl : c.l = d.l) (hv : c.var = d.var) (hs : c.stk = d.stk) :
    c = d := by
  obtain ⟨cl, cv, cs⟩ := c
  obtain ⟨dl, dv, ds⟩ := d
  simp_all

/-- The witness config at time `0` is the initial config `initList tm input`. -/
theorem cfgsW_zero (input : List (tm.Γ tm.k₀)) :
    cfgsW tm input (0 : Fin (T + 1)) = initList tm input := by
  -- `var`/`stk` come from `traceState 0 = initUnif = unifOfCfg (initList …)`; label is `some main`.
  refine cfg_ext ?_ ?_ ?_
  · simp only [cfgsW, Fin.val_zero]; rfl
  · simp only [cfgsW, Fin.val_zero, traceState_zero, initUnif, unifOfCfg_eq]
  · funext k
    simp only [cfgsW, Fin.val_zero, traceState_zero, initUnif, unifOfCfg_eq]

/-- The witness continuation at time `0` is the loaded program token of `tm.main`. -/
theorem contsW_zero (input : List (tm.Γ tm.k₀)) :
    contsW tm input (0 : Fin (T + 1)) =
      (some ⟨tm.m tm.main, program_mem_relevant tm tm.main⟩ : ContTok tm) := by
  rw [contsW, Fin.val_zero, contRun]

/-- **Halt config boundary.** Under `hhalt` and `0 < T`, the witness config at `Fin.last T` is the
halt config `haltList tm acceptOutput`: `traceState T = unifOfCfg (haltList …)`, giving its
`var`/`stk`, and the label is `none` because `T ≠ 0`. -/
theorem cfgsW_last {input : List (tm.Γ tm.k₀)} {acceptOutput : List (tm.Γ tm.k₁)}
    (hT : 0 < T)
    (hhalt : (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm (haltList tm acceptOutput)) :
    cfgsW tm input (Fin.last T) = haltList tm acceptOutput := by
  have hTr : traceState tm input T = unifOfCfg tm (haltList tm acceptOutput) := hhalt
  refine cfg_ext ?_ ?_ ?_
  · simp only [cfgsW, Fin.val_last, if_neg (by omega : T ≠ 0), haltList]
  · simp only [cfgsW, Fin.val_last, hTr, unifOfCfg_eq, haltList]
  · funext k
    simp only [cfgsW, Fin.val_last, hTr, unifOfCfg_eq, haltList]

/-- **Halt continuation boundary.** Under `hhalt`, the witness continuation at `Fin.last T` is the
halted token `none`: `(contRun T).map val = (traceState T).1 = contOfLabel none = none`, so
`contRun T = none` since `Option.map _ x = none ↔ x = none`. -/
theorem contsW_last {input : List (tm.Γ tm.k₀)} {acceptOutput : List (tm.Γ tm.k₁)}
    (hhalt : (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm (haltList tm acceptOutput)) :
    contsW tm input (Fin.last T) = (none : ContTok tm) := by
  have hmap : (contRun tm input T).map Subtype.val = none := by
    rw [contRun_map]
    have hTr : traceState tm input T = unifOfCfg tm (haltList tm acceptOutput) := hhalt
    rw [hTr, unifOfCfg_eq]; rfl
  rw [contsW, Fin.val_last, Option.map_eq_none_iff.mp hmap]

/-! ## (3) Stack-length bound and step consistency -/

/-- **Stack-length bound.** Each `traceState`-stack grows by at most one cell per step:
`((traceState t).2.2 k).length ≤ ((initList tm input).stk k).length + t`.  Induction on `t` via
`unifStep_stack_length_le`. -/
theorem traceState_len (input : List (tm.Γ tm.k₀)) (t : ℕ) (k : tm.K) :
    ((traceState tm input t).2.2 k).length ≤ ((initList tm input).stk k).length + t := by
  induction t with
  | zero =>
    simp only [traceState_zero, initUnif, unifOfCfg_eq, Nat.add_zero, le_refl]
  | succ t ih =>
    rw [traceState_succ]
    calc ((unifStep tm.m (traceState tm input t)).2.2 k).length
        ≤ ((traceState tm input t).2.2 k).length + 1 := unifStep_stack_length_le tm.m _ k
      _ ≤ (((initList tm input).stk k).length + t) + 1 := by omega
      _ = ((initList tm input).stk k).length + (t + 1) := by omega

/-- **Step consistency.** The unified readback of `cfgsW`/`contsW` at `t.succ` is one `unifStep` of
that at `t.castSucc` — both are `traceState` at consecutive times, related by `traceState_succ`. -/
theorem step_consistency (input : List (tm.Γ tm.k₀)) (t : Fin T) :
    (contToUnif (contsW tm input t.succ), (cfgsW tm input t.succ).var,
        fun k => (cfgsW tm input t.succ).stk k) =
      unifStep tm.m (contToUnif (contsW tm input t.castSucc), (cfgsW tm input t.castSucc).var,
        fun k => (cfgsW tm input t.castSucc).stk k) := by
  -- Both sides rewrite to `traceState` at the same indices.
  rw [contToUnif_contsW, contToUnif_contsW, cfgsW_var, cfgsW_var, cfgsW_stk, cfgsW_stk]
  -- `(t.succ : ℕ) = (t.castSucc : ℕ) + 1` and `(t.castSucc : ℕ) = (t : ℕ)`.
  have hsucc : (t.succ : ℕ) = (t.castSucc : ℕ) + 1 := by
    rw [Fin.val_succ, Fin.val_castSucc]
  rw [hsucc, traceState_succ]
  -- Both sides are now `unifStep (traceState ↑t.castSucc)` read componentwise; reassemble.
  obtain ⟨c, v, Stk⟩ := traceState tm input (t.castSucc : ℕ)
  rfl

/-- **Per-step stack fit.** Under the space bound `hSpace`, each `cfgsW`-stack at `t.castSucc` fits
within `S` (`length < S`): `length ≤ length(init) + t < S`. -/
theorem cfgsW_len_lt {input : List (tm.Γ tm.k₀)}
    (hSpace : ∀ k, ((initList tm input).stk k).length + T < S) (t : Fin T) (k : tm.K) :
    ((cfgsW tm input t.castSucc).stk k).length < S := by
  rw [cfgsW_stk]
  calc ((traceState tm input (t.castSucc : ℕ)).2.2 k).length
      ≤ ((initList tm input).stk k).length + (t.castSucc : ℕ) := traceState_len input _ k
    _ < ((initList tm input).stk k).length + T := by
        have : (t.castSucc : ℕ) < T := by rw [Fin.val_castSucc]; exact t.isLt
        omega
    _ < S := hSpace k

section Assembly

-- The assembly step needs the stack-alphabet typeclasses (the `_satisfies` lemmas consume them).
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **`Finset.univ`-`flatMap` intro.** A combined assignment satisfies a `flatMap` of clause groups
over `univ : Finset (Fin T)` iff it satisfies the group for every index. -/
theorem satisfiesAll_finFlatMap {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    {g : Fin T → List (Clause (fullNumVars tm T S (ContTok tm)))}
    (h : ∀ t : Fin T, satisfiesAll assign (g t)) :
    satisfiesAll assign ((Finset.univ : Finset (Fin T)).toList.flatMap g) := by
  rw [List.flatMap_def, satisfiesAll_flatten]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
  rintro cs t rfl
  exact h t

/-! ## (4) The encode direction: acceptance forces satisfiability -/

/-- **Encode direction.** If iterating `unifStep` for `T` steps from `initUnif tm input` reaches the
encoding of the halt config (`hhalt`), under the structural space bound `hSpace` and `0 < T`, the
tableau formula is `Satisfiable` — witnessed by `encodeC cfgsW contsW` of the real run.  Composition:
`eval_iff_satisfiesAll` + `satisfiesAll_append`×3, then `encodeC_fullConsistent`,
`initClausesC_satisfies`, the flat-mapped `unifTransClauses_satisfies` (via `step_consistency` and
`cfgsW_len_lt`), and `acceptClausesC_satisfies`. -/
theorem tableauFormula_accepts_imp_sat {input : List (tm.Γ tm.k₀)}
    {acceptOutput : List (tm.Γ tm.k₁)} {hS0 : 0 < S} (hT : 0 < T)
    (hSpace : ∀ k, ((initList tm input).stk k).length + T < S)
    (hhalt : (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm (haltList tm acceptOutput)) :
    Satisfiable (tableauFormula tm T S input acceptOutput hS0) := by
  refine ⟨encodeC (S := S) (cfgsW tm input) (contsW tm input), ?_⟩
  rw [eval_iff_satisfiesAll]
  -- Peel `((consistency ++ init) ++ transitions) ++ accept`.
  simp only [tableauFormula]
  rw [satisfiesAll_append, satisfiesAll_append, satisfiesAll_append]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- consistency
    exact encodeC_fullConsistent (cfgsW tm input) (contsW tm input)
  · -- init clauses
    exact initClausesC_satisfies (cfgsW tm input) (contsW tm input) input
      (cfgsW_zero input) (contsW_zero input)
  · -- the flat-mapped per-time transition clauses
    refine satisfiesAll_finFlatMap (fun t => ?_)
    exact unifTransClauses_satisfies (cfgsW tm input) (contsW tm input) t hS0
      (step_consistency input t) (fun k => cfgsW_len_lt hSpace t k)
  · -- accept clauses
    exact acceptClausesC_satisfies (cfgsW tm input) (contsW tm input) acceptOutput
      (cfgsW_last hT hhalt) (contsW_last hhalt)

end Assembly

/-! ## Sanity restatement (intent check against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- A `T`-step uniform halt to the encoded accept config makes the tableau formula satisfiable.
example {input : List (tm.Γ tm.k₀)} {acceptOutput : List (tm.Γ tm.k₁)} {hS0 : 0 < S} (hT : 0 < T)
    (hSpace : ∀ k, ((initList tm input).stk k).length + T < S)
    (hhalt : (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm (haltList tm acceptOutput)) :
    Satisfiable (tableauFormula tm T S input acceptOutput hS0) :=
  tableauFormula_accepts_imp_sat hT hSpace hhalt

end Examples

end CombinedTableau

end DeepWiki
