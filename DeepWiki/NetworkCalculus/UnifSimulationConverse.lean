import DeepWiki.NetworkCalculus.UnifSimulation

/-!
# Converse simulation: a halted `unifStep` iterate forces a TM2 halt config

Layer 3b-iii(e): the reverse of `UnifSimulation.lean`.  Where the forward direction
shows that iterating `unifStep` from `initUnif` *tracks* the TM2 trace, this file shows
that if some `unifStep` iterate from `initUnif tm input` reaches the encoding
`unifOfCfg tm c` of a *halt* config (`c.l = none`, hence a halted uniform state with
continuation `none`), then the TM2 genuinely reaches `c` along its own trace
(`∃ k, tm2Trace tm input k = some c`).

The argument has two ingredients:
* **Halted fixed point + determinism.** Once a `unifStep` iterate lands on a halted state
  `(none, v, S)` it stays there (`unifStep_halted_iterate`); comparing two iterate counts
  via `Function.iterate_add_apply` (`unifStep_iterate_eq_of_ge`) makes both the halt time
  `N` and any forward-sim time agree on the halted state.
* **Strictly-positive per-big-step fuel.** Every TM2 statement consumes at least one
  `unifStep` (its `goto`/`halt` leaf is one move; `exists_unifStep_iterate_stmt_pos`),
  so the forward simulation reaches unif fuel `≥ k` at trace step `k`
  (`exists_unifStep_iterate_tm2Trace_ge`).  This lets a *running* config at step `N+1`
  be ruled out against the halted fixed point.

Deferred to later layers: the accept clauses, the tableau formula assembly,
`Satisfiable ⟺ accepts`, poly-size bounds, the verifier/certificate encoding, and the
Cook- and Levin discharge — this file only delivers the converse simulation.
-/

open Turing
open Function (update)

namespace DeepWiki

namespace UnifSmallStep

open Turing.TM2 Turing.TM2.Stmt

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
variable (M : Λ → Turing.TM2.Stmt Γ Λ σ)

/-- STRICTLY-POSITIVE FUEL: every statement `q` consumes at least one `unifStep` to reach
its big-step encoding.  Strengthens `exists_unifStep_iterate_stmt` with `n ≥ 1`: each
constructor either is a one-move `goto`/`halt` leaf or prepends a move before recursing. -/
theorem exists_unifStep_iterate_stmt_pos (q : Turing.TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) :
    ∃ n ≥ 1, (unifStep M)^[n] (some q, v, S) =
      (contOfLabel M (Turing.TM2.stepAux q v S).l, (Turing.TM2.stepAux q v S).var,
        (Turing.TM2.stepAux q v S).stk) := by
  induction q generalizing v S with
  | push k f q ih =>
    obtain ⟨n, _, hn⟩ := ih v (update S k (f v :: S k))
    exact ⟨n + 1, by omega, by rw [Function.iterate_succ_apply, unifStep_push]; simpa using hn⟩
  | peek k f q ih =>
    obtain ⟨n, _, hn⟩ := ih (f v (S k).head?) S
    exact ⟨n + 1, by omega, by rw [Function.iterate_succ_apply, unifStep_peek]; simpa using hn⟩
  | pop k f q ih =>
    obtain ⟨n, _, hn⟩ := ih (f v (S k).head?) (update S k (S k).tail)
    exact ⟨n + 1, by omega, by rw [Function.iterate_succ_apply, unifStep_pop]; simpa using hn⟩
  | load a q ih =>
    obtain ⟨n, _, hn⟩ := ih (a v) S
    exact ⟨n + 1, by omega, by rw [Function.iterate_succ_apply, unifStep_load]; simpa using hn⟩
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases hb : f v with
    | false =>
      obtain ⟨n, _, hn⟩ := ih₂ v S
      refine ⟨n + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply, unifStep_branch]
      simp only [Turing.TM2.stepAux, hb, Bool.cond_false]
      exact hn
    | true =>
      obtain ⟨n, _, hn⟩ := ih₁ v S
      refine ⟨n + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply, unifStep_branch]
      simp only [Turing.TM2.stepAux, hb, Bool.cond_true]
      exact hn
  | goto f => exact ⟨1, le_rfl, by rw [Function.iterate_one, unifStep_goto]; rfl⟩
  | halt => exact ⟨1, le_rfl, by rw [Function.iterate_one, unifStep_halt]; rfl⟩

/-- STRICTLY-POSITIVE BRIDGE: from `(some (M l), v, S)`, iterating `unifStep` reaches the
encoding of the next big-step config in `≥ 1` moves (positive fuel `exists_unifStep_iterate_step`). -/
theorem exists_unifStep_iterate_step_pos (l : Λ) (v : σ) (S : ∀ k, List (Γ k)) :
    ∃ n ≥ 1, (unifStep M)^[n] (some (M l), v, S) =
      (contOfLabel M (Turing.TM2.stepAux (M l) v S).l, (Turing.TM2.stepAux (M l) v S).var,
        (Turing.TM2.stepAux (M l) v S).stk) :=
  exists_unifStep_iterate_stmt_pos M (M l) v S

/-- Iterating from a state that has already reached the halted state stays halted: if
`(unifStep M)^[a] x = (none, v, S)` and `a ≤ b`, then `(unifStep M)^[b] x = (none, v, S)`.
`b = a + (b - a)`, `Function.iterate_add_apply`, and the halted fixed point. -/
theorem unifStep_iterate_eq_of_ge {x : UnifState Γ Λ σ} {a b : ℕ} {v : σ}
    {S : ∀ k, List (Γ k)} (ha : (unifStep M)^[a] x = (none, v, S)) (hab : a ≤ b) :
    (unifStep M)^[b] x = (none, v, S) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [add_comm, Function.iterate_add_apply, ha, unifStep_halted_iterate]

variable {tm : FinTM2}

/-- SINGLE-BIG-STEP BRIDGE (config, positive fuel): from `unifOfCfg tm c` with
`c.l = some l`, some `n ≥ 1` `unifStep` moves reach `unifOfCfg tm (stepAux (tm.m l) c.var c.stk)`.
Positive-fuel `exists_unifStep_iterate_cfg`. -/
theorem exists_unifStep_iterate_cfg_pos (c : tm.Cfg) (l : tm.Λ) (hl : c.l = some l) :
    ∃ n ≥ 1, (unifStep tm.m)^[n] (unifOfCfg tm c) =
      unifOfCfg tm (Turing.TM2.stepAux (tm.m l) c.var c.stk) := by
  obtain ⟨n, hn1, hn⟩ := exists_unifStep_iterate_step_pos tm.m l c.var c.stk
  refine ⟨n, hn1, ?_⟩
  rw [unifOfCfg_eq, hl, contOfLabel_some] at *
  rw [hn, unifOfCfg_eq]

/-- THE SIMULATION, POSITIVE FUEL: whenever `tm2Trace tm input k = some c`, some fuel
`n ≥ k` brings `(unifStep tm.m)^[n] (initUnif tm input)` to `unifOfCfg tm c`.  Strengthens
`exists_unifStep_iterate_tm2Trace` with `n ≥ k`, since each of the `k` big-steps consumes
at least one `unifStep` (`exists_unifStep_iterate_cfg_pos`). -/
theorem exists_unifStep_iterate_tm2Trace_ge (input : List (tm.Γ tm.k₀)) (k : ℕ) (c : tm.Cfg)
    (hk : tm2Trace tm input k = some c) :
    ∃ n ≥ k, (unifStep tm.m)^[n] (initUnif tm input) = unifOfCfg tm c := by
  induction k generalizing c with
  | zero =>
    rw [tm2Trace_zero] at hk
    obtain rfl : c = initList tm input := (Option.some.injEq _ _).mp hk.symm
    exact ⟨0, le_rfl, rfl⟩
  | succ k ih =>
    rw [tm2Trace, traceFrom_succ, ← tm2Trace] at hk
    obtain ⟨cprev, hprev, hstep⟩ := Option.bind_eq_some_iff.mp hk
    obtain ⟨l, hl, rfl⟩ := exists_label_of_step cprev c hstep
    obtain ⟨N, hNk, hN⟩ := ih cprev hprev
    obtain ⟨n, hn1, hn⟩ := exists_unifStep_iterate_cfg_pos cprev l hl
    refine ⟨n + N, by omega, ?_⟩
    rw [Function.iterate_add_apply, hN, hn]

/-- A `none` continuation reads back to a halt label: `contOfLabel tm.m c.l = none → c.l = none`
(a `some l` label would give the non-`none` continuation `some (tm.m l)`). -/
theorem label_eq_none_of_contOfLabel (c : tm.Cfg) (h : contOfLabel tm.m c.l = none) :
    c.l = none := by
  cases hcl : c.l with
  | none => rfl
  | some l => rw [hcl, contOfLabel_some] at h; exact absurd h (Option.some_ne_none _)

/-- `unifOfCfg` is injective on halt configs: two configs with `l = none` and the same
uniform encoding are equal (the encoding keeps `var`/`stk` verbatim and `l` is forced `none`). -/
theorem unifOfCfg_inj_of_halt {c c' : tm.Cfg} (hc : c.l = none) (hc' : c'.l = none)
    (h : unifOfCfg tm c = unifOfCfg tm c') : c = c' := by
  have hvar : c.var = c'.var := congrArg (fun p => p.2.1) h
  have hstk : c.stk = c'.stk := congrArg (fun p => p.2.2) h
  cases c; cases c'; simp_all

/-- A `tm.step` returning `none` forces a halt label: `tm.step c = none → c.l = none`. -/
theorem label_eq_none_of_step_none (c : tm.Cfg) (h : tm.step c = none) : c.l = none := by
  by_contra hcl
  obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp hcl
  have : tm.step c = some (Turing.TM2.stepAux (tm.m l) c.var c.stk) := step_eq_some_of_label c l hl
  rw [this] at h
  exact Option.some_ne_none _ h

variable (tm)

/-- CONVERSE SIMULATION (headline): if iterating `unifStep` from `initUnif tm input` reaches
the encoding `unifOfCfg tm c` of a *halt* config (`c.l = none`, a halted uniform state), then
the TM2 genuinely reaches `c` along its trace: `∃ k, tm2Trace tm input k = some c`.
Determinism (`unifStep_iterate_eq_of_ge`) + the positive-fuel forward simulation
(`exists_unifStep_iterate_tm2Trace_ge`); a running config at step `N+1` is ruled out against
the halted fixed point, a halted one is pinned to `c` by injectivity. -/
theorem unifStep_halts_imp_tm2_halts (input : List (tm.Γ tm.k₀)) (N : ℕ) (c : tm.Cfg)
    (hhalt : (unifStep tm.m)^[N] (initUnif tm input) = unifOfCfg tm c) (hc : c.l = none) :
    ∃ k, tm2Trace tm input k = some c := by
  -- The reached uniform state is halted: `unifOfCfg tm c = (none, c.var, c.stk)`.
  have hhaltN : (unifStep tm.m)^[N] (initUnif tm input) = (none, c.var, c.stk) := by
    rw [hhalt, unifOfCfg_eq, hc, contOfLabel_none]
  -- Inspect the TM2 trace one step past the halt time.
  cases hN1 : tm2Trace tm input (N + 1) with
  | some c' =>
    -- A config at step `N+1` needs unif fuel `n ≥ N+1`, so it is halted (fixed point), `= c`.
    obtain ⟨n, hn, hnval⟩ := exists_unifStep_iterate_tm2Trace_ge input (N + 1) c' hN1
    have hnhalt : (unifStep tm.m)^[n] (initUnif tm input) = (none, c.var, c.stk) :=
      unifStep_iterate_eq_of_ge tm.m hhaltN (by omega)
    rw [hnval] at hnhalt
    -- `unifOfCfg tm c' = (none, c.var, c.stk)`: forces `c'.l = none` and `c' = c`.
    have hcl' : c'.l = none :=
      label_eq_none_of_contOfLabel c' (by rw [unifOfCfg_eq] at hnhalt; exact congrArg (·.1) hnhalt)
    refine ⟨N + 1, ?_⟩
    rw [hN1]
    congr 1
    refine unifOfCfg_inj_of_halt hcl' hc ?_
    rw [hnhalt, unifOfCfg_eq, hc, contOfLabel_none]
  | none =>
    -- The trace halted before `N+1`: find the first `some → none` transition.
    -- `tm2Trace … 0 = some _` and `tm2Trace … (N+1) = none`, so such a step exists.
    have h0 : tm2Trace tm input 0 = some (initList tm input) := tm2Trace_zero input
    -- Find the largest `k ≤ N` with `tm2Trace tm input k = some _`.
    obtain ⟨k, hkN, ck, hck, hknone⟩ :
        ∃ k ≤ N, ∃ ck, tm2Trace tm input k = some ck ∧ tm2Trace tm input (k + 1) = none := by
      -- Decreasing search: the predicate "trace is `some` at step `j`" holds at `0`, fails at `N+1`.
      clear hhalt hhaltN
      induction N with
      | zero => exact ⟨0, le_rfl, initList tm input, h0, hN1⟩
      | succ M ih =>
        cases hM1 : tm2Trace tm input (M + 1) with
        | none => obtain ⟨k, hkM, ck, hck, hkn⟩ := ih hM1; exact ⟨k, by omega, ck, hck, hkn⟩
        | some cM => exact ⟨M + 1, le_rfl, cM, hM1, hN1⟩
    -- `tm.step ck = none` (the trace dies after `ck`), so `ck.l = none`.
    have hstepck : tm.step ck = none := by
      rw [tm2Trace, traceFrom_succ, ← tm2Trace, hck, Option.bind_some] at hknone
      exact hknone
    have hckl : ck.l = none := label_eq_none_of_step_none ck hstepck
    -- Forward sim reaches `unifOfCfg tm ck = (none, ck.var, ck.stk)` at some time `m`.
    obtain ⟨m, _, hmval⟩ := exists_unifStep_iterate_tm2Trace_ge input k ck hck
    have hmhalt : (unifStep tm.m)^[m] (initUnif tm input) = (none, ck.var, ck.stk) := by
      rw [hmval, unifOfCfg_eq, hckl, contOfLabel_none]
    -- Both the time-`N` halt and the time-`m` halt agree on `(unifStep)^[max N m] (initUnif)`.
    have hNm : (unifStep tm.m)^[max N m] (initUnif tm input) = (none, c.var, c.stk) :=
      unifStep_iterate_eq_of_ge tm.m hhaltN (le_max_left N m)
    have hmM : (unifStep tm.m)^[max N m] (initUnif tm input) = (none, ck.var, ck.stk) :=
      unifStep_iterate_eq_of_ge tm.m hmhalt (le_max_right N m)
    have heq : (none, c.var, c.stk) = ((none, ck.var, ck.stk) : UnifState tm.Γ tm.Λ tm.σ) := by
      rw [← hNm, ← hmM]
    -- Hence `ck = c`, and the trace reaches `c` at step `k`.
    refine ⟨k, ?_⟩
    rw [hck]
    congr 1
    refine unifOfCfg_inj_of_halt hckl hc ?_
    rw [unifOfCfg_eq, unifOfCfg_eq, hckl, hc, contOfLabel_none]
    exact heq.symm

-- Restatements ("it compiled" ≠ "it says the right thing").

/-- The converse simulation, restated against its expected type. -/
example (input : List (tm.Γ tm.k₀)) (N : ℕ) (c : tm.Cfg)
    (hhalt : (unifStep tm.m)^[N] (initUnif tm input) = unifOfCfg tm c) (hc : c.l = none) :
    ∃ k, tm2Trace tm input k = some c :=
  unifStep_halts_imp_tm2_halts tm input N c hhalt hc

/-- Positive-fuel forward simulation, restated: trace step `k` needs unif fuel `n ≥ k`. -/
example (input : List (tm.Γ tm.k₀)) (k : ℕ) (c : tm.Cfg)
    (hk : tm2Trace tm input k = some c) :
    ∃ n ≥ k, (unifStep tm.m)^[n] (initUnif tm input) = unifOfCfg tm c :=
  exists_unifStep_iterate_tm2Trace_ge input k c hk

end UnifSmallStep

end DeepWiki
