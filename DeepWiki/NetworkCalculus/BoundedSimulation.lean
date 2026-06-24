import DeepWiki.NetworkCalculus.UnifSimulation

/-!
# Bounded forward simulation of `Turing.FinTM2` by `unifStep`

Layer 3b-iii(f): a *quantitatively bounded* version of the forward simulation in
`UnifSimulation.lean`.  Where the headline `exists_unifStep_iterate_*` lemmas give an
unbounded `∃ n`, this file re-proves them carrying an explicit small-step bound, so the
tableau's small-step time axis `T` can be set to a polynomial in the big-step count.

* **Per-statement bound** `exists_unifStep_iterate_stmt_le`: `n ≤ stmtSize q + 1`, the same
  bound the fuel runner `runFuel_stmtSize_succ` uses, carried through the same structural
  induction.
* **Machine constant** `maxStmt tm := (⨆ l, stmtSize (tm.m l)) + 1`, the worst-case
  per-big-step small-step cost (`Λ` is `Fintype` via `tm.ΛFin`).
* **Multi-big-step bound** `exists_unifStep_iterate_tm2Trace_le`: `n ≤ k * maxStmt tm`, by
  induction on the trace length `k` accumulating the per-step bound.
* **Bounded acceptance** `exists_unifStep_iterate_halt_le` (`n ≤ m * maxStmt tm`) and the
  padded form `unifStep_iterate_halt_padded`: for any `T ≥ m * maxStmt tm`, exactly `T`
  `unifStep` iterations from `initUnif` land on the halted encoding of the output — the
  output the encode direction's `hhalt` hypothesis needs, supplied from `AcceptsWithin`.

Deferred to later layers: the verifier/certificate encoding, the `IsInNP_TM` refinement,
and the Cook- and Levin discharge.
-/

open Turing
open Function (update)

namespace DeepWiki

namespace UnifSmallStep

open Turing.TM2 Turing.TM2.Stmt
open TM2SmallStep (stmtSize one_le_stmtSize)

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
variable (M : Λ → Turing.TM2.Stmt Γ Λ σ)

/-- BOUNDED PER-STATEMENT: from `(some q, v, S)`, at most `stmtSize q + 1` `unifStep` moves
reach the encoding of the big-step `stepAux q v S`.  Re-proves `exists_unifStep_iterate_stmt`
carrying the bound through structural induction: `push`/`peek`/`pop`/`load` add one move to
the recursive `≤ stmtSize q' + 1`; `branch` takes the chosen arm (`≤ stmtSize qᵢ + 1`, and
`stmtSize qᵢ ≤ stmtSize (branch …)`); `goto`/`halt` are one-move leaves. -/
theorem exists_unifStep_iterate_stmt_le (q : Turing.TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) :
    ∃ n ≤ stmtSize q + 1, (unifStep M)^[n] (some q, v, S) =
      (contOfLabel M (Turing.TM2.stepAux q v S).l, (Turing.TM2.stepAux q v S).var,
        (Turing.TM2.stepAux q v S).stk) := by
  induction q generalizing v S with
  | push k f q ih =>
    obtain ⟨n, hle, hn⟩ := ih v (update S k (f v :: S k))
    refine ⟨n + 1, ?_, by rw [Function.iterate_succ_apply, unifStep_push]; simpa using hn⟩
    simp only [stmtSize]; omega
  | peek k f q ih =>
    obtain ⟨n, hle, hn⟩ := ih (f v (S k).head?) S
    refine ⟨n + 1, ?_, by rw [Function.iterate_succ_apply, unifStep_peek]; simpa using hn⟩
    simp only [stmtSize]; omega
  | pop k f q ih =>
    obtain ⟨n, hle, hn⟩ := ih (f v (S k).head?) (update S k (S k).tail)
    refine ⟨n + 1, ?_, by rw [Function.iterate_succ_apply, unifStep_pop]; simpa using hn⟩
    simp only [stmtSize]; omega
  | load a q ih =>
    obtain ⟨n, hle, hn⟩ := ih (a v) S
    refine ⟨n + 1, ?_, by rw [Function.iterate_succ_apply, unifStep_load]; simpa using hn⟩
    simp only [stmtSize]; omega
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases hb : f v with
    | false =>
      obtain ⟨n, hle, hn⟩ := ih₂ v S
      refine ⟨n + 1, ?_, ?_⟩
      · have h₁ := one_le_stmtSize q₁
        simp only [stmtSize]; omega
      · rw [Function.iterate_succ_apply, unifStep_branch]
        simp only [Turing.TM2.stepAux, hb, Bool.cond_false]
        exact hn
    | true =>
      obtain ⟨n, hle, hn⟩ := ih₁ v S
      refine ⟨n + 1, ?_, ?_⟩
      · have h₂ := one_le_stmtSize q₂
        simp only [stmtSize]; omega
      · rw [Function.iterate_succ_apply, unifStep_branch]
        simp only [Turing.TM2.stepAux, hb, Bool.cond_true]
        exact hn
  | goto f => exact ⟨1, by simp [stmtSize], by rw [Function.iterate_one, unifStep_goto]; rfl⟩
  | halt => exact ⟨1, by simp [stmtSize], by rw [Function.iterate_one, unifStep_halt]; rfl⟩

/-- BOUNDED BRIDGE: from `(some (M l), v, S)`, iterating `unifStep` reaches the encoding of
the next big-step config in at most `stmtSize (M l) + 1` moves (bounded
`exists_unifStep_iterate_step`). -/
theorem exists_unifStep_iterate_step_le (l : Λ) (v : σ) (S : ∀ k, List (Γ k)) :
    ∃ n ≤ stmtSize (M l) + 1, (unifStep M)^[n] (some (M l), v, S) =
      (contOfLabel M (Turing.TM2.stepAux (M l) v S).l, (Turing.TM2.stepAux (M l) v S).var,
        (Turing.TM2.stepAux (M l) v S).stk) :=
  exists_unifStep_iterate_stmt_le M (M l) v S

variable (tm : FinTM2)

/-- The machine's worst-case per-big-step small-step cost: `(⨆ l, stmtSize (tm.m l)) + 1`,
the `+1` absorbing the `goto`/`halt` leaf move.  `Λ` is `Fintype` via `tm.ΛFin`. -/
def maxStmt : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup (fun l => stmtSize (tm.m l)) + 1

variable {tm}

/-- Every label's per-big-step cost is bounded by `maxStmt tm`:
`stmtSize (tm.m l) + 1 ≤ maxStmt tm`. -/
theorem stmtSize_M_le_maxStmt (l : tm.Λ) : stmtSize (tm.m l) + 1 ≤ maxStmt tm := by
  rw [maxStmt]
  refine Nat.add_le_add_right
    (Finset.le_sup (s := @Finset.univ tm.Λ tm.ΛFin) (f := fun l => stmtSize (tm.m l))
      (b := l) ?_) 1
  exact @Finset.mem_univ tm.Λ tm.ΛFin l

/-- BOUNDED SIMULATION: whenever `tm2Trace tm input k = some c`, at most `k * maxStmt tm`
`unifStep` moves bring `(unifStep tm.m)^[n] (initUnif tm input)` to `unifOfCfg tm c`.
Re-proves `exists_unifStep_iterate_tm2Trace` carrying the bound: base `k = 0` uses `n = 0`;
the step composes the IH (`n₁ ≤ k * maxStmt`) with the per-big-step bound
(`n₂ ≤ stmtSize (tm.m l) + 1 ≤ maxStmt`) via `Function.iterate_add_apply`, giving
`n₁ + n₂ ≤ (k + 1) * maxStmt`. -/
theorem exists_unifStep_iterate_tm2Trace_le (input : List (tm.Γ tm.k₀)) (k : ℕ) (c : tm.Cfg)
    (hk : tm2Trace tm input k = some c) :
    ∃ n ≤ k * maxStmt tm, (unifStep tm.m)^[n] (initUnif tm input) = unifOfCfg tm c := by
  induction k generalizing c with
  | zero =>
    rw [tm2Trace_zero] at hk
    obtain rfl : c = initList tm input := (Option.some.injEq _ _).mp hk.symm
    exact ⟨0, by simp, rfl⟩
  | succ k ih =>
    rw [tm2Trace, traceFrom_succ, ← tm2Trace] at hk
    obtain ⟨cprev, hprev, hstep⟩ := Option.bind_eq_some_iff.mp hk
    obtain ⟨l, hl, rfl⟩ := exists_label_of_step cprev c hstep
    obtain ⟨N, hNk, hN⟩ := ih cprev hprev
    obtain ⟨n, hnle, hn⟩ := exists_unifStep_iterate_step_le tm.m l cprev.var cprev.stk
    refine ⟨n + N, ?_, ?_⟩
    · -- n ≤ stmtSize (tm.m l) + 1 ≤ maxStmt; N ≤ k * maxStmt; so n + N ≤ (k+1) * maxStmt.
      have hmax := stmtSize_M_le_maxStmt (tm := tm) l
      have : n ≤ maxStmt tm := le_trans hnle hmax
      calc n + N ≤ maxStmt tm + k * maxStmt tm := by omega
        _ = (k + 1) * maxStmt tm := by ring
    · -- Compose the IH-iterate with the bridge-iterate (from `unifOfCfg tm cprev`).
      rw [Function.iterate_add_apply, hN]
      have hsrc : unifOfCfg tm cprev =
          (some (tm.m l), cprev.var, cprev.stk) := by
        rw [unifOfCfg_eq, hl, contOfLabel_some]
      rw [hsrc, hn, unifOfCfg_eq]

/-- BOUNDED ACCEPTANCE: if `tm` accepts `input` with `output` within `m` steps, at most
`m * maxStmt tm` `unifStep` moves from `initUnif tm input` reach `unifOfCfg tm (haltList tm
output)` — a halted uniform state.  From the bounded simulation at the halt config, with
`k ≤ m` giving `k * maxStmt ≤ m * maxStmt`. -/
theorem exists_unifStep_iterate_halt_le (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (m : ℕ) (h : AcceptsWithin tm input (some output) m) :
    ∃ n ≤ m * maxStmt tm,
      (unifStep tm.m)^[n] (initUnif tm input) = unifOfCfg tm (haltList tm output) := by
  obtain ⟨k, hkm, hk⟩ := h
  rw [Option.map_some] at hk
  obtain ⟨n, hnle, hn⟩ := exists_unifStep_iterate_tm2Trace_le input k (haltList tm output) hk
  refine ⟨n, ?_, hn⟩
  exact le_trans hnle (Nat.mul_le_mul_right _ hkm)

/-- PADDED ACCEPTANCE (key output): for any `T ≥ m * maxStmt tm`, exactly `T` `unifStep`
iterations from `initUnif tm input` land on the halted encoding `unifOfCfg tm (haltList tm
output)`.  From bounded acceptance (`∃ n ≤ m * maxStmt ≤ T`) padded to `T` via the halted
fixed point `unifStep_halted_iterate`: the halted state encodes a `none` continuation, so
the extra `T - n` steps stay put.  Lets the encode direction's `hhalt` hypothesis be
supplied from `AcceptsWithin` once `T ≥ m * maxStmt tm`. -/
theorem unifStep_iterate_halt_padded (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (m T : ℕ) (hT : m * maxStmt tm ≤ T)
    (h : AcceptsWithin tm input (some output) m) :
    (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm (haltList tm output) := by
  obtain ⟨n, hnle, hn⟩ := exists_unifStep_iterate_halt_le input output m h
  -- The reached state is halted: `unifOfCfg tm (haltList …) = (none, …)`.
  rw [unifOfCfg_haltList] at hn
  -- Pad `n` up to `T` through the halted fixed point.
  obtain ⟨d, rfl⟩ : ∃ d, T = n + d := ⟨T - n, by omega⟩
  rw [add_comm, Function.iterate_add_apply, hn, unifStep_halted_iterate, unifOfCfg_haltList]

-- Restatements ("it compiled" ≠ "it says the right thing").

/-- The bounded per-statement simulation, restated. -/
example (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    ∃ n ≤ stmtSize q + 1, (unifStep M)^[n] (some q, v, S) =
      (contOfLabel M (Turing.TM2.stepAux q v S).l, (Turing.TM2.stepAux q v S).var,
        (Turing.TM2.stepAux q v S).stk) :=
  exists_unifStep_iterate_stmt_le M q v S

/-- The per-label bound on `maxStmt`, restated. -/
example (l : tm.Λ) : stmtSize (tm.m l) + 1 ≤ maxStmt tm :=
  stmtSize_M_le_maxStmt l

/-- The bounded multi-big-step simulation, restated. -/
example (input : List (tm.Γ tm.k₀)) (k : ℕ) (c : tm.Cfg)
    (hk : tm2Trace tm input k = some c) :
    ∃ n ≤ k * maxStmt tm, (unifStep tm.m)^[n] (initUnif tm input) = unifOfCfg tm c :=
  exists_unifStep_iterate_tm2Trace_le input k c hk

/-- Bounded acceptance, restated. -/
example (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (m : ℕ)
    (h : AcceptsWithin tm input (some output) m) :
    ∃ n ≤ m * maxStmt tm,
      (unifStep tm.m)^[n] (initUnif tm input) = unifOfCfg tm (haltList tm output) :=
  exists_unifStep_iterate_halt_le input output m h

/-- The padded acceptance bound, restated against its expected type. -/
example (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (m T : ℕ)
    (hT : m * maxStmt tm ≤ T) (h : AcceptsWithin tm input (some output) m) :
    (unifStep tm.m)^[T] (initUnif tm input) = unifOfCfg tm (haltList tm output) :=
  unifStep_iterate_halt_padded input output m T hT h

end UnifSmallStep

end DeepWiki
