import DeepWiki.NetworkCalculus.UnifSmallStep
import DeepWiki.NetworkCalculus.TM2Trace

/-!
# Multi-big-step simulation of `Turing.FinTM2` by `unifStep`

Layer 3b-iii(d): the uniform small-step `unifStep` (`UnifSmallStep.lean`), iterated
from the initial state, *tracks the whole TM2 configuration trace* (`TM2Trace.lean`).
Encoding a config `c` as the uniform state `unifOfCfg tm c`, we lift the single-big-step
bridge `exists_unifStep_iterate_step` to configs (`exists_unifStep_iterate_cfg`), then
chain it along the trace by induction: whenever `tm2Trace tm input k = some c`, some fuel
`n` brings `(unifStep tm.m)^[n] (initUnif tm input)` to `unifOfCfg tm c`
(`exists_unifStep_iterate_tm2Trace`). Specialized to acceptance, this reaches the encoded
halt config (`exists_unifStep_iterate_halt`), whose continuation is `none` — a halted
uniform state.

Deferred to later layers: the converse (a halted uniform state ⟹ acceptance — only needed
if the reduction's reverse direction routes through `unifStep`), the tableau clause encoding
of `unifStep`, and reduction correctness.
-/

open Turing

namespace DeepWiki

namespace UnifSmallStep

open Turing.TM2

variable (tm : FinTM2)

/-- Encode a TM2 config as a uniform state: read the label into a continuation via
`contOfLabel`, keep `var`/`stk`. A halting config (`l = none`) maps to a halted state. -/
def unifOfCfg (c : tm.Cfg) : UnifState tm.Γ tm.Λ tm.σ :=
  (contOfLabel tm.m c.l, c.var, c.stk)

/-- The uniform state encoding the initial config on `input`. -/
def initUnif (input : List (tm.Γ tm.k₀)) : UnifState tm.Γ tm.Λ tm.σ :=
  unifOfCfg tm (initList tm input)

variable {tm}

/-- `unifOfCfg` of a config is its label-continuation, `var`, `stk`. -/
@[simp] theorem unifOfCfg_eq (c : tm.Cfg) :
    unifOfCfg tm c = (contOfLabel tm.m c.l, c.var, c.stk) := rfl

/-- `initUnif` loads `tm.main`'s program: `(some (tm.m tm.main), tm.initialState, stk)`. -/
theorem initUnif_eq (input : List (tm.Γ tm.k₀)) :
    initUnif tm input =
      (some (tm.m tm.main), tm.initialState, (initList tm input).stk) := rfl

/-- A halt config encodes to a *halted* uniform state: continuation `none`. -/
@[simp] theorem unifOfCfg_haltList (output : List (tm.Γ tm.k₁)) :
    unifOfCfg tm (haltList tm output) =
      (none, tm.initialState, (haltList tm output).stk) := rfl

/-- SINGLE-BIG-STEP BRIDGE (config form): from `unifOfCfg tm c` with `c.l = some l`,
some `unifStep` iterate reaches `unifOfCfg tm (stepAux (tm.m l) c.var c.stk)` — i.e. the
encoding of the next config `tm.step c`. Rewrites `exists_unifStep_iterate_step` through
`unifOfCfg`, using `c = ⟨some l, c.var, c.stk⟩` from `hl`. -/
theorem exists_unifStep_iterate_cfg (c : tm.Cfg) (l : tm.Λ) (hl : c.l = some l) :
    ∃ n, (unifStep tm.m)^[n] (unifOfCfg tm c) =
      unifOfCfg tm (Turing.TM2.stepAux (tm.m l) c.var c.stk) := by
  obtain ⟨n, hn⟩ := exists_unifStep_iterate_step tm.m l c.var c.stk
  refine ⟨n, ?_⟩
  -- The source: `unifOfCfg tm c = (some (tm.m l), c.var, c.stk)` since `c.l = some l`.
  rw [unifOfCfg_eq, hl, contOfLabel_some] at *
  rw [hn, unifOfCfg_eq]

/-- `tm.step c = some (stepAux (tm.m l) c.var c.stk)` when `c.l = some l`. -/
theorem step_eq_some_of_label (c : tm.Cfg) (l : tm.Λ) (hl : c.l = some l) :
    tm.step c = some (Turing.TM2.stepAux (tm.m l) c.var c.stk) := by
  cases c with
  | mk cl cvar cstk =>
    subst hl
    rfl

/-- A `tm.step` producing `some` forces a labelled source: if `tm.step c = some c'` then
`∃ l, c.l = some l` and `c' = stepAux (tm.m l) c.var c.stk`. -/
theorem exists_label_of_step (c c' : tm.Cfg) (h : tm.step c = some c') :
    ∃ l, c.l = some l ∧ c' = Turing.TM2.stepAux (tm.m l) c.var c.stk := by
  cases c with
  | mk cl cvar cstk =>
    cases cl with
    | none =>
      -- `step ⟨none, …⟩ = none`, contradicting `= some c'`.
      exact absurd h (by simp [FinTM2.step, Turing.TM2.step])
    | some l =>
      refine ⟨l, rfl, ?_⟩
      have : tm.step ⟨some l, cvar, cstk⟩ = some (Turing.TM2.stepAux (tm.m l) cvar cstk) := rfl
      rw [this] at h
      exact (Option.some.injEq _ _).mp h.symm

/-- THE SIMULATION (headline): iterating `unifStep` from `initUnif tm input` tracks the
TM2 trace — whenever `tm2Trace tm input k = some c`, some fuel `n` reaches `unifOfCfg tm c`.
Induction on `k`: base `k = 0` gives `c = initList tm input` and `n = 0`; step uses
`tm2Trace_succ` to extract the previous config + a `tm.step`, the IH, the config bridge
`exists_unifStep_iterate_cfg`, and `Function.iterate_add_apply` to compose the fuels. -/
theorem exists_unifStep_iterate_tm2Trace (input : List (tm.Γ tm.k₀)) (k : ℕ) (c : tm.Cfg)
    (hk : tm2Trace tm input k = some c) :
    ∃ n, (unifStep tm.m)^[n] (initUnif tm input) = unifOfCfg tm c := by
  induction k generalizing c with
  | zero =>
    rw [tm2Trace_zero] at hk
    obtain rfl : c = initList tm input := (Option.some.injEq _ _).mp hk.symm
    exact ⟨0, rfl⟩
  | succ k ih =>
    -- `tm2Trace … (k+1) = (tm2Trace … k).bind tm.step = some c`.
    rw [tm2Trace, traceFrom_succ, ← tm2Trace] at hk
    -- Extract the previous config and the step that produced `c`.
    obtain ⟨cprev, hprev, hstep⟩ := Option.bind_eq_some_iff.mp hk
    -- `tm.step cprev = some c` forces a label on `cprev`.
    obtain ⟨l, hl, rfl⟩ := exists_label_of_step cprev c hstep
    -- IH: reach `unifOfCfg tm cprev` in `N` moves.
    obtain ⟨N, hN⟩ := ih cprev hprev
    -- Bridge: from `unifOfCfg tm cprev`, reach the encoding of the next config in `n` moves.
    obtain ⟨n, hn⟩ := exists_unifStep_iterate_cfg cprev l hl
    refine ⟨n + N, ?_⟩
    rw [Function.iterate_add_apply, hN, hn]

/-- ACCEPTANCE COROLLARY: if `tm` accepts `input` with `output` within `m` steps, some
`unifStep` iterate from `initUnif tm input` reaches `unifOfCfg tm (haltList tm output)` —
a *halted* uniform state (continuation `none`). Unfolds `AcceptsWithin` to a trace hitting
the halt config, then applies the simulation. -/
theorem exists_unifStep_iterate_halt (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (m : ℕ) (h : AcceptsWithin tm input (some output) m) :
    ∃ n, (unifStep tm.m)^[n] (initUnif tm input) = unifOfCfg tm (haltList tm output) := by
  obtain ⟨k, _, hk⟩ := h
  rw [Option.map_some] at hk
  exact exists_unifStep_iterate_tm2Trace input k (haltList tm output) hk

-- Restatements ("it compiled" ≠ "it says the right thing").

/-- The simulation, restated. -/
example (input : List (tm.Γ tm.k₀)) (k : ℕ) (c : tm.Cfg)
    (hk : tm2Trace tm input k = some c) :
    ∃ n, (unifStep tm.m)^[n] (initUnif tm input) = unifOfCfg tm c :=
  exists_unifStep_iterate_tm2Trace input k c hk

/-- The acceptance corollary, restated. -/
example (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (m : ℕ)
    (h : AcceptsWithin tm input (some output) m) :
    ∃ n, (unifStep tm.m)^[n] (initUnif tm input) = unifOfCfg tm (haltList tm output) :=
  exists_unifStep_iterate_halt input output m h

/-- The reached halt state is genuinely halted (continuation `none`). -/
example (output : List (tm.Γ tm.k₁)) :
    (unifOfCfg tm (haltList tm output)).1 = none := rfl

end UnifSmallStep

end DeepWiki
