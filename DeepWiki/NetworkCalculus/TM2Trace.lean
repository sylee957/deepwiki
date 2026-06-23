import Mathlib.Computability.TuringMachine.Computable

/-!
# Computation-trace abstraction over `Turing.FinTM2`

Layer 2 of a Cook- and Levin-style formalization: an explicit time-indexed
configuration trace `traceFrom f c₀ k = (flip bind f)^[k] (some c₀)` over a state
transition function `f : σ → Option σ`, bridged to Mathlib's `StateTransition.EvalsTo`
and the Turing-machine predicate `Turing.TM2OutputsInTime`.  The trace is the form the
tableau (layer 3) encodes as per-time-step variables.
-/

open StateTransition Turing

namespace DeepWiki

section Trace

variable {σ : Type*}

/-- `traceFrom f c₀ k`: the configuration `f` reaches from `c₀` after exactly `k` steps
(`none` once the computation has halted). -/
def traceFrom (f : σ → Option σ) (c₀ : σ) (k : ℕ) : Option σ :=
  (flip bind f)^[k] (some c₀)

/-- The trace at time `0` is the start config. -/
@[simp]
theorem traceFrom_zero (f : σ → Option σ) (c₀ : σ) : traceFrom f c₀ 0 = some c₀ :=
  rfl

/-- One step of the trace: bind the previous config through `f`. -/
theorem traceFrom_succ (f : σ → Option σ) (c₀ : σ) (k : ℕ) :
    traceFrom f c₀ (k + 1) = (traceFrom f c₀ k).bind f := by
  unfold traceFrom
  rw [Function.iterate_succ_apply']
  rfl

/-- Once the trace is `none` it is `none` one step later. -/
theorem traceFrom_none {f : σ → Option σ} {c₀ : σ} {k : ℕ}
    (h : traceFrom f c₀ k = none) : traceFrom f c₀ (k + 1) = none := by
  rw [traceFrom_succ, h]; rfl

/-- Once the trace is `none` it stays `none` for all later times. -/
theorem traceFrom_none_of_le {f : σ → Option σ} {c₀ : σ} {k : ℕ}
    (h : traceFrom f c₀ k = none) : ∀ j ≥ k, traceFrom f c₀ j = none := by
  intro j hj
  induction j with
  | zero => rw [Nat.le_zero.mp hj] at h; exact h
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with _ | hge
    · exact traceFrom_none (ih (by omega))
    · rw [Nat.le_antisymm hge hj]; exact h

/-- Halting is permanent: if the trace is `some c` with `f c = none`, the next step is `none`. -/
theorem traceFrom_halt {f : σ → Option σ} {c₀ : σ} {k : ℕ} {c : σ}
    (hk : traceFrom f c₀ k = some c) (hc : f c = none) : traceFrom f c₀ (k + 1) = none := by
  rw [traceFrom_succ, hk]; exact hc

end Trace

section EvalsToBridge

variable {σ : Type*} {f : σ → Option σ} {c₀ : σ} {b : Option σ}

/-- An `EvalsTo` proof yields the trace value at its step count. -/
theorem _root_.StateTransition.EvalsTo.traceFrom (h : EvalsTo f c₀ b) :
    DeepWiki.traceFrom f c₀ h.steps = b :=
  h.evals_in_steps

/-- A trace hitting `b` at time `k` is an `EvalsTo` proof. -/
def traceFrom.evalsTo {k : ℕ} (h : DeepWiki.traceFrom f c₀ k = b) : EvalsTo f c₀ b :=
  ⟨k, h⟩

/-- `EvalsTo f c₀ b` is inhabited iff some time `k` has trace value `b`. -/
theorem evalsTo_iff_exists_trace :
    Nonempty (EvalsTo f c₀ b) ↔ ∃ k, traceFrom f c₀ k = b :=
  ⟨fun ⟨h⟩ => ⟨h.steps, h.evals_in_steps⟩, fun ⟨k, h⟩ => ⟨⟨k, h⟩⟩⟩

/-- `EvalsToInTime f c₀ b m` is inhabited iff `b` appears in the trace at some time `k ≤ m`. -/
theorem evalsToInTime_iff {m : ℕ} :
    Nonempty (EvalsToInTime f c₀ b m) ↔ ∃ k ≤ m, traceFrom f c₀ k = b :=
  ⟨fun ⟨h⟩ => ⟨h.steps, h.steps_le_m, h.evals_in_steps⟩,
   fun ⟨k, hk, h⟩ => ⟨⟨⟨k, h⟩, hk⟩⟩⟩

end EvalsToBridge

section TM2

variable {tm : FinTM2}

/-- `tm2Trace tm l k`: the configuration `tm` is in at time `k` started on input `l`. -/
def tm2Trace (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (k : ℕ) : Option tm.Cfg :=
  traceFrom tm.step (initList tm l) k

/-- The TM2 trace at time `0` is the initial configuration on input `l`. -/
@[simp]
theorem tm2Trace_zero (l : List (tm.Γ tm.k₀)) :
    tm2Trace tm l 0 = some (initList tm l) :=
  rfl

/-- `TM2OutputsInTime tm l l' m` is inhabited iff the trace reaches the halt config of `l'`
at some time `k ≤ m`. -/
theorem tm2OutputsInTime_iff_trace {l : List (tm.Γ tm.k₀)} {l' : Option (List (tm.Γ tm.k₁))}
    {m : ℕ} :
    Nonempty (TM2OutputsInTime tm l l' m) ↔
      ∃ k ≤ m, tm2Trace tm l k = Option.map (haltList tm) l' :=
  evalsToInTime_iff

/-- `AcceptsWithin tm l l' m`: the trace from input `l` reaches output `l'`'s halt config
within `m` steps. -/
def AcceptsWithin (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁)))
    (m : ℕ) : Prop :=
  ∃ k ≤ m, tm2Trace tm l k = Option.map (haltList tm) l'

/-- `AcceptsWithin` is exactly the inhabitedness of `TM2OutputsInTime`. -/
theorem acceptsWithin_iff {l : List (tm.Γ tm.k₀)} {l' : Option (List (tm.Γ tm.k₁))} {m : ℕ} :
    AcceptsWithin tm l l' m ↔ Nonempty (TM2OutputsInTime tm l l' m) :=
  tm2OutputsInTime_iff_trace.symm

end TM2

section Restatements

-- Each new theorem restated against its expected type ("it compiled" ≠ "it says the right thing").

variable {σ : Type*}

example (f : σ → Option σ) (c₀ : σ) : traceFrom f c₀ 0 = some c₀ := traceFrom_zero f c₀

example (f : σ → Option σ) (c₀ : σ) (k : ℕ) :
    traceFrom f c₀ (k + 1) = (traceFrom f c₀ k).bind f := traceFrom_succ f c₀ k

example {f : σ → Option σ} {c₀ : σ} {k : ℕ} (h : traceFrom f c₀ k = none) :
    traceFrom f c₀ (k + 1) = none := traceFrom_none h

example {f : σ → Option σ} {c₀ : σ} {k : ℕ} (h : traceFrom f c₀ k = none) :
    ∀ j ≥ k, traceFrom f c₀ j = none := traceFrom_none_of_le h

example {f : σ → Option σ} {c₀ : σ} {k : ℕ} {c : σ}
    (hk : traceFrom f c₀ k = some c) (hc : f c = none) :
    traceFrom f c₀ (k + 1) = none := traceFrom_halt hk hc

example {f : σ → Option σ} {c₀ : σ} {b : Option σ} (h : EvalsTo f c₀ b) :
    traceFrom f c₀ h.steps = b := h.traceFrom

example {f : σ → Option σ} {c₀ : σ} {b : Option σ} :
    Nonempty (EvalsTo f c₀ b) ↔ ∃ k, traceFrom f c₀ k = b := evalsTo_iff_exists_trace

example {f : σ → Option σ} {c₀ : σ} {b : Option σ} {m : ℕ} :
    Nonempty (EvalsToInTime f c₀ b m) ↔ ∃ k ≤ m, traceFrom f c₀ k = b := evalsToInTime_iff

example (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (k : ℕ) :
    tm2Trace tm l k = traceFrom tm.step (initList tm l) k := rfl

example {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {l' : Option (List (tm.Γ tm.k₁))} {m : ℕ} :
    Nonempty (TM2OutputsInTime tm l l' m) ↔
      ∃ k ≤ m, tm2Trace tm l k = Option.map (haltList tm) l' := tm2OutputsInTime_iff_trace

example {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {l' : Option (List (tm.Γ tm.k₁))} {m : ℕ} :
    AcceptsWithin tm l l' m ↔ Nonempty (TM2OutputsInTime tm l l' m) := acceptsWithin_iff

end Restatements

end DeepWiki
